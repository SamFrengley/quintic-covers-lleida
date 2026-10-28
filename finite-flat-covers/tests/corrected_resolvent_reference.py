"""Exact independent checks of the trace-halving sextic correction.
No Magma is executed. Bases are rows, starting with the identity.
"""
from __future__ import annotations
import json
from itertools import product, combinations, permutations
from pathlib import Path
from random import Random
import sympy as s
from sympy.matrices.normalforms import hermite_normal_form
from resolvent_reference import sextic, split_model, table_mod, sextic_transport
from reference_checks import quintic, quintic_model, disc, associative, alt
from resolution_reference import basis_transform
from action_reference import quintic_action
HERE=Path(__file__).resolve().parent

def flat(T): return [v for plane in T for row in plane for v in row]
def trace(T): return [sum(T[i][j][j] for j in range(len(T))) for i in range(len(T))]
def poly2(x,t=None):
    x=s.cancel(x)
    if t is None:
        x=s.Rational(x); assert int(x.q)%2
        return s.Integer(int(x.p)%2)
    p=s.Poly(x,t,domain=s.QQ)
    return s.Poly.from_dict({m:int(c.p)%2 for m,c in p.terms() if int(c.p)%2},t,modulus=2).as_expr() \
        if all(int(c.q)%2 for c in p.all_coeffs()) else (_ for _ in ()).throw(AssertionError('even denominator'))
def mul(T,u,v):
    n=len(T)
    return s.Matrix(1,n,[s.expand(sum(u[i]*v[j]*T[i][j][k] for i in range(n) for j in range(n) if u[i] and v[j])) for k in range(n)])
def integral(T,t=None):
    if t is None:return all(s.sympify(v).is_Integer for v in flat(T))
    for v in flat(T):
        try:s.Poly(v,t,domain=s.ZZ)
        except (s.polys.polyerrors.CoercionFailed,s.polys.polyerrors.PolynomialError):return False
    return True

def correct(T,t=None):
    """Z: trace-halving algebra. Z[t]: its reflexive, free envelope.
    Checks all output coefficients instead of presuming integrality.
    """
    tr=[s.sympify(v) for v in trace(T)]; n=6
    assert integral([[[v/2 for v in tr]]],t)
    E=s.diag(1,*([s.Rational(1,2)]*5))
    for i in range(1,6):E[i,0]=-tr[i]/4
    U=basis_transform(T,E)
    defects=[[poly2(2*U[i][j][k],t) for k in range(6)] for i in range(1,6) for j in range(i,6)]
    rows=[r for r in defects if any(r)]
    if not rows:
        assert integral(U,t)
        return U,E,{'index':32,'factor':4,'primitive_defect':None}
    r=rows[0]
    assert any(r[1:])
    if t is not None:
        g=s.Poly(0,t,modulus=2)
        for a in r[1:]:g=s.gcd(g,s.Poly(a,t,modulus=2))
        quot=[s.div(s.Poly(a,t,modulus=2),g) for a in r]
        assert all(rem.is_zero for _,rem in quot)
        r=[q.as_expr() for q,_ in quot]
    # The defect space must have rank one, including its scalar coordinate.
    j=next(j for j in range(1,6) if r[j])
    for a in rows:
        for k in range(6):assert poly2(a[k]*r[j]-a[j]*r[k],t)==0
    # Complete the quotient vector by a WORD of elementary operations.
    # Merely lifting a mod-2 unimodular matrix can introduce an odd polynomial determinant.
    col=s.eye(5);u=r[1:]
    if j!=1:
        col.col_swap(0,j-1);u[0],u[j-1]=u[j-1],u[0]
    for j in range(1,5):
        while u[j]!=0:
            if t is None:q=s.Integer(int(u[0]));rem=s.Integer(0)
            else:
                q,rem=s.div(s.Poly(u[0],t,modulus=2),s.Poly(u[j],t,modulus=2))
                q,rem=q.as_expr(),rem.as_expr()
            col[:,0]=col[:,0]-q*col[:,j]
            u[0]=rem
            col.col_swap(0,j);u[0],u[j]=u[j],u[0]
    assert u==[1,0,0,0,0]
    assert col.det() in [-1,1]
    G=s.diag(s.ones(1),col.inv());H=s.eye(6)
    H[1,1]=s.Rational(1,2);H[1,0]=r[0]/2
    B=H*G*E
    V=basis_transform(T,B)
    assert integral(V,t), (r,[(i,v) for i,v in enumerate(flat(V)) if not s.sympify(v).is_Integer][:3])
    assert s.cancel(B.det()**2)==s.Rational(1,4096)
    assert all(s.Poly(x,t,domain=s.ZZ) is not None for x in B.inv()) if t is not None else all(x.is_Integer for x in B.inv())
    return V,B,{'index':64,'factor':1,'primitive_defect':[str(x) for x in r]}

def row_hnf(rows):
    A=s.Matrix.vstack(*rows);den=s.ilcm(*[v.q for v in A]);Z=(den*A).applyfunc(int)
    return hermite_normal_form(Z.T).T/den

def slow_envelope(T):
    """Independent integer closure by HNF, rather than rank-one defects."""
    e=s.eye(6);tr=trace(T)
    B=row_hnf([e[0,:]]+[(e[i,:]-s.Rational(tr[i],2)*e[0,:])/2 for i in range(1,6)])
    for count in range(8):
        V=row_hnf([B[i,:] for i in range(6)]+[mul(T,B[i,:],B[j,:]) for i in range(6) for j in range(i,6)])
        assert all((4*x).is_Integer for x in V)
        if V==B:return B
        B=V
    raise AssertionError('Closure did not stabilize')

def frob_matrix(T,p):
    n=len(T);e=s.eye(n)
    return s.Matrix([list(mul(T,e[i,:],e[i,:])) for i in range(n)]).applyfunc(lambda v:int(v)%p)

def rank_mod(A,p):
    a=[[int(x)%p for x in row] for row in A.tolist()]; nr=len(a);nc=len(a[0]);r=0
    for j in range(nc):
        piv=next((i for i in range(r,nr) if a[i][j]),None)
        if piv is None:continue
        a[r],a[piv]=a[piv],a[r];c=pow(a[r][j],-1,p);a[r]=[c*x%p for x in a[r]]
        for i in range(nr):
            if i!=r:
                c=a[i][j];a[i]=[(x-c*y)%p for x,y in zip(a[i],a[r])]
        r+=1
    return r

def exceptional_cycles(factor_degrees):
    # The six cyclic order-five subgroups of S5, with conjugation action.
    def compose(a,b):return tuple(a[b[i]] for i in range(5))
    def power(a,k):
        b=tuple(range(5))
        for _ in range(k):b=compose(a,b)
        return b
    def inverse(a):return tuple(a.index(i) for i in range(5))
    subgroups=[]
    for tail in permutations(range(1,5)):
        seq=(0,)+tail;a=list(range(5))
        for i in range(5):a[seq[i]]=seq[(i+1)%5]
        H=frozenset(power(tuple(a),k) for k in range(5))
        if H not in subgroups:subgroups.append(H)
    assert len(subgroups)==6
    p=list(range(5));off=0
    for d in factor_degrees:
        for i in range(d):p[off+i]=off+(i+1)%d
        off+=d
    p=tuple(p);pi=inverse(p)
    act=[subgroups.index(frozenset(compose(compose(p,a),pi) for a in H)) for H in subgroups]
    unseen=set(range(6));out=[]
    while unseen:
        i=min(unseen);n=0
        while i in unseen:unseen.remove(i);n+=1;i=act[i]
        out.append(n)
    return sorted(out)

def etale_f2_check(T,cycles):
    F=frob_matrix(T,2);I=s.eye(6)
    assert rank_mod(F,2)==6
    for k in range(1,7):
        expected=sum(s.gcd(d,k) for d in cycles)
        assert 6-rank_mod(F**k-I,2)==expected,(cycles,k)

def corrected_rational_function_fibre(T,variables):
    """Independent mixed-characteristic lift/reduction backend over F2(variables)."""
    K=s.GF(2).frac_field(*variables)
    def v2(q):
        q=s.Rational(q); a=abs(int(q.p));b=int(q.q);r=0
        assert a
        while a%2==0:a//=2;r+=1
        while b%2==0:b//=2;r-=1
        return r
    def reduce(x):
        x=s.cancel(x)
        if x==0:return K.zero
        a,b=s.fraction(x);a=s.Poly(a,*variables,domain=s.QQ);b=s.Poly(b,*variables,domain=s.QQ)
        m=min(v2(c) for c in b.coeffs() if c)
        scale=s.Rational(2)**(-m)
        def rp(f):
            out=0
            for ex,c in f.terms():
                c=s.Rational(scale*c);assert int(c.q)%2==1,(x,c)
                out+=(int(c.p)%2)*s.prod(v**e for v,e in zip(variables,ex))
            return K.from_sympy(out)
        aa,bb=rp(a),rp(b);assert bb
        return aa/bb
    E=s.diag(1,*([s.Rational(1,2)]*5))
    for i in range(1,6):E[i,0]=-s.sympify(trace(T)[i])/4
    U=basis_transform(T,E)
    rows=[[reduce(2*U[i][j][k]) for k in range(6)] for i in range(1,6) for j in range(i,6)]
    r=next(a for a in rows if any(a));p=next(j for j in range(1,6) if r[j]);r=[a/r[p] for a in r]
    H=s.eye(6)
    for j in range(6):H[p,j]=K.to_sympy(r[j])/2
    B=H*E;V=basis_transform(T,B);W=[[[reduce(v) for v in row] for row in plane] for plane in V]
    assert associative(W)[0]
    tr=trace(W);pair=[[sum(W[i][j][k]*tr[k] for k in range(6)) for j in range(6)] for i in range(6)]
    rank=0
    for j in range(6):
        p=next((i for i in range(rank,6) if pair[i][j]),None)
        if p is None:continue
        pair[rank],pair[p]=pair[p],pair[rank];c=pair[rank][j];pair[rank]=[a/c for a in pair[rank]]
        for i in range(6):
            if i!=rank:
                c=pair[i][j];pair[i]=[a-c*b for a,b in zip(pair[i],pair[rank])]
        rank+=1
    assert rank==6
    assert s.cancel(B.det()**2)==s.Rational(1,4096)
    inclusion=[[reduce(a) for a in row] for row in B.inv().tolist()]
    raw=[[[reduce(v) for v in row] for row in plane] for plane in T]
    for i,j,k in product(range(6),repeat=3):
        assert sum(inclusion[i][a]*inclusion[j][b]*W[a][b][k] for a in range(6) for b in range(6)) == sum(raw[i][j][a]*inclusion[a][k] for a in range(6))
    return {'variables':[str(x) for x in variables],'trace_pairing_rank':rank,
            'associativity':True,'specialized_inclusion_multiplicative':True,
            'fractional_basis_pivot':[str(K.to_sympy(a)) for a in r]}

def run():
    rng=Random(617)
    inputs=[split_model(),quintic_model([-1,-1,0,0,0,1]),quintic_model([0,0,0,0,0,1]),[alt([0]*10) for _ in range(4)]]
    inputs += [[alt([rng.randrange(-2,3) for _ in range(10)]) for _ in range(4)] for _ in range(20)]
    cases=[]
    for A in inputs:
        T=sextic(A);V,B,info=correct(T);W=slow_envelope(T)
        assert (B*W.inv()).det() in [-1,1] and all(x.is_Integer for x in B*W.inv())
        assert associative(V)[0]
        dq=disc(quintic(A));assert disc(V)==info['factor']*dq**3
        assert (dq%2==0) or info['index']==64
        for p in (2,3,5,7):assert associative(table_mod(V,p),p)[0]
        cases.append({'source_discriminant':str(dq),**info})
    # Split order identified as Z^6, every product, not merely equal discriminants.
    oldimages=s.Matrix(json.loads((HERE/'fixtures/split_sextic_lattice.json').read_text())['basis_images_in_Z6'])
    V,B,_=correct(sextic(split_model()));images=B*oldimages
    assert abs(images.det())==1 and all(x.is_Integer for x in images)
    for i in range(6):
        for j in range(6):
            assert s.Matrix(1,6,V[i][j])*images == s.Matrix(1,6,[images[i,k]*images[j,k] for k in range(6)])
    etale_f2_check(table_mod(V,2),[1]*6)
    # Every squarefree monic quintic over F2: expected exceptional Frobenius action.
    z=s.Symbol('z');ff=[]
    for cs in product(range(2),repeat=5):
        f=s.Poly(z**5+sum(cs[i]*z**i for i in range(5)),z,modulus=2)
        if s.gcd(f,f.diff()).degree()!=0:continue
        A=quintic_model(list(cs)+[1]);V,_,info=correct(sextic(A))
        degs=sorted(g.degree() for g,e in s.factor_list(f)[1] for _ in range(e))
        cyc=exceptional_cycles(degs);etale_f2_check(table_mod(V,2),cyc)
        ff.append({'coefficients':list(cs)+[1],'quintic_factors':degs,'sextic_factors':cyc})
        # Independent lifts: add 2 to selected coefficients and compare isomorphism type via Frobenius.
        cs2=[c+2*(i%2+1) for i,c in enumerate(cs)]
        VV,_,_=correct(sextic(quintic_model(cs2+[1])))
        etale_f2_check(table_mod(VV,2),cyc)
    # Polynomial bases: saturation at codimension two, with no inversion of t.
    t=s.Symbol('t');families=[[ -t,-1,0,0,0,1],[1+t,t,t+1,t**2,t,1]];polyout=[]
    for cs in families:
        T=sextic(quintic_model(cs));V,B,info=correct(T,t)
        assert integral(V,t)
        # All associativity identities polynomial, not sampled.
        for i,j,k,l in product(range(6),repeat=4):
            assert s.expand(sum(V[i][j][r]*V[r][k][l]-V[j][k][r]*V[i][r][l] for r in range(6)))==0
        # Discriminant equality is structural from det(B), then tested independently.
        dq=s.Poly(sum(cs[i]*z**i for i in range(6)),z).discriminant()
        assert s.expand(disc(V)-info['factor']*dq**3)==0
        for a in [0,1,2,-1]:
            V0=[[[s.expand(v).subs(t,a) for v in row] for row in plane] for plane in V]
            assert associative(V0)[0]
        polyout.append({'coefficients':[str(c) for c in cs],**info,'integral_basis':[[str(v) for v in row] for row in B.tolist()]})
    # Invariant under integral frame changes: compare actual lattices after the known old-ring isomorphism.
    acted=0
    for A in inputs[:2]:
        T=sextic(A);V,B,_=correct(T)
        for _ in range(5):
            g=s.eye(5);h=s.eye(4)
            for M in (g,h):
                for __ in range(3):
                    i,j=rng.sample(range(M.rows),2);M[i,:]=M[i,:]+rng.choice([-1,1])*M[j,:]
            AA=quintic_action(A,g,h);TT=sextic(AA)
            transported,J=sextic_transport(T,g.inv().T)
            assert transported==TT
            VV,BB,_=correct(TT)
            change=BB*J*B.inv()
            assert abs(change.det())==1 and all(x.is_Integer for x in change)
            assert basis_transform(V,change)==VV
            acted+=1
    u,v=s.symbols('u v');function_fibres=[]
    for variables,c in [((u,),u),((u,v),u+v)]:
        T=sextic(quintic_model([1,1,0,c,0,1]))
        function_fibres.append(corrected_rational_function_fibre(T,variables))
    return {'rational_function_characteristic_2_fibres':function_fibres,'integer_models':len(cases),'integer_closure_agrees_with_independent_HNF':True,
            'integer_cases':cases,'split_corrected_ring':'Z^6, explicit unimodular evaluation basis',
            'characteristic_2_squarefree_monic_quintics':len(ff),'characteristic_2_frobenius_tests':ff,
            'alternative_lifts_compared':len(ff),'polynomial_families':polyout,
            'integral_action_lattice_comparisons':acted,
            'native_magma_executed':False,'scope':'Z and Z[t] reference implementation; characteristic-2 residue algebras from integral lifts'}
if __name__=='__main__':
    r=run();(HERE/'corrected-resolvent-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
