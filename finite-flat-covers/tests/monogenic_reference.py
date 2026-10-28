"""Independent quotient-ring isomorphisms, NOT a Magma runtime test.
Every model-basis product is checked in R[t]/f, even for nilpotent f.
The coefficient-of-t^(n-1) pairing is used, not an invertible trace pairing.
The change of basis must be unimodular over the ORIGINAL coefficient ring.
"""
from __future__ import annotations
import json
from pathlib import Path
from random import Random
import sympy as sp
from reference_checks import blank,put,quartic,quintic,quintic_model,matrices
from action_reference import cubic
from resolution_reference import pmat,kernel,fr,monomial,betti,export_magma
from geometry_reference import expr


def anchors(n):
    return {3:[2,1],4:[2,1,1],5:[2,1,4,3]}.get(n,list(range(2,n))+[1])


def ring_model(a):
    n=len(a)-1
    if n==2:
        T=blank(2);put(T,1,1,0,-a[2]*a[0]);put(T,1,1,1,-a[1]);return T
    if n==3:return cubic(list(reversed(a)))
    if n==4:return quartic([[1,0,0],[0,0,-1],[0,-1,0]],[[0,a[3],a[1]],[a[3],a[4],a[2]],[a[1],a[2],a[0]]])
    if n==5:return quintic(quintic_model(a))
    raise ValueError(n)


def canonical_binary(a):
    n=len(a)-1;m=n-2;r=n-1
    pairs=[(i,j) for i in range(r) for j in range(i,r)]
    piv=[next(b for b,ij in enumerate(pairs) if sum(ij)==k) for k in range(2*m+1)]
    mm=[monomial(r,i,j) for i,j in pairs];Q=[]
    for b,ij in enumerate(pairs):
        if b not in piv:Q.append({mm[b]:sp.Integer(1),mm[piv[sum(ij)]]:sp.Integer(-1)})
    for k in range(n-3):Q.append({mm[piv[i+k]]:sp.sympify(v) for i,v in enumerate(a) if v})
    assert len(Q)==n*(n-3)//2
    return Q


def quotient_comparison(T,f,t,v,p=0):
    n=int(sp.degree(f,t));r=n-1
    assert sp.Poly(f,t).LC()==1
    kw={'modulus':p} if p else {}
    rem=lambda q:sp.Poly(sp.rem(sp.expand(q),f,t,**kw),t,**kw)
    red=lambda c:sp.Integer(c)%p if p else sp.expand(c)
    if n==2:B=sp.eye(n)
    else:
        H=sp.Matrix(r,r,lambda i,j:rem(t**(i+1)*v[j]).nth(n-1))
        assert int(H.det())%p!=0 if p else H.det() in [1,-1]
        B=sp.diag(1,H.inv_mod(p) if p else H.inv())
        images=[sum(B[i,k]*t**k for k in range(n)) for i in range(n)]
        Bi=B.inv_mod(p) if p else B.inv();shifts=[0]
        for i,j in enumerate(anchors(n),1):
            row=sp.Matrix(1,n,[rem(images[i]*images[j]).nth(k) for k in range(n)])*Bi
            shifts.append(red(row[j]))
        for i in range(1,n):B[i,0]-=shifts[i]
        images=[sum(B[i,k]*t**k for k in range(n)) for i in range(n)]
        Bi=B.inv_mod(p) if p else B.inv();u=None
        for i in range(1,n):
            for j in range(i,n):
                row=sp.Matrix(1,n,[rem(images[i]*images[j]).nth(k) for k in range(n)])*Bi
                for k in range(1,n):
                    c=red(row[k])
                    if (p and c) or (not p and c in [1,-1]):
                        u=red(T[i][j][k]*(pow(int(c),-1,p) if p else 1/c));break
                if u is not None:break
            if u is not None:break
        assert u is not None,'No unit product coefficient fixes the orientation'
        assert u!=0 if p else u in [1,-1],('nonunit resolution orientation',u)
        for i in range(1,n):
            for k in range(n):B[i,k]=red(u*B[i,k])
    images=[sum(B[i,k]*t**k for k in range(n)) for i in range(n)]
    det=red(B.det());assert det!=0 if p else det in [1,-1]
    for i in range(n):
        for j in range(n):
            q=images[i]*images[j]-sum(T[i][j][k]*images[k] for k in range(n))
            assert rem(q).is_zero,('product mismatch',n,p,i,j,rem(q))
    zmat=sp.Matrix(n,n,lambda i,j:rem(t**(j+1)).nth(i))
    for i,L in enumerate(matrices(T)):
        op=sum((B[i,k]*zmat**k for k in range(n)),sp.zeros(n))
        assert all(red(c)==0 for c in op*B.T-B.T*L),('matrix intertwiner',n,p,i)
    return B


def geometric_coordinates(n,t):
    if n<=3:return [t,sp.Integer(1)]
    if n==4:return [t,t*t,sp.Integer(1)]
    return [t**i for i in range(n-1)]


def check_model_equations(a,t,p=0):
    n=len(a)-1;f=sum(c*t**i for i,c in enumerate(a));v=geometric_coordinates(n,t)
    if n<=3:eqs=[f]
    elif n==4:eqs=[v[0]**2-v[1]*v[2],a[0]*v[2]**2+a[1]*v[0]*v[2]+a[2]*v[1]*v[2]+a[3]*v[0]*v[1]+a[4]*v[1]**2]
    elif n==5:
        from reference_checks import pf
        M=sum((v[i]*sp.Matrix(A) for i,A in enumerate(quintic_model(a))),sp.zeros(5));eqs=pf(M.tolist())
    else:eqs=[expr(q,v) for q in canonical_binary(a)]
    kw={'modulus':p} if p else {}
    for q in eqs:assert sp.Poly(sp.rem(sp.expand(q),f,t,**kw),t,**kw).is_zero


def binary_ring_constants(a):
    n=len(a)-1;b=list(reversed(a));T=blank(n)
    for i in range(1,n):
        for j in range(i,n):
            row=[sp.Integer(0)]*n
            for k in range(max(1,i+j-n),i+1):row[k]-=b[i+j-k]
            for k in range(j+1,min(i+j,n)+1):
                if k==n:row[0]-=b[i+j-k]*b[n]
                else:row[k]+=b[i+j-k]
            for k in range(n):put(T,i,j,k,row[k])
    return T


def run_low():
    t=sp.Symbol('t');rng=Random(20261003);out={};count=0;products=0;mods=0
    for n in range(2,6):
        aa=[[rng.randrange(-4,5) for _ in range(n)]+[1] for _ in range(5)]
        aa += [[0]*n+[1],list(reversed(sp.Poly((t-1)**n,t).all_coeffs()))]
        for a in aa:
            f=sum(c*t**i for i,c in enumerate(a));T=ring_model(a)
            quotient_comparison(T,f,t,geometric_coordinates(n,t));check_model_equations(a,t)
            count+=1;products+=n*n
            for p in [2,3,5,7]:
                aa=[int(c)%p for c in a];fp=sum(c*t**i for i,c in enumerate(aa))
                quotient_comparison(ring_model(aa),fp,t,geometric_coordinates(n,t),p)
                check_model_equations(aa,t,p);mods+=1;products+=n*n
    out.update(integer_monic_models=count,small_characteristic_models=mods,checked_basis_products=products)
    u=sp.Symbol('u');families=0
    for n in range(2,6):
        f=t**n+u*t**(n-1)+(u*u+1)*t+(u+2);a=[sp.Poly(f,t).nth(i) for i in range(n+1)]
        quotient_comparison(ring_model(a),f,t,geometric_coordinates(n,t));check_model_equations(a,t);families+=1
    out['Z_u_families']=families
    n=6;a=sp.symbols('a0:7');f=sum(a[i]*t**i for i in range(n+1));b=list(reversed(a))
    zz=[sp.Integer(1)]+[sum(b[j]*t**(i-j) for j in range(i)) for i in range(1,n)];T=binary_ring_constants(a)
    for i in range(n):
        for j in range(n):assert sp.rem(sp.expand(zz[i]*zz[j]-sum(T[i][j][k]*zz[k] for k in range(n))),f,t)==0
    out['universal_nonmonic_sextic_products']=n*n
    return out


def run_high():
    t=sp.Symbol('t');out={};fixture=Path(__file__).parent/'fixtures'
    for n in [6,7]:
        for label,f in [('mixed',t**n+2*t**(n-2)-3*t*t+t+1),('nilpotent',t**n)]:
            print('Explicit monogenic isomorphism:',n,label,flush=True)
            a=[sp.Poly(f,t).nth(i) for i in range(n+1)];Q=canonical_binary(a);F=[pmat([Q])]
            for pos in range(1,n-2):F.append(kernel(F[-1],n-1,2 if pos==n-3 else 1))
            assert [1]+[A['nc'] for A in F]==betti(n)
            T=fr(F);B=quotient_comparison(T,f,t,geometric_coordinates(n,t));check_model_equations(a,t)
            for p in [2,3,5,7]:
                Fp=[{'nr':A['nr'],'nc':A['nc'],'data':{ij:{e:int(c)%p for e,c in q.items() if int(c)%p} for ij,q in A['data'].items()}} for A in F]
                fp=sum((int(c)%p)*t**i for i,c in enumerate(a))
                quotient_comparison(fr(Fp),fp,t,geometric_coordinates(n,t),p)
            file=fixture/f'monogenic_{n}_{label}.m';export_magma(F,n,file)
            text=file.read_text().replace(f'StandardResolution{n}',f'MonogenicResolution{n}_{label}').replace('axes plus (1:...:1).',f'{f}.');file.write_text(text)
            (fixture/f'monogenic_{n}_{label}_basis.json').write_text(json.dumps([[str(c) for c in row] for row in B.tolist()],indent=2))
            out[f'{n}_{label}']={'polynomial':str(f),'basis_determinant':str(B.det()),'all_products':n*n,'primes':[2,3,5,7]}
    return out

if __name__=='__main__':
    import sys
    result=run_high() if '--high' in sys.argv else run_low()
    name='monogenic-high-results.json' if '--high' in sys.argv else 'monogenic-low-results.json'
    (Path(__file__).parent/name).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
