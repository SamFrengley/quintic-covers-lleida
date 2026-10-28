"""Exact checks for monogenic canonical models and local syzygy elimination.
This exercises the equations and certificates, not Magma scheme constructors.
"""
from pathlib import Path
import json
import sympy as sp
from reference_checks import associative,disc
from resolution_reference import mons,monomial,pmat,kernel,fr,standard,read_fixture,betti


def canonical(f,t):
    n=sp.degree(f,t); r=n-1
    pairs=[(i,j) for i in range(r) for j in range(i,r)]
    pivots=[next(a for a,p in enumerate(pairs) if sum(p)==k) for k in range(n)]
    mm=[monomial(r,i,j) for i,j in pairs]; Q=[]
    for a,p in enumerate(pairs):
        if a in pivots: continue
        q={mm[a]:sp.Integer(1)}; rem=sp.Poly(sp.rem(t**sum(p),f,t),t)
        for k in range(n):
            c=rem.nth(k)
            if c: q[mm[pivots[k]]]=q.get(mm[pivots[k]],0)-c
        Q.append({e:v for e,v in q.items() if v})
    return Q


def expr(f,x):
    return sum(c*sp.prod(v**p for v,p in zip(x,e)) for e,c in f.items())


def local_reduce(F,chart):
    r=len(F)+1; x=sp.symbols(f'x0:{r-1}'); images=list(x); images.insert(chart,sp.Integer(1))
    Q=[expr(F[0]['data'].get((0,j),{}),images) for j in range(F[0]['nc'])]
    A=F[1]; S=sp.Matrix(A['nr'],A['nc'],lambda i,j:expr(A['data'].get((i,j),{}),images))
    original=sp.Matrix(Q); U=sp.eye(len(Q))
    while True:
        # Units of Z[x] are +/-1; this tests the stricter arithmetic version.
        pivots=[(i,j) for i in range(S.rows) for j in range(S.cols) if S[i,j] in [-1,1]]
        if not pivots: break
        a,b=pivots[0]; keep=[i for i in range(len(Q)) if i!=a]; cols=[j for j in range(S.cols) if j!=b]
        E=sp.zeros(len(Q),len(keep))
        for k,i in enumerate(keep): E[i,k]=1; E[a,k]=-S[i,b]/S[a,b]
        U=U*E; S=(E.T*S).extract(range(len(keep)),cols).applyfunc(sp.expand); Q=[Q[i] for i in keep]
    assert (original-U*sp.Matrix(Q)).applyfunc(sp.expand)==sp.zeros(len(original),1)
    return len(Q)


def run():
    out={}; t=sp.Symbol('t')
    for n in [6,7]:
        local=[local_reduce(read_fixture(n),j) for j in range(n-1)]
        out[f'degree_{n}_local_generators']=local
        assert all(n-2 <= k < n*(n-3)//2 for k in local),local
        for f in [t**n-t-1,t**n]:
            print('monic model',f,flush=True)
            Q=canonical(f,t); F=[pmat([Q])]
            for a in range(1,n-2): F.append(kernel(F[-1],n-1,2 if a==n-3 else 1))
            assert [1]+[A['nc'] for A in F]==betti(n)
            C=fr(F); assert associative(C)[0]
            df=sp.discriminant(f,t); dc=disc(C)
            assert dc==df,(n,f,dc,df)
            for p in [2,3,5,7]: assert associative(C,p)[0]
            # x0=1 gives precisely the monogenic algebra, including t^n.
            x=sp.symbols(f'x0:{n-2}'); equations=[expr(q,[1,*x]) for q in Q]
            # In these coordinates x[0] is t, x[i] is t^(i+1).
            G=sp.groebner(equations,*reversed(x)); H=sp.groebner([f.subs(t,x[0])]+[x[i]-x[0]**(i+1) for i in range(1,n-2)],*reversed(x))
            assert G==H
            # No projective point at infinity: every chart at x0=0 is empty.
            for j in range(1,n-1):
                xx=sp.symbols(f'y0:{n-1}'); eq=[expr(q,xx) for q in Q]+[xx[0],xx[j]-1]
                GG=sp.groebner(eq,*xx); assert list(GG)==[sp.Integer(1)]
            out[str(f)]={'discriminant':str(dc),'associative':True,'affine_ring_and_no_infinity':True,'primes_checked':[2,3,5,7]}
    return out

if __name__=='__main__':
    result=run(); (Path(__file__).parent/'geometry-reference-results.json').write_text(json.dumps(result,indent=2)); print(json.dumps(result,indent=2))
