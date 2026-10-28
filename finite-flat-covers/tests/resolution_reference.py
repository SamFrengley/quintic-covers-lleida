"""Independent exact arithmetic for the Fisher--Radicevic formulas (not Magma).
Sparse homogeneous coefficient kernels generate reference resolutions. Integral
brackets then recover the rank-n multiplication tables, without division by 2n.
"""
from __future__ import annotations
from itertools import combinations_with_replacement
from functools import lru_cache, reduce
from pathlib import Path
from math import gcd
import json, time
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from reference_checks import blank, put, constants0, sign, associative, disc


def monomial(r, *indices):
    a=[0]*r
    for i in indices: a[i]+=1
    return tuple(a)


def mons(r,d):
    return [monomial(r,*a) for a in combinations_with_replacement(range(r),d)]


def add(f,g,c=1):
    z=f.copy()
    for e,v in g.items():
        z[e]=z.get(e,0)+c*v
        if z[e]==0: del z[e]
    return z


def mul(f,g):
    z={}
    for a,u in f.items():
        for b,v in g.items():
            e=tuple(x+y for x,y in zip(a,b)); z[e]=z.get(e,0)+u*v
    return {e:v for e,v in z.items() if v}


def pmat(rows):
    return {'nr':len(rows),'nc':len(rows[0]),'data':{(i,j):f for i,row in enumerate(rows) for j,f in enumerate(row) if f}}


def kernel(A,r,e):
    t=time.monotonic(); degree=max(sum(m) for f in A['data'].values() for m in f)
    inputs=mons(r,e); outputs=mons(r,e+degree); outindex={m:i for i,m in enumerate(outputs)}
    entries={}
    for (i,j),f in A['data'].items():
        for b,m in enumerate(inputs):
            col=j*len(inputs)+b
            for a,c in f.items():
                mm=tuple(x+y for x,y in zip(m,a)); row=i*len(outputs)+outindex[mm]
                entries.setdefault(row,{})[col]=c
    nr=A['nr']*len(outputs); nc=A['nc']*len(inputs)
    D=DomainMatrix.from_dict_sympy(nr,nc,entries).convert_to(sp.QQ)
    K=D.nullspace(divide_last=True).to_Matrix(); rows=[]
    for rr in K.tolist():
        den=sp.ilcm(*[v.q for v in rr]); rr=[int(v*den) for v in rr]
        content=reduce(gcd,rr); rows.append([v//content for v in rr])
    out={}
    for a,row in enumerate(rows):
        for j in range(A['nc']):
            f={m:row[j*len(inputs)+b] for b,m in enumerate(inputs) if row[j*len(inputs)+b]}
            if f: out[j,a]=f
    B={'nr':A['nc'],'nc':len(rows),'data':out}
    assert compositions_zero(A,B)
    print(f'  kernel {nr}x{nc} -> {len(rows)} generators ({time.monotonic()-t:.2f}s)',flush=True)
    return B


def compositions_zero(A,B):
    z={}; brow={}
    for (j,k),g in B['data'].items(): brow.setdefault(j,[]).append((k,g))
    for (i,j),f in A['data'].items():
        for k,g in brow.get(j,[]): z[i,k]=add(z.get((i,k),{}),mul(f,g))
    return all(not f for f in z.values())


def betti(n):
    return [1]+[int(n*sp.binomial(n-2,i)-sp.binomial(n,i+1)) for i in range(1,n-2)]+[1]


def standard(n):
    r=n-1; origin=monomial(r,0,1)
    Q=[{monomial(r,i,j):1,origin:-1} for i in range(r) for j in range(i+1,r) if (i,j)!=(0,1)]
    F=[pmat([Q])]; b=betti(n)
    for a in range(1,n-2):
        F.append(kernel(F[-1],r,2 if a==n-3 else 1))
        assert F[-1]['nc']==b[a+1],(n,a,F[-1]['nc'],b)
    return F


def slice_(A,m):
    return sp.SparseMatrix(A['nr'],A['nc'],{ij:f[m] for ij,f in A['data'].items() if m in f})


def fr(F):
    n=len(F)+2; r=n-1
    ends={(i,j):slice_(F[0],monomial(r,i-1,j-1)) for i in range(1,n) for j in range(1,n)}
    tails={(i,j):slice_(F[-1],monomial(r,i-1,j-1)) for i in range(1,n) for j in range(1,n)}
    middles=[{i:slice_(A,monomial(r,i-1)) for i in range(1,n)} for A in F[1:-1]]
    @lru_cache(None)
    def bracket(a):
        u=ends[a[:2]]
        for k in range(n-4): u=u*middles[k][a[k+2]]
        return (u*tails[a[-2:]])[0]
    anchors={3:[2,1],4:[2,1,1],5:[2,1,4,3]}.get(n,list(range(2,n))+[1])
    C=blank(n)
    for i in range(1,n):
        for j in range(i+1,n):
            for k in range(1,n):
                if k in [i,j]: continue
                rest=[l for l in range(1,n) if l not in [i,j,k]]
                put(C,i,j,k,(-1)**(n+1)*sign([i,j,k]+rest)*bracket(tuple([i,i]+rest+[j,j])))
        for j in range(1,n):
            if j==i: continue
            rest=[l for l in range(1,n) if l not in [i,j]]
            put(C,i,i,j,sign([i,j]+rest)*bracket(tuple([i,i]+rest+[i])))
        k=anchors[i-1]
        for j in range(1,n):
            if j in [i,k]: continue
            rest=[l for l in range(1,n) if l not in [i,j,k]]
            put(C,i,j,j,(-1)**n*sign([i,j,k]+rest)*bracket(tuple([i,i]+rest+[j,k])))
    for i in range(1,n):
        j,k=[l for l in range(1,n) if l!=i][:2]
        rest=[l for l in range(1,n) if l not in [i,j,k]]
        put(C,i,i,i,C[i][j][j]+C[i][k][k]+(-1)**(n+1)*sign([i,j,k]+rest)*bracket(tuple([i,j]+rest+[k,i])))
    return constants0(C)


def basis_transform(C,B):
    n=len(C); Bi=B.inv(); D=blank(n)
    for i in range(1,n):
        for j in range(i,n):
            v=sp.zeros(1,n)
            for a in range(n):
                for b in range(n):
                    z=B[i,a]*B[j,b]
                    if not z: continue
                    for k in range(n): v[k]+=z*C[a][b][k]
            v=v*Bi
            for k in range(n): put(D,i,j,k,v[k])
    return D


def transport(C,L):
    n=len(C); B=sp.diag(sp.ones(1),L); D=basis_transform(C,B)
    a={3:[2,1],4:[2,1,1],5:[2,1,4,3]}.get(n,list(range(2,n))+[1])
    H=sp.eye(n)
    for i in range(1,n): H[i,0]=-D[i][a[i-1]][a[i-1]]
    return basis_transform(D,H)


def substitute(A,g):
    r=g.rows; variables=[{monomial(r,i):g[i,j] for i in range(r) if g[i,j]} for j in range(r)]
    data={}
    for ij,f in A['data'].items():
        z={}
        for e,c in f.items():
            term={(0,)*r:c}
            for j,pow_ in enumerate(e):
                for _ in range(pow_): term=mul(term,variables[j])
            z=add(z,term)
        if z: data[ij]=z
    return {'nr':A['nr'],'nc':A['nc'],'data':data}


def scalar(A,u):
    return {'nr':A['nr'],'nc':A['nc'],'data':{ij:{e:u*c for e,c in f.items()} for ij,f in A['data'].items()}}


def export_magma(F,n,path):
    def poly(f):
        if not f: return 'P!0'
        terms=[]
        for e,c in sorted(f.items()):
            term=str(c)
            for i,v in enumerate(e):
                if v: term+=f'*x[{i+1}]'+(f'^{v}' if v>1 else '')
            terms.append(term)
        return '('+' + '.join(terms)+')'
    lines=[f'// Integral degree-{n} reference resolution: axes plus (1:...:1).',
           f'function StandardResolution{n}(R)',f'    P<[x]> := PolynomialRing(R,{n-1});','    F := [* *];']
    for A in F:
        cells=[poly(A['data'].get((i,j),{})) for i in range(A['nr']) for j in range(A['nc'])]
        lines+=[f'    Append(~F,Matrix(P,{A["nr"]},{A["nc"]},[']
        for pos in range(0,len(cells),8): lines.append('        '+','.join(cells[pos:pos+8])+(',' if pos+8<len(cells) else ''))
        lines+=['    ]));']
    lines+=['    return F;','end function;']; path.write_text('\n'.join(lines)+'\n')


def read_fixture(n):
    raw=json.loads((Path(__file__).parent/'fixtures'/f'standard_degree_{n}.json').read_text())
    return [{'nr':A['rows'],'nc':A['cols'],'data':{(i,j):{tuple(e):sp.Integer(c) for e,c in f} for i,j,f in A['entries']}} for A in raw]


def run():
    results={}; out=Path(__file__).parent/'fixtures'; out.mkdir(exist_ok=True)
    for n in [4,5,6,7]:
        print('degree',n,flush=True); F=standard(n); C=fr(F)
        ok,why=associative(C); assert ok,(n,why)
        d=disc(C); assert d==1,(n,d)
        for p in [2,3,5,7,11]:
            FF=[{'nr':A['nr'],'nc':A['nc'],'data':{ij:{e:c%p for e,c in f.items() if c%p} for ij,f in A['data'].items()}} for A in F]
            D=fr(FF); assert associative(D,p)[0]
            assert all((D[i][j][k]-C[i][j][k])%p==0 for i in range(n) for j in range(n) for k in range(n))
        g=sp.eye(n-1); g[0,0]=2; g[0,1]=3; g[1,2]=-1
        FF=[substitute(A,g) for A in F]; FF[-1]=scalar(FF[-1],3)
        D=fr(FF); predicted=transport(C,3*g.det()*g)
        assert D==predicted,(n,'coordinate action basis mismatch')
        assert disc(D)==3**(2*(n-1))*g.det()**(2*n)*d
        export_magma(F,n,out/f'standard_degree_{n}.m')
        encoded=[{'rows':A['nr'],'cols':A['nc'],'entries':[[i,j,[[list(e),int(c)] for e,c in f.items()]] for (i,j),f in A['data'].items()]} for A in F]
        (out/f'standard_degree_{n}.json').write_text(json.dumps(encoded))
        results[f'degree_{n}']={'betti':betti(n),'discriminant':str(d),'integral_associativity':True,'primes_checked':[2,3,5,7,11], 'coordinate_and_endpoint_action':True}
    return results

if __name__=='__main__':
    results=run(); (Path(__file__).parent/'resolution-reference-results.json').write_text(json.dumps(results,indent=2)); print(json.dumps(results,indent=2))
