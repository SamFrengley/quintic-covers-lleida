"""Independent exact-arithmetic checks of the formulas used by the Magma package.
This is NOT a Magma runtime test. Run with Python 3 and sympy.
"""
from itertools import permutations
from random import Random
import json
import sympy as s


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1,len(p)))


def blank(d):
    C = [[[0 for k in range(d)] for j in range(d)] for i in range(d)]
    for i in range(d): C[0][i][i] = C[i][0][i] = 1
    return C


def put(C,i,j,k,v):
    C[i][j][k]=C[j][i][k]=v


def constants0(C):
    n=len(C)-1
    for i in range(1,n+1):
        for j in range(i,n+1):
            k=2 if i==1 else 1
            v=sum(C[j][k][r]*C[r][i][k]-C[i][j][r]*C[r][k][k] for r in range(1,n+1))
            put(C,i,j,0,v)
    return C


def quartic(A,B):
    C=blank(4)
    lm=lambda i,j,k,l: A[i-1][j-1]*B[k-1][l-1]-B[i-1][j-1]*A[k-1][l-1]
    eps=[0,1,-1,1]
    CC=[0,lm(2,3,1,1),-lm(1,3,2,2),lm(1,2,3,3)]
    for i,j,k in permutations(range(1,4)):
        z=sign([i,j,k])
        put(C,i,i,i,z*lm(i,k,i,j)+CC[i])
        put(C,i,i,j,z*lm(i,i,i,k))
        put(C,i,j,i,((z+eps[j])//2)*lm(i,k,j,j))
        put(C,i,j,k,z*lm(j,j,i,i))
    return constants0(C)


def pf(A):
    out=[]
    for i in range(5):
        a,b,c,d=[j for j in range(5) if j!=i]
        out.append((-1)**i*(A[a][b]*A[c][d]-A[a][c]*A[b][d]+A[a][d]*A[b][c]))
    return out


def add(A,B): return [[a+b for a,b in zip(r,t)] for r,t in zip(A,B)]


def bil(A,B): return [a-b-c for a,b,c in zip(pf(add(A,B)),pf(A),pf(B))]


def contract(u,A,v): return sum(u[a]*A[a][b]*v[b] for a in range(5) for b in range(5))


def quintic(A):
    C=blank(5)
    P=[pf(a) for a in A]
    B=[[bil(a,b) for b in A] for a in A]
    def bracket(i,j,k,l,m): return contract(B[i-1][j-1],A[k-1],B[l-1][m-1])
    for i in range(1,5):
        for j in range(i+1,5):
            for k in range(1,5):
                if k not in [i,j]:
                    l=next(r for r in range(1,5) if r not in [i,j,k])
                    put(C,i,j,k,sign([i,j,k,l])*contract(P[i-1],A[l-1],P[j-1]))
    for i in range(1,5):
        for j in range(1,5):
            if j!=i:
                k,l=[r for r in range(1,5) if r not in [i,j]]
                put(C,i,i,j,sign([i,j,k,l])*bracket(l,i,i,i,k))
    anchors=[0,2,1,4,3]
    for i in range(1,5):
        k=anchors[i]
        put(C,i,k,k,0)
        for j in range(1,5):
            if j not in [i,k]:
                l=next(r for r in range(1,5) if r not in [i,j,k])
                put(C,i,j,j,sign([i,j,k,l])*contract(B[j-1][k-1],A[l-1],P[i-1]))
    for i in range(1,5):
        j,k,l=[r for r in range(1,5) if r!=i]
        put(C,i,i,i,C[i][j][j]+C[i][k][k]+sign([i,j,k,l])*bracket(i,j,l,k,i))
    return constants0(C)


def associative(C,p=0):
    d=len(C)
    for i in range(d):
        for j in range(d):
            for k in range(d):
                for l in range(d):
                    v=sum(C[i][j][r]*C[r][k][l]-C[j][k][r]*C[i][r][l] for r in range(d))
                    if p: v%=p
                    if v!=0: return False,(i,j,k,l,v)
    return True,None


def alt(u):
    A=[[0]*5 for _ in range(5)]
    for v,(i,j) in zip(u,[(i,j) for i in range(5) for j in range(i+1,5)]):
        A[i][j],A[j][i]=v,-v
    return A


def quintic_model(a):
    a0,a1,a2,a3,a4,a5=a
    return [alt([-a0,-a1,0,0,-a2,0,0,0,-1,0]),
            alt([0,0,0,0,a3,0,1,1,0,0]),
            alt([0,-a3,0,-1,-a4,-1,0,0,0,0]),
            alt([-a3,0,1,0,-a5,0,0,0,0,0])]


def matrices(C):
    d=len(C)
    return [s.Matrix(d,d,lambda k,j:C[i][j][k]) for i in range(d)]


def disc(C):
    L=matrices(C)
    return s.det(s.Matrix(len(L),len(L),lambda i,j:s.trace(L[i]*L[j])))


def matrix_mul(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A): return list(map(list,zip(*A)))


def run():
    rng=Random(20261002)
    results={}
    for degree,fn,size in [(4,quartic,3),(5,quintic,5)]:
        count=0
        for p in [0,2,3,5,7,101]:
            for _ in range(20):
                if degree==4:
                    mats=[]
                    for j in range(2):
                        A=[[0]*3 for _ in range(3)]
                        for i in range(3):
                            for k in range(i,3):
                                A[i][k]=A[k][i]=rng.randrange(-4,5)
                        mats.append(A)
                    C=fn(*mats)
                else:
                    mats=[alt([rng.randrange(-2,3) for _ in range(10)]) for j in range(4)]
                    C=fn(mats)
                ok,why=associative(C,p)
                assert ok,(degree,p,why)
                # Reduction commutes with construction, including p=2 and p=3.
                if p:
                    red=[[[v%p for v in row] for row in A] for A in mats]
                    D=fn(*red) if degree==4 else fn(red)
                    assert all((C[i][j][k]-D[i][j][k])%p==0 for i in range(degree) for j in range(degree) for k in range(degree))
                count+=1
        results[f'degree_{degree}_associativity_and_reduction']=count
    x=s.symbols('x')
    for a in [[-1,-1,0,0,0,1],[1,2,3,4,5,1],[0,0,0,0,0,1]]:
        C=quintic(quintic_model(a))
        f=sum(c*x**i for i,c in enumerate(a))
        assert s.expand((-matrices(C)[4]).charpoly(x).as_expr()-f)==0
        assert disc(C)==s.discriminant(f,x)
    results['monogenic_quintic_charpoly_discriminant']=3
    # Quartic polynomial conversion and the integral cubic resolvent.
    u,v=s.symbols('u v')
    A=[[1,0,0],[0,0,-1],[0,-1,0]]
    for a in [[1,2,3,4,1],[-1,-1,0,0,1],[0,0,0,0,1]]:
        B=[[0,a[3],a[1]],[a[3],a[4],a[2]],[a[1],a[2],a[0]]]
        C=quartic(A,B); f=sum(c*x**i for i,c in enumerate(a))
        T=s.Matrix(3,3,lambda i,j:u*A[i][j]+v*B[i][j])
        r=4*T[0,0]*T[1,1]*T[2,2]+T[0,1]*T[0,2]*T[1,2]-T[0,0]*T[1,2]**2-T[1,1]*T[0,2]**2-T[2,2]*T[0,1]**2
        assert disc(C)==s.discriminant(f,x)==s.discriminant(r.subs(v,1),u)
    results['quartic_and_resolvent_discriminants']=3
    # A nontrivial graded specialization of every tensor coefficient.
    t=s.symbols('t')
    for d in [4,5]:
        if d==4:
            w=[0,-1,-2]; eq=[1,2]; AB=[]
            for e in eq:
                M=[[0]*3 for _ in range(3)]
                for i in range(3):
                    for j in range(i,3):
                        M[i][j]=M[j][i]=rng.choice([-3,-2,-1,1,2,3])*t**(e-w[i]-w[j])
                AB.append(M)
            C=quartic(*AB); delta=sum(eq)-sum(w)
        else:
            w=[0,1,2,-1]; rw=[0,1,2,0,1]; twist=2
            AA=[alt([rng.choice([-2,-1,1,2])*t**(twist+rw[i]+rw[j]-wk)
                     for i in range(5) for j in range(i+1,5)]) for wk in w]
            C=quintic(AA); delta=5*twist+2*sum(rw)-sum(w)
        aw=[0]+[delta-wi for wi in w]
        for i in range(d):
            for j in range(d):
                for k in range(d):
                    f=s.expand(C[i][j][k])
                    if f!=0:
                        assert s.Poly(f,t).monoms()==[(aw[i]+aw[j]-aw[k],)]
        results[f'degree_{d}_graded_structure_constants']=True
    # Universal signed Pfaffian syzygy in 10 independent variables.
    u=s.symbols('u0:10'); A=alt(u); v=pf(A)
    assert all(s.expand(sum(A[i][j]*v[j] for j in range(5)))==0 for i in range(5))
    results['universal_pfaffian_syzygy']=True
    # Universal quartic associativity over Z[a_ij,b_ij].
    vs=iter(s.symbols('a0:12')); AB=[]
    for _ in range(2):
        A=[[0]*3 for _ in range(3)]
        for i in range(3):
            for j in range(i,3): A[i][j]=A[j][i]=next(vs)
        AB.append(A)
    C=quartic(*AB)
    for i in range(1,4):
        for j in range(1,4):
            for k in range(1,4):
                for l in range(4):
                    assert s.expand(sum(C[i][j][r]*C[r][k][l]-C[j][k][r]*C[i][r][l] for r in range(4)))==0
    results['universal_quartic_associativity']=True
    return results

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
