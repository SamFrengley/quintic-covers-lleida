"""Exact tensor-action, basis-transport, and discriminant checks (not Magma).
Nonsymmetric matrices detect accidental transpose reversals; determinant-nonunit
examples are over Q, while reductions are checked where matrices remain units.
"""
from pathlib import Path
from random import Random
import json
import sympy as sp
from reference_checks import blank,put,quartic,quintic,quintic_model,alt,pf,disc,associative,matrices
from resolution_reference import transport,fr,pmat,monomial,substitute,scalar


def cubic(a):
    a,b,c,d=a; T=blank(3)
    for i,j,k,v in [(1,1,0,-a*c),(1,1,1,b),(1,1,2,-a),(1,2,0,-a*d),(2,2,0,-b*d),(2,2,1,d),(2,2,2,-c)]: put(T,i,j,k,v)
    return T


def cubic_action(a,g,twist):
    x,y=sp.symbols('x y'); f=sum(a[i]*x**(3-i)*y**i for i in range(4))
    f=sp.Poly(sp.expand(f.subs({x:g[0,0]*x+g[1,0]*y,y:g[0,1]*x+g[1,1]*y},simultaneous=True)/ (g.det() if twist else 1)),x,y)
    return [f.coeff_monomial(x**(3-i)*y**i) for i in range(4)]


def quartic_action(AB,g,h):
    mats=[]
    for A in AB:
        # Input is an unordered-monomial coefficient table, not a Gram matrix.
        gram=sp.Matrix(3,3,lambda i,j:sp.Rational(A[i][j],1 if i==j else 2))
        gram=g*gram*g.T
        mats.append(sp.Matrix(3,3,lambda i,j:gram[i,j]*(1 if i==j else 2)))
    return [(h[i,0]*mats[0]+h[i,1]*mats[1]).tolist() for i in range(2)]


def quintic_action(AA,g,h,twist=False):
    mats=[g*sp.Matrix(A)*g.T for A in AA]; factor=1/h.det() if twist else 1
    return [(factor*sum((h[i,j]*mats[j] for j in range(4)),sp.zeros(5))).tolist() for i in range(4)]


def polynomial_from_sympy(f,x):
    return {tuple(e):c for e,c in sp.Poly(f,*x).terms() if c}


def cross_check_fr_quartic(AB):
    r=3; Q=[]
    for A in AB: Q.append({monomial(r,i,j):A[i][j] for i in range(r) for j in range(i,r) if A[i][j]})
    F=[pmat([Q]),pmat([[Q[1]],[{m:-v for m,v in Q[0].items()}]])]
    assert fr(F)==quartic(*AB)


def cross_check_fr_quintic(AA):
    x=sp.symbols('x0:4'); M=sum((x[i]*sp.Matrix(AA[i]) for i in range(4)),sp.zeros(5))
    Q=[polynomial_from_sympy(q,x) for q in pf(M.tolist())]
    F=[pmat([Q]),pmat([[polynomial_from_sympy(M[i,j],x) for j in range(5)] for i in range(5)]),pmat([[q] for q in Q])]
    assert fr(F)==quintic(AA)


def cache_matrix_transport(C,L,D):
    # Verify the transported matrices using a full normalized basis transform,
    # independently of the direct new-table calculation.
    n=len(C); B=sp.diag(sp.ones(1),L)
    from resolution_reference import basis_transform
    U=basis_transform(C,B); anchors={3:[2,1],4:[2,1,1],5:[2,1,4,3]}[n]
    H=sp.eye(n)
    for i in range(1,n): H[i,0]=-U[i][anchors[i-1]][anchors[i-1]]
    B=H*B; LC=matrices(C); LD=matrices(D); Bt=B.T
    predicted=[Bt.inv()*sum((B[i,j]*LC[j] for j in range(n)),sp.zeros(n))*Bt for i in range(n)]
    assert predicted==LD
    trace=lambda LL:sp.Matrix(n,n,lambda i,j:sp.trace(LL[i]*LL[j]))
    assert trace(LD)==B*trace(LC)*B.T
    # The implemented O(n^3) trace-pairing formula, independently compared
    # with actual multiplication-matrix traces.
    vC=sp.Matrix([sum(C[i][j][j] for j in range(n)) for i in range(n)])
    vD=sp.Matrix([sum(D[i][j][j] for j in range(n)) for i in range(n)])
    assert vD==B*vC
    TC=sp.Matrix(n,n,lambda i,j:sum(C[i][j][k]*vC[k] for k in range(n)))
    TD=sp.Matrix(n,n,lambda i,j:sum(D[i][j][k]*vD[k] for k in range(n)))
    assert TC==trace(LC) and TD==trace(LD)


def run():
    rng=Random(1222026); result={}
    g2=sp.Matrix([[2,1],[3,2]])
    # determinant 1 nonsymmetric matrix, then determinant 2 to detect twists.
    for g in [g2,sp.Matrix([[2,1],[0,1]])]:
        for twist in [False,True]:
            for _ in range(6):
                a=[rng.randrange(-3,4) for _ in range(4)]; C=cubic(a)
                D=cubic(cubic_action(a,g,twist)); L=(1 if twist else g.det())*g
                assert D==transport(C,L),('cubic transport',a,g,twist)
                assert disc(D)==g.det()**(2 if twist else 6)*disc(C)
                cache_matrix_transport(C,L,D)
    result['cubic_actions_and_full_cache_transport']=24
    g3=sp.Matrix([[2,1,0],[0,1,1],[0,0,1]]); h2=sp.Matrix([[3,1],[0,1]])
    for _ in range(10):
        AB=[]
        for j in range(2):
            A=[[0]*3 for i in range(3)]
            for i in range(3):
                for k in range(i,3): A[i][k]=A[k][i]=rng.randrange(-3,4)
            AB.append(A)
        C=quartic(*AB); D=quartic(*quartic_action(AB,g3,h2)); L=g3.det()*h2.det()*g3
        assert D==transport(C,L), 'quartic transport'
        assert disc(D)==g3.det()**8*h2.det()**6*disc(C)
        cache_matrix_transport(C,L,D); cross_check_fr_quartic(AB)
    result['quartic_actions_cache_transport_and_FR_compatibility']=10
    g5=sp.eye(5); g5[0,0]=2; g5[0,1]=1; g5[2,3]=-1
    h4=sp.eye(4); h4[1,1]=3; h4[0,2]=1; h4[1,3]=2
    for _ in range(8):
        AA=[alt([rng.randrange(-2,3) for _ in range(10)]) for j in range(4)]
        C=quintic(AA); BB=quintic_action(AA,g5,h4); D=quintic(BB)
        L=g5.det()**2*h4.det()*h4
        assert D==transport(C,L), 'quintic transport'
        assert disc(D)==g5.det()**16*h4.det()**10*disc(C)
        cache_matrix_transport(C,L,D); cross_check_fr_quintic(AA)
        for p in [5,7,11]:
            red=[[[int(a)%p for a in row] for row in A] for A in BB]
            T=quintic(red)
            assert all((T[i][j][k]-D[i][j][k])%p==0 for i in range(5) for j in range(5) for k in range(5))
    result['quintic_actions_cache_transport_and_FR_compatibility']=8
    g5[0,0]=9
    assert g5.det()==h4.det()**2
    for _ in range(4):
        AA=[alt([rng.randrange(-2,3) for _ in range(10)]) for j in range(4)]
        C=quintic(AA); D=quintic(quintic_action(AA,g5,h4,True))
        assert D==transport(C,h4)
        assert disc(D)==h4.det()**2*disc(C)
        cache_matrix_transport(C,h4,D)
    result['FV_twisted_actions_and_cache_transport']=4
    return result

if __name__=='__main__':
    r=run(); (Path(__file__).parent/'action-reference-results.json').write_text(json.dumps(r,indent=2)); print(json.dumps(r,indent=2))
