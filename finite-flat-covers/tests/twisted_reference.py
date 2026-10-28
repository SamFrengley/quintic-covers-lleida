"""Checks the v3 determinant twists against direct fresh multiplication tables.
This independently validates the mathematics, not Magma intrinsic dispatch.
"""
from pathlib import Path
from random import Random
import json
import sympy as s
from reference_checks import blank,put,quartic,quintic,alt,disc,matrices
from action_reference import cubic,cubic_action,quartic_action,quintic_action,cache_matrix_transport
from resolution_reference import basis_transform,transport,fr,read_fixture,substitute,scalar


def quad(a):
    a,b,c=a;T=blank(2);put(T,1,1,0,-a*c);put(T,1,1,1,-b);return T


def qa(a,g,tw):
    x,y=s.symbols('x y');a,b,c=a;factor=1/g.det() if tw else 1
    f=s.Poly(factor*(a*(g[0,0]*x+g[1,0]*y)**2+b*(g[0,0]*x+g[1,0]*y)*(g[0,1]*x+g[1,1]*y)+c*(g[0,1]*x+g[1,1]*y)**2),x,y)
    return [f.coeff_monomial(x*x),f.coeff_monomial(x*y),f.coeff_monomial(y*y)]


def run():
    rng=Random(20261004);out={};g2=s.Matrix([[2,1],[0,1]])
    for tw in [True,False]:
        for _ in range(12):
            a=[rng.randrange(-5,6) for _ in range(3)];C=quad(a);D=quad(qa(a,g2,tw))
            factor=1/g2.det() if tw else 1
            beta=-factor*(a[0]*g2[0,0]*g2[1,0]+a[1]*g2[0,1]*g2[1,0]+a[2]*g2[0,1]*g2[1,1])
            B=s.Matrix([[1,0],[beta,factor*g2.det()]])
            assert basis_transform(C,B)==D
            assert disc(D)==(1 if tw else g2.det()**2)*disc(C)
            assert [B.T.inv()*sum((B[i,j]*matrices(C)[j] for j in range(2)),s.zeros(2))*B.T for i in range(2)]==matrices(D)
    out['quadratic_full_product_and_cache_transport_cases']=24
    for tw in [True,False]:
        for _ in range(8):
            a=[rng.randrange(-3,4) for _ in range(4)];C=cubic(a);D=cubic(cubic_action(a,g2,tw));L=(1 if tw else g2.det())*g2
            assert D==transport(C,L);assert disc(D)==g2.det()**(2 if tw else 6)*disc(C)
            cache_matrix_transport(C,L,D)
    out['cubic_cases']=16
    g3=s.Matrix([[2,1,0],[0,1,1],[0,0,1]])
    for tw in [True,False]:
        h2=s.Matrix([[2 if tw else 3,1],[0,1]])
        for _ in range(10):
            AB=[]
            for __ in range(2):
                A=s.zeros(3)
                for i in range(3):
                    for j in range(i,3):A[i,j]=A[j,i]=rng.randrange(-3,4)
                AB.append(A.tolist())
            C=quartic(*AB);BB=quartic_action(AB,g3,h2)
            if tw:BB=[(s.Matrix(A)/h2.det()).tolist() for A in BB]
            D=quartic(*BB);L=g3 if tw else g3.det()*h2.det()*g3
            assert D==transport(C,L);assert disc(D)==(g3.det()**2 if tw else g3.det()**8*h2.det()**6)*disc(C)
            cache_matrix_transport(C,L,D)
            if tw:
                # Wood's original Gamma uses det(g3)*det(hWood)=1.
                hWood=h2/h2.det();assert g3.det()*hWood.det()==1
                assert BB==quartic_action(AB,g3,hWood)
    out['quartic_cases_including_Wood_reparametrization']=20
    h4=s.eye(4);h4[1,1]=3;h4[0,2]=1;h4[1,3]=2
    for tw in [True,False]:
        g5=s.eye(5);g5[0,0]=9 if tw else 2;g5[0,1]=1;g5[2,3]=-1
        for _ in range(8):
            AA=[alt([rng.randrange(-2,3) for _ in range(10)]) for __ in range(4)]
            C=quintic(AA);D=quintic(quintic_action(AA,g5,h4,tw))
            L=h4 if tw else g5.det()**2*h4.det()*h4
            assert D==transport(C,L)
            assert disc(D)==(h4.det()**2 if tw else g5.det()**16*h4.det()**10)*disc(C)
            cache_matrix_transport(C,L,D)
    out['quintic_cases']=16
    for n in [6,7]:
        F=read_fixture(n);C=fr(F);g=s.eye(n-1);g[0,0]=2;g[0,1]=1;g[1,2]=3
        for tw in [True,False]:
            for u in [1,3]:
                FF=[substitute(A,g) for A in F];FF[-1]=scalar(FF[-1],u/g.det() if tw else u)
                D=fr(FF);L=(u if tw else u*g.det())*g
                assert D==transport(C,L)
                assert disc(D)==u**(2*n-2)*g.det()**(2 if tw else 2*n)*disc(C)
    out['higher_resolution_cases']=8
    return out

if __name__=='__main__':
    out=run();(Path(__file__).parent/'twisted-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
