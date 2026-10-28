"""Exact checks for retained homogeneous degree and nonmonic input.
Tests the formulas independently; not a Magma execution test.
"""
from pathlib import Path
import json
import sympy as s
from monogenic_reference import ring_model,canonical_binary,quotient_comparison,binary_ring_constants
from resolution_reference import pmat,kernel,fr
from reference_checks import associative,disc,quintic_model,pf
from geometry_reference import expr

def run():
    t=s.Symbol('t');out={}
    for n in range(2,8):
        # The homogeneous form Y^n has degree n, although f(x,1) is 1.
        a=[1]+[0]*n
        if n<6:T=ring_model(a)
        else:
            Q=canonical_binary(a);F=[pmat([Q])]
            for pos in range(1,n-2):F.append(kernel(F[-1],n-1,2 if pos==n-3 else 1))
            T=fr(F)
        v=[1,t] if n<4 else ([t,1,t*t] if n==4 else [t**i for i in reversed(range(n-1))])
        B=quotient_comparison(T,t**n,t,v)
        assert disc(T)==0 and associative(T)[0]
        if n==4:qs=[v[0]**2-v[1]*v[2],v[2]**2]
        elif n==5:
            M=sum((v[i]*s.Matrix(A) for i,A in enumerate(quintic_model(a))),s.zeros(5));qs=pf(M.tolist())
        elif n>5:qs=[expr(q,v) for q in canonical_binary(a)]
        else:qs=[t**n]
        assert all(s.rem(s.expand(q),t**n,t)==0 for q in qs)
        out[f'Y^{n}']={'rank':n,'basis_determinant':str(B.det()),'quotient':'Z[t]/t^'+str(n)}
    nonprimitive=[]
    for n in range(6,10):
        a=[2]+[0]*(n-1)+[2];T=binary_ring_constants(a)
        assert associative(T)[0]
        # When both extreme coefficients are even, this is not the
        # non-flat projective zero locus reduced modulo two.
        T2=[[[int(c)%2 for c in row] for row in L] for L in T]
        assert associative(T2)[0] and all(T2[i][j][k]==0 for i in range(1,n) for j in range(1,n) for k in range(n))
        nonprimitive.append(n)
    return {'forms_with_vanishing_x_n_coefficient':out,'nonprimitive_and_mod2_square_zero_ranks':nonprimitive}
if __name__=='__main__':
    result=run();(Path(__file__).parent/'constructor-results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
