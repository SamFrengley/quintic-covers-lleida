"""Exact regression for the reported homogeneous prime fibre.

This checks quotient-ring identities, Pfaffians and Jacobians independently of
Magma. It does not claim to run Magma's scheme/factorization implementation.
"""
from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path
import sympy as sp
from projective_weight_reference import example, ordered_frames, order_quintic
from reference_checks import pf, quintic_model


def run() -> dict:
    s, t, x, u = sp.symbols('s t x u')
    X = sp.symbols('X1:5')
    pi = 3*s**2+14*s*t-t**2
    f = sp.Poly(example(s, t, x), x)
    coeff = [f.nth(i) for i in range(6)]
    e, syzygy, pe, pr = ordered_frames(5, 5, 1)
    A = order_quintic(quintic_model(coeff), pe, pr)
    matrix = sum((X[i]*sp.Matrix(A[i]) for i in range(4)), sp.zeros(5))
    Q = [sp.expand(q) for q in pf(matrix.tolist())]

    def reduce(expr):
        # Normal form in QQ[t,x,X1,...,X4][s]/(pi), with constant leading coefficient.
        return sp.rem(sp.expand(expr), pi, s)

    roots = [(17*t-249*s)/4, (141*s-9*t)/4, 14*t-202*s]
    r1, r2, r3 = roots
    assert reduce(f.as_expr()-(x-r1)**2*(x-r2)**2*(x-r3)) == 0
    assert all(reduce(a-b) != 0 for a, b in combinations(roots, 2))

    # Rewrite ALL six coefficients in the user's output using true s, not s/t.
    components = [
        [X[0]+(5567640*s*t**2-391781*t**3)*X[3],
         X[1]+(74451*s*t-5239*t**2)*X[3]/4,
         X[2]+(249*s-17*t)*X[3]/4],
        [X[0]+(-1008150*s*t**2+70941*t**3)*X[3],
         X[1]+(23829*s*t-1677*t**2)*X[3]/4,
         X[2]+(-141*s+9*t)*X[3]/4],
    ]
    old = [
        [X[0]+(5567640*u-391781)*t**3*X[3],
         X[1]+(74451*u-5239)*t**2*X[3]/4,
         X[2]+(249*u-17)*t*X[3]/4],
        [X[0]+(-1008150*u+70941)*t**3*X[3],
         X[1]+(23829*u-1677)*t**2*X[3]/4,
         X[2]+(-141*u+9)*t*X[3]/4],
    ]
    for root, comp, previous in zip(roots[:2], components, old):
        for i, (q, qold) in enumerate(zip(comp, previous)):
            assert reduce(q-(X[i]-root**(3-i)*X[3])) == 0
            assert sp.expand(q.subs(s, u*t)-qold) == 0
            weights = {sum(m)+sum(a*b for a,b in zip(n, [-1,-2,-3,-4]))
                       for n,c in sp.Poly(q,*X).terms()
                       for m in sp.Poly(c,s,t).monoms()}
            assert weights == {-(i+1)}

    Qred = [reduce(q) for q in Q]
    for i, q in enumerate(Qred):
        for mon, c in sp.Poly(q, *X).terms():
            if c == 0: continue
            expected_degree = sum(a*b for a,b in zip(mon,e))-syzygy[i]
            assert {sum(m) for m in sp.Poly(c,s,t).monoms()} == {expected_degree}

    # Full zero-dimensional scheme: the affine chart is the quotient by f,
    # not just a set of roots. The final three quadrics force X1=X3^3, X2=X3^2.
    chart = [q.subs(X[3],1) for q in Qred]
    param = {X[0]: X[2]**3, X[1]: X[2]**2}
    assert reduce(chart[0].subs(param)+X[2]*f.as_expr().subs(x,X[2])) == 0
    assert reduce(chart[1].subs(param)+f.as_expr().subs(x,X[2])) == 0
    assert all(reduce(q.subs(param)) == 0 for q in chart[2:])
    # On X4=0 the quadrics successively force X3=X2=X1=0: no points at infinity.
    assert sp.expand(Qred[4].subs(X[3],0)-X[2]**2) == 0
    assert sp.expand(Qred[2].subs({X[3]:0,X[2]:0})-X[1]**2) == 0
    assert sp.expand(Qred[0].subs({X[3]:0,X[2]:0,X[1]:0})+X[0]**2) == 0

    jac = sp.Matrix(chart).jacobian(X[:3])
    jacobian_ranks = []
    for root in roots:
        point = {X[0]:root**3,X[1]:root**2,X[2]:root}
        J = jac.subs(point).applyfunc(reduce)
        assert all(reduce(q.subs(point)) == 0 for q in chart)
        nonzero3 = any(reduce(J[list(rows),:].det()) != 0 for rows in combinations(range(5),3))
        nonzero2 = any(reduce(J[list(rows),list(cols)].det()) != 0
                       for rows in combinations(range(5),2) for cols in combinations(range(3),2))
        jacobian_ranks.append(3 if nonzero3 else 2 if nonzero2 else 1)
    assert jacobian_ranks == [2,2,3]

    # The singular scheme of a finite characteristic-zero hypersurface is (f,f').
    alpha = (-7+2*sp.sqrt(13))/3
    fa = sp.Poly(f.as_expr().subs({s:alpha,t:1}),x,extension=alpha)
    gcd = sp.gcd(fa,fa.diff()).monic()
    expected = sp.Poly((x-r1)*(x-r2),x).as_expr().subs({s:alpha,t:1})
    assert gcd == sp.Poly(expected,x,extension=alpha)
    assert sp.gcd(gcd,gcd.diff()).degree() == 0
    # Verify the fibre/total-space distinction instead of calling both singularities.
    fs = sp.diff(f.as_expr(),s)
    assert reduce(fs.subs(x,r1)) != 0
    assert reduce(fs.subs(x,r2)) == 0

    # Generic homogeneity checks in the new field presentation. The normal form
    # of a homogeneous coefficient must still have the same base degree.
    primes = [s-2*t, 3*s+2*t, s*s-2*t*t, s**3-2*t**3, s**4-2*t**4, pi]
    coefficient_checks = 0
    for prime in primes:
        p0 = prime.subs({s:u,t:1})
        for d in range(11):
            h = sum((i+1)*s**i*t**(d-i) for i in range(d+1))
            hred = sp.rem(h,prime,s)
            if hred != 0:
                assert {sum(m) for m in sp.Poly(hred,s,t).monoms()} == {d}
            h0 = sp.rem(h.subs({s:u,t:1}),p0,u)
            assert sp.expand(hred.subs(s,u*t)-h0*t**d) == 0
            coefficient_checks += 1
    return {
        'exact_quintic_factorization': '(x-r1)^2*(x-r2)^2*(x-r3)',
        'roots': [str(r) for r in roots], 'root_multiplicities':[2,2,1],
        'reported_component_coefficients_matched':6,
        'weighted_linear_component_equations_verified':6,
        'pfaffian_equations_specialized':5,
        'scheme_chart_equals_polynomial_quotient':True,
        'points_at_infinity':False, 'relative_jacobian_ranks':jacobian_ranks,
        'reduced_non_smooth_fibre_degree':2,
        'first_double_root_smooth_on_total_curve':True,
        'second_double_root_singular_on_total_curve':True,
        'homogeneous_normal_form_cases':coefficient_checks,
        'native_magma_execution':False,
    }


if __name__ == '__main__':
    result = run()
    (Path(__file__).with_name('prime-fibre-results.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
