"""Identify the reported equations and check the intended model independently.
This uses exact polynomial arithmetic, NOT Magma constructor dispatch.
"""
from pathlib import Path
import json
import re
import sympy as sp
from reference_checks import quintic_model, quintic, pf
from projective_weight_reference import ordered_frames, order_quintic, example

HERE = Path(__file__).resolve().parent


def run():
    s, t, x = sp.symbols('s t x')
    z = sp.symbols('Z0:5')
    X = sp.symbols('X1:5')
    a = sp.symbols('a0:5') + (sp.Integer(1),)
    e, f, pe, rows = ordered_frames(5, 5, 1)
    A = order_quintic(quintic_model(a), pe, rows)
    T = quintic(A)
    algebra = [sp.expand(z[i]*z[j]-sum(T[i][j][k]*z[0]*z[k] for k in range(5)))
               for i in range(1, 5) for j in range(i, 5)]
    assert len(algebra) == 10

    source = sp.Poly(example(s, t, x), x)
    values = dict(zip(a[:5], [source.nth(i) for i in range(5)]))
    text = (HERE/'fixtures/reported_quintic_algebra_output.txt').read_text()
    text = re.sub(r'X\[(\d+)\]', lambda m: f'Z{int(m[1])-1}', text)
    # The fixture is package-owned polynomial text, not arbitrary executable input.
    reported = sp.sympify(text.replace('^', '**'), locals={str(v): v for v in (s,t)+z})
    assert len(reported) == 10
    for i, (actual, expected) in enumerate(zip(reported, algebra)):
        assert sp.expand(actual-expected.subs(values)) == 0, f'reported equation {i+1}'

    M = sum((X[k]*sp.Matrix(A[k]) for k in range(4)), sp.zeros(5))
    model = [sp.expand(q) for q in pf(M.tolist())]
    x1,x2,x3,x4 = X
    a0,a1,a2,a3,a4,_ = a
    expected = [
        -x1*x1-a4*x1*x2-a2*x1*x4-a3*x2*x2-a1*x2*x4-a0*x3*x4,
        -x1*x2-a3*x1*x4-a4*x2*x2-a2*x2*x4-a1*x3*x4-a0*x4*x4,
        -x1*x3+x2*x2, -x1*x4+x2*x3, -x2*x4+x3*x3,
    ]
    assert all(sp.expand(q-r) == 0 for q,r in zip(model, expected))
    f_universal = sum(a[i]*x**i for i in range(6))
    point = {x1: x**3, x2: x**2, x3: x, x4: 1}
    restrictions = [sp.expand(q.subs(point)) for q in model]
    assert restrictions == [sp.expand(-x*f_universal), sp.expand(-f_universal), 0, 0, 0]
    # On X4=1, the last three quadrics give X2=X3^2 and X1=X3^3.
    # Hence the ideal is precisely the quotient by f, not just a set of points.
    point2 = {x1: x3**3, x2: x3**2, x4: 1}
    affine = [sp.expand(q.subs(point2)) for q in model]
    assert sp.expand(affine[1] + f_universal.subs(x,x3)) == 0

    checks = 0
    for i,q in enumerate(model):
        for mon,c in sp.Poly(q,*X).terms():
            c = sp.expand(c.subs(values))
            if c == 0:
                continue
            degrees = {sum(m) for m in sp.Poly(c,s,t).monoms()}
            assert degrees == {sum(mon[k]*e[k] for k in range(4))-f[i]}
            checks += 1
    return {
        'reported_equations_identified_exactly': 10,
        'reported_presentation': 'Algebra: ten quadrics, five fibre coordinates',
        'universal_model_equations_compared': 5,
        'model_fibre_variables': 4,
        'model_cox_variables': 6,
        'model_equations_on_canonical_point': ['-x*f', '-f', '0', '0', '0'],
        'affine_chart_is_polynomial_quotient': True,
        'example_coefficient_degree_checks': checks,
        'native_magma_execution': False,
    }


if __name__ == '__main__':
    result = run()
    (HERE/'presentation-results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
