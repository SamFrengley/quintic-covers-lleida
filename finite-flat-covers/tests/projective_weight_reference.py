"""Independent exact checks for projective weights and FV frame ordering.
This tests the mathematics, not Magma parsing or intrinsic dispatch.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp
from monogenic_reference import geometric_coordinates, quotient_comparison, ring_model
from reference_checks import pf, quintic, quintic_model


def homogeneous_degree(f, variables):
    p = sp.Poly(f, *variables)
    if p.is_zero:
        return None
    degrees = {sum(m) for m in p.monoms()}
    if len(degrees) != 1:
        raise ValueError("nonhomogeneous coefficient")
    return degrees.pop()


def input_weights(a, variables):
    support = [(i, homogeneous_degree(c, variables)) for i, c in enumerate(a) if c != 0]
    if len(support) <= 1:
        return (support[0][1] if support else 0), 0
    (i, di), (j, dj) = support[0], support[-1]
    if (di-dj) % (j-i):
        raise ValueError("nonintegral relative weight")
    r = (di-dj)//(j-i)
    c = di+i*r
    if any(v != c-k*r for k, v in support):
        raise ValueError("inconsistent degree progression")
    return c, r


def raw_frames(n, c, r):
    if n == 2:
        return [c-r], []
    if n == 3:
        return [c-2*r, c-r], []
    if n == 4:
        return [c-2*r, c-3*r, c-r], [2*c-4*r, c-2*r]
    if n == 5:
        return [c-i*r for i in range(1, 5)], [2*c-4*r, 2*c-5*r, 2*c-6*r, c-2*r, c-3*r]
    return [c-i*r for i in range(1, n)], []


def order(v):
    return sorted(range(len(v)), key=lambda i: (v[i], i))


def ordered_frames(n, c, r):
    eraw, fraw = raw_frames(n, c, r)
    pe, pf = order(eraw), order(fraw)
    return [eraw[i] for i in pe], [fraw[i] for i in pf], pe, pf


def order_quintic(A, pe, pf):
    return [[[A[k][pf[i]][pf[j]] for j in range(5)] for i in range(5)] for k in pe]


def quartic_equations(a):
    x = sp.symbols("x0:3")
    X, Y, Z = x
    return x, [X**2-Y*Z, a[0]*Z**2+a[1]*X*Z+a[2]*Y*Z+a[3]*X*Y+a[4]*Y**2]


def permute_variables(q, x, pe):
    inv = [pe.index(j) for j in range(len(pe))]
    return sp.expand(q.subs({x[j]: x[inv[j]] for j in range(len(x))}, simultaneous=True))


def relative_degree(q, x, w, base_variables):
    values = set()
    for mon, coef in sp.Poly(q, *x).terms():
        d = homogeneous_degree(coef, base_variables)
        if d is not None:
            values.add(d+sum(a*b for a, b in zip(mon, w)))
    assert len(values) == 1
    return values.pop()


def example(s, t, x):
    return (x**5 - 2*(9*t-128*s)*x**4 + (9*t-128*s)*(17*t-54*s)*x**3
            - 18*(5*t+4*s)*(9*t-128*s)**2*x**2
            - 27*(33*t**2-488*t*s-60*s**2)*(9*t-128*s)**2*x
            - 27*(27*t**2-92*t*s-3*s**2)*(9*t-128*s)**3)


def check_quintic_tensor(A, e, f, base_variables):
    checked = 0
    for k, matrix in enumerate(A):
        for i in range(5):
            for j in range(i+1, 5):
                d = homogeneous_degree(matrix[i][j], base_variables)
                if d is not None:
                    assert d == f[i]+f[j]+e[k]-sum(e)
                    checked += 1
    return checked


def permute_table(T, pe):
    p = [0]+[i+1 for i in pe]
    n = len(p)
    return [[[T[p[i]][p[j]][p[k]] for k in range(n)] for j in range(n)] for i in range(n)]


def run():
    s, t, x = sp.symbols("s t x")
    source = sp.Poly(example(s, t, x), x)
    a = [source.nth(i) for i in range(6)]
    c, r = input_weights(a, (s, t))
    assert (c, r) == (5, 1)

    e, f, pe, pF = ordered_frames(5, c, r)
    assert e == [1, 2, 3, 4]
    assert f == [2, 3, 4, 5, 6]
    A = order_quintic(quintic_model(a), pe, pF)
    checked = check_quintic_tensor(A, e, f, (s, t))

    # The five deleted-row Pfaffians occur in the same increasing f_i order.
    X = sp.symbols("X0:4")
    M = sum((X[k]*sp.Matrix(A[k]) for k in range(4)), sp.zeros(5))
    Q = pf(M.tolist())
    qdegrees = [relative_degree(q, X, [-v for v in e], (s, t)) for q in Q]
    assert qdegrees == [-v for v in f]
    # In FV order, the coefficient of X_a X_b in Pf_i has ordinary base
    # degree e_a+e_b-f_i.  This catches an actual reversal of the X-frame.
    coefficient_checks = 0
    for i, q in enumerate(Q):
        pq = sp.Poly(q, *X)
        for aa in range(4):
            for bb in range(aa, 4):
                mon = X[aa]*X[bb]
                coeff = pq.coeff_monomial(mon)
                if coeff != 0:
                    assert homogeneous_degree(coeff, (s,t)) == e[aa]+e[bb]-f[i]
                    coefficient_checks += 1

    # Reordering the nonidentity basis preserves the monogenic ring itself.
    Traw = ring_model(a)
    Tordered = permute_table(Traw, pe)
    # Independently run Bhargava's tensor formula on the reordered matrices.
    Ttensor_raw = quintic(quintic_model(a))
    assert all(sp.expand(quintic(A)[i][j][k]-permute_table(Ttensor_raw, pe)[i][j][k]) == 0 for i in range(5) for j in range(5) for k in range(5))
    Braw = quotient_comparison(Traw, source.as_expr(), x, geometric_coordinates(5, x))
    Bordered = sp.Matrix([Braw[0, :]]+[Braw[i+1, :] for i in pe])
    assert Bordered.det() in [-1, 1]
    # Check every product against the quotient in the ordered basis.
    n = 5
    for i in range(n):
        for j in range(n):
            lhs = sp.rem(sp.Poly(sum(Bordered[i,k]*x**k for k in range(n)), x)
                         * sp.Poly(sum(Bordered[j,k]*x**k for k in range(n)), x), source).as_expr()
            rhs = sum(Tordered[i][j][k] * sum(Bordered[k,l]*x**l for l in range(n)) for k in range(n))
            assert sp.expand(lhs-rhs) == 0

    # Quartic: both ambient coordinates and the two generators are reordered.
    aq = [t**4, t**3, t**2, t, 1]
    eq, fq, peq, pfq = ordered_frames(4, 4, 1)
    assert eq == [1,2,3] and fq == [2,4]
    vars4, rawQ = quartic_equations(aq)
    orderedQ = [permute_variables(rawQ[i], vars4, peq) for i in pfq]
    assert [relative_degree(q, vars4, [-v for v in eq], (s,t)) for q in orderedQ] == [-2,-4]

    # Formal low-degree splitting data: F=N_1 is empty for d=2,3.
    formal = {}
    for n in range(2, 6):
        ee, ff, _, _ = ordered_frames(n, n, 1)
        formal[n] = {"e": ee, "f": ff}
    assert formal == {
        2: {"e": [1], "f": []},
        3: {"e": [1,2], "f": []},
        4: {"e": [1,2,3], "f": [2,4]},
        5: {"e": [1,2,3,4], "f": [2,3,4,5,6]},
    }

    # Negative relative weights are sorted too; ordering is not hard-coded reversal.
    for n in range(3, 6):
        ee, ff, _, _ = ordered_frames(n, 7, -2)
        assert ee == sorted(ee)
        assert ff == sorted(ff)

    bad = [[1,0,0,t**3,s,1], [s+t**2,0,0,0,0,1], [s,0,0,0,0,1]]
    for aa in bad:
        try:
            input_weights(aa, (s,t))
        except ValueError:
            pass
        else:
            raise AssertionError("bad grading was accepted")

    return {
        "user_quintic_e_frame": e,
        "user_quintic_f_frame": f,
        "nonzero_quintic_entries_checked": checked,
        "pfaffian_relative_degrees": qdegrees,
        "pfaffian_coefficient_degree_checks": coefficient_checks,
        "ordered_monogenic_products_checked": 25,
        "ordered_basis_determinant": str(Bordered.det()),
        "quartic_e_frame": eq,
        "quartic_f_frame": fq,
        "formal_degree_2_through_5": formal,
        "negative_weight_sorting_checked": True,
        "native_magma_executed": False,
    }


if __name__ == "__main__":
    result = run()
    (Path(__file__).parent/"projective-weight-results.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
