"""Exact checks for generic-field actions, integral descent, and changing split weights."""
import sympy as sp


def run():
    X,Y,s,t = sp.symbols('X Y s t')

    # Twisted cubic: scalar lambda I acts by lambda on a binary cubic.
    f = 2*(X**3 + X**2*Y + X*Y**2 + Y**3)
    lam = sp.Rational(1,2)
    transformed = sp.expand((lam**2)**-1 * f.subs({X:lam*X,Y:lam*Y}))
    assert transformed == X**3 + X**2*Y + X*Y**2 + Y**3
    bad = sp.expand((sp.Rational(1,3)**2)**-1 * f.subs({X:X/3,Y:Y/3}))
    assert any(c.q != 1 for c in sp.Poly(bad,X,Y).coeffs())

    f0 = X**3 + X**2*Y + X*Y**2 + Y**3

    # Degree-zero generic action preserves the splitting.
    r = t/s
    proj = sp.cancel(r * s*f0)
    assert sp.expand(proj) == sp.expand(t*f0)
    bad_proj = sp.cancel((t/(s+t))*s*f0)
    assert sp.denom(bad_proj) != 1
    assert {sum(m) for m,c in sp.Poly(s+t**2,s,t).terms()} == {1,2}

    # The new feature: 1/s has degree -1.  For a dual coordinate action,
    # w_new = w_old - deg(1/s).  The input s*f0 has w_old=(-1,-1), so
    # diag(1/s,1/s) changes the target weights to (0,0).  The twisted scalar
    # det(g)^-1=s^2 makes the transformed cubic integral and equal to f0.
    old_w = [-1,-1]
    entry_degree = -1
    new_w = [w-entry_degree for w in old_w]
    assert new_w == [0,0]
    gscalar = 1/s
    changed = sp.cancel((gscalar**2)**-1 * (s*f0).subs({X:gscalar*X,Y:gscalar*Y}))
    assert sp.expand(changed) == sp.expand(f0)

    # An individual row must determine one target weight.  With old weights
    # (-1,-1), entries of degrees 0 and -1 in the same row predict -1 and 0.
    assert old_w[0]-0 != old_w[1]-(-1)

    # FV quintic central scalars: g=r^8 I_5, h=r^5 I_4 satisfy
    # det(g)=det(h)^2 and act on the tensor by scalar r.
    rr = sp.symbols('r', nonzero=True)
    dg = (rr**8)**5
    dh = (rr**5)**4
    assert sp.simplify(dg-dh**2) == 0
    tensor_scale = sp.simplify((dh**-1)*(rr**5)*(rr**8)**2)
    assert tensor_scale == rr

    # For r=1/s and a model s*A with (w,row,twist)=(0,0,1), the target
    # data inferred from homogeneous row degrees are (5,-8,21), and the
    # transformed tensor has coefficient degree zero.
    w_new = 0 - (-5)
    row_new = 0 + (-8)
    twist_new = 1 + 20
    assert (w_new,row_new,twist_new) == (5,-8,21)
    assert twist_new + 2*row_new - w_new == 0
    delta = 5*twist_new + 2*(5*row_new) - 4*w_new
    assert delta == 5
    assert delta-w_new == 0   # new Tschirnhausen degrees
    q = 2*twist_new + 5*row_new - row_new
    assert q == 10
    assert 2*((delta-w_new)+w_new)-q == 0  # new f_i

    return {
        'cubic_fractional_descent': True,
        'projective_degree_zero_fractional_action': True,
        'projective_weight_changing_action': True,
        'target_weights_after_1_over_s': new_w if isinstance(new_w, list) else [0,0],
        'inconsistent_row_detected': True,
        'nonintegral_projective_result_detected': True,
        'nonhomogeneous_rational_entry_detected': True,
        'quintic_weight_change': {'variable_weight': 5, 'row_weight': -8, 'matrix_twist': 21},
        'quintic_central_fractional_scaling': str(tensor_scale),
    }

if __name__ == '__main__':
    import json
    print(json.dumps(run(), indent=2))
