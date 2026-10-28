# Homogeneous prime fibres and their printed coordinates

## The reported issue

For `pi = 3*s^2 + 14*s*t - t^2`, version 11 used the tower

```text
k0 = QQ(alpha),  3*alpha^2 + 14*alpha - 1 = 0;
K = k0(t);
s |-> alpha*t,  t |-> t.
```

It then named `alpha` **s**. Thus the printed s meant the ratio of the original
homogeneous coordinates, not the original s. For example,

```text
(5567640*alpha - 391781)*t^3
```

is homogeneous of base degree 3 (`alpha` has degree zero), but printing `alpha`
as s misleadingly suggests mixed base degrees 4 and 3. The base-change map and
the two reported points were correct; their coordinate notation was not.

## Version 12: retain the actual homogeneous coordinates

The default is still `Homogeneous := true`. No chart is silently selected.
The coefficient field is now represented as

```text
K = QQ(t)[s] / (s^2 + (14/3)*t*s - (1/3)*t^2),
```

with `phi(s)` equal to the displayed algebraic generator s and `phi(t)` equal
to the displayed transcendental generator t. This is the same abstract field
`Frac(QQ[s,t]/(pi))` as before; the presentation is different.
It is an algebraic function field (`FldFun`), not the previous rational function
field over a number field (`FldFunRat`). Code must not assume the previous type
or that `BaseRing(K)` is the Proj residue field. The separate, experimental
fresh characteristic-2 correction backend still accepts only finite fields and
explicit rational function fields over them; this patch does not extend that
backend to `FldFun`. Specializing an already chosen conjectural resolvent remains
a different supported operation.

```magma
B,phi := BaseChange(A,3*s^2+14*s*t-t^2);
assert phi(3*s^2+14*s*t-t^2) eq 0;
[phi(s),phi(t)];                // [s,t], with their original meanings
Y := UnderlyingScheme(B);
IrreducibleComponents(ReducedSubscheme(SingularSubscheme(Y)));
```

The implementation uses Magma's documented `ext<F | g>` over `F=k(t)`.
A coordinate prime such as `(t)` is handled separately: its homogeneous field
is `k(s)`, with `s |-> s, t |-> 0`. A linear prime requires no algebraic extension.
The separable-function-field backend reports an explicit error on an inseparable
polynomial prime; no approximation or arbitrary root is substituted.

Over Z the horizontal construction still passes to QQ; it does not pretend to
retain integral arithmetic at primes dividing the leading coefficient of pi.
Reduction at a rational prime and `ToField := false` are unchanged.

## Exact check of the two reported components

In the homogeneous field, put

```text
r1 = (17*t - 249*s)/4;
r2 = (141*s - 9*t)/4;
r3 = 14*t - 202*s.
```

For the supplied quintic, the following is an exact identity modulo pi:

```text
f(x) = (x-r1)^2 * (x-r2)^2 * (x-r3).
```

The three roots are distinct. The full fibre has length five, and its reduced
non-smooth locus consists of the two points

```text
[r1^3 : r1^2 : r1 : 1],    [r2^3 : r2^2 : r2 : 1].
```

Equivalently, the first component has ideal

```text
X[1] + (5567640*s*t^2 - 391781*t^3)*X[4],
X[2] + (74451*s*t - 5239*t^2)/4*X[4],
X[3] + (249*s - 17*t)/4*X[4],
```

and the second has ideal

```text
X[1] + (-1008150*s*t^2 + 70941*t^3)*X[4],
X[2] + (23829*s*t - 1677*t^2)/4*X[4],
X[3] + (-141*s + 9*t)/4*X[4].
```

These are ideal generators, not a promise of Magma's exact term ordering or
factorization of printed coefficients. Their nonconstant coefficients have
base degrees 3, 2 and 1. With the recorded coordinate weights `[-1,-2,-3,-4]`,
the three equations have base weights -1, -2 and -3, respectively; all have
fibre degree one. Individual equations are homogeneous in the fibre variables.
Over a coefficient FIELD, Magma does not impose the old Cox bigrading itself.

## The genuine Proj residue field is smaller

Use the existing option

```magma
B0,phi0 := BaseChange(A,pi : Homogeneous := false);
```

to take `t=1` and work over `QQ[s]/(3*s^2+14*s-1)`. In this mode s is the
AFFINE chart coordinate s/t, and t is absent (its image is 1), so there is no
ambiguous simultaneous use of s for a ratio and t for a scaling variable.
The prime `(t)` instead uses the chart `s=1, t=0`.

The distinction is between the degree-zero field of a homogeneous prime on
Proj and the full fraction field of its homogeneous coordinate ring. On the
`t != 0` chart the two fibre presentations are related by
`Y[i] = t^(e_i)*X[i]` in the recorded FV normalization. In particular, they
have isomorphic geometric fibres; their coordinate trivializations differ.

## Singular fibre versus singular total curve

`SingularSubscheme` here is relative to the field `BaseRing(B)`: it tests the
zero-dimensional fibre for smoothness. A double root can arise at a smooth
ramification point of the total curve. In this example, on `t=1`, the base
derivative `partial f / partial s` is nonzero at r1 and zero at r2. Both are
non-smooth points of the fibre, but only the second is singular on this affine
chart of the total characteristic-zero curve.

Do not interpret the output of the composite `SingularSubscheme(BaseChange(...))`
as automatically equal to base change of the total curve's singular locus.

## Names and caching

The native projective ambient is now built from the ALREADY NAMED fibre
polynomial ring. It no longer creates a second anonymous ring and loses the
`X[i]` names. Scroll/toric ambients explicitly receive the Cox-ring names too.
Subschemes inherit their ambient coordinates.

No public attributes or options were added. Construction, base change, and model
geometry do not request a discriminant. A cached discriminant specializes along
the same map; unknown multiplication tables and resolutions remain lazy.

## Verification

Run `magma -b tests/v12_only.m` for the exact reported order of calls over Z and
QQ, homogeneous binary input, literal coordinate names, both field conventions,
coordinate and linear primes, and the actual `SingularSubscheme`/reduction/component
sequence. These native tests have not been executed in the authoring environment.

`python tests/prime_fibre_reference.py` independently checks the factorization,
all six reported component coefficients, all five specialized Pfaffians, the
quotient-ring chart, the relative Jacobian ranks 2,2,3, the non-smooth ideal, and
66 homogeneous normal-form examples. It is not a substitute for Magma integration.

## Primary references

- Magma: creation and naming of algebraic function fields,
  https://magma.maths.usyd.edu.au/magma/handbook/text/503
- Magma: projective ambient from a polynomial ring and naming schemes,
  https://magma.maths.usyd.edu.au/magma/handbook/text/1430
- Magma: `SingularSubscheme` is the non-smooth subscheme relative to the base field,
  https://magma.maths.usyd.edu.au/magma/handbook/text/1439
- Stacks Project, Proj via degree-zero homogeneous localizations,
  https://stacks.math.columbia.edu/tag/01M3
