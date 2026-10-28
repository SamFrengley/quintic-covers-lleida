# Projective bases, FV ordering, and splitting invariants

## Constructor

```magma
R<s,t> := PolynomialRing(Integers(),2);
P<x> := PolynomialRing(R);
C := FiniteFlatCover(x^5+s*x^4+t^5 : ProjectiveBase := true);
```

`ProjectiveBase := false` is the default. The homogeneous base ring must be a
standard graded two-variable polynomial ring such as `Z[s,t]` or `k[s,t]`.

## Polynomial input is put in FV order

For `f = sum a_i x^i`, the constructor first checks for integers `c,r` with

```text
deg(a_i) = c-i*r
```

for every nonzero coefficient. In degrees 3, 4, and 5, when the grading is
inferred automatically, the **actual tensor frame is then reordered**, not just
the displayed invariant list.

The convention is the one used by Frengley--Vemulapalli:

```text
e_1 <= ... <= e_(d-1)
f_1 <= ... <= f_rank(F)
```

Thus `X[1]` is the coordinate belonging to `e_1`, `X[2]` to `e_2`, and so on.
For a quintic, `A[k]` belongs to `e_k`, while row/column `i` belongs to `f_i`.
Consequently

```text
deg(A[k][i,j]) = f_i + f_j + e_k - sum(e_l).
```

The five deleted-row Pfaffians are also returned in increasing `f_i` order.

For the example from `examples/projective_quintic.m`:

```magma
e := TschirnhausenInvariants(C : Sorted := false);
f := FirstSyzygyInvariants(C : Sorted := false);

assert e eq [1,2,3,4];
assert f eq [2,3,4,5,6];
assert BundleWeights(C : Embedding := "Model") eq [-1,-2,-3,-4];
```

For polynomial-derived low-degree models in automatic grading, `Sorted := false`
and the default sorted output therefore agree. `Sorted := false` is still useful
for arbitrary tensor input, where the library never silently permutes a user
supplied frame.

Explicit `VariableWeights`, `RowWeights`, or `MatrixTwist` are treated as an
expert override and preserve the supplied frame.

## The e_i and f_i in degrees 2 through 5

`TschirnhausenInvariants(C)` is available for every projective cover for which a
split algebra grading is recorded. In degrees 2--5 the polynomial constructor
computes the data formally from the coefficient degrees; no multiplication table,
resolution, discriminant, or geometry is constructed.

`FirstSyzygyInvariants(C)` means the splitting type of the Casnati--Ekedahl
bundle `F=N_1` of quadratic generators. Hence:

| degree | rank E | rank F | accessor behaviour |
|---:|---:|---:|---|
| 2 | 1 | 0 | `f = []` |
| 3 | 2 | 0 | `f = []` |
| 4 | 3 | 2 | two quadratic-generator degrees |
| 5 | 4 | 5 | five Pfaffian-generator degrees |

For the standard monic weight-one families this gives

```text
d=2: e=[1],       f=[]
d=3: e=[1,2],     f=[]
d=4: e=[1,2,3],   f=[2,4]
d=5: e=[1,2,3,4], f=[2,3,4,5,6].
```

The empty list in degrees 2 and 3 is intentional: the relative canonical ideal
has no quadratic-generator bundle `N_1` there (a triple cover is cut out by a
cubic).

## Relation with stored grading weights

The package records model coordinate weights `w_i`; after fixing the common
projective twist `delta`,

```text
e_i = delta-w_i,
f_j = 2*delta-q_j,
```

where `q_j` is the relative base degree of the j-th quadratic generator. The
automatic polynomial normalization through degree 5 chooses the natural frame
with increasing `e_i` and `f_i`.

For a quintic the row weights are the `f_i` themselves and the tensor twist is
`-sum(e_i)` in this normalization.

## What is and is not reordered

Automatic FV reordering applies to polynomial input with `ProjectiveBase := true`
and inferred grading. It covers both

```magma
P<x> := PolynomialRing(R);
FiniteFlatCover(f : ProjectiveBase := true);
```

and homogeneous binary input. A bare pair of quadrics or quadruple of alternating
matrices is **not** reordered: its frame is part of the input data.

Actions and base changes preserve the recorded frame rather than sorting again.
This matters when specialisation makes coefficients vanish.

## Which equations are returned by default

For **polynomial input**, `Embedding := "Model"` is now the default.  Thus on a
projective base

```magma
C := FiniteFlatCover(f : ProjectiveBase := true);
Q := DefiningPolynomials(C);
```

returns the relative-canonical/Bhargava equations (in Cox coordinates), not the
auxiliary projectivized multiplication-table embedding.  Use
`Embedding := "Algebra"` explicitly if that latter presentation is wanted.

For a quintic in FV order, the i-th Pfaffian has base weight `-f_i`.  Hence the
coefficient of `X[a]*X[b]` in that Pfaffian has ordinary base degree

```text
e_a + e_b - f_i.
```

This is a useful sanity check on the physical coordinate ordering: in a fixed
Pfaffian, coefficient degrees increase with the `e`-indices.  The regression
suite checks this identity term-by-term for the projective quintic example.
