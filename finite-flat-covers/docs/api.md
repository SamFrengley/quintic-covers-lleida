# API

Load once with `AttachSpec("spec")`. The public constructor is `FiniteFlatCover`;
its Magma dispatch type is `FinFlatCov`.

## Object and caching

The ten public attributes are:

| Always available | Assigned by their computation |
|---|---|
| `Degree`, `Model`, `CoefficientRing` | `StructureConstants` |
| `ProjectiveBase`, `Embedding`, `Twisted` | `Discriminant` |
| | `DefiningPolynomials`, `UnderlyingScheme` |

Use `FiniteFlatCoverVersion()` to identify the loaded implementation.
Use `Degree(C)`, `Model(C)`, `BaseRing(C)`, `ProjectiveBase(C)`, and `IsTwisted(C)`
for inexpensive inspection. The last four attributes have same-named accessors.
A backtick read does not calculate an unassigned value.

All other caches live in one implementation attribute `_Data`, divided by
responsibility. It is not a public API: use accessors, not record-field paths.
Treat every public attribute as read-only. Use `ActBy` and `BaseChange` to obtain
consistent transformed objects.

```magma
CachedComputations(C);             // sorted names, no calculations
assigned C`Discriminant;           // no calculation
T := StructureConstants(C);        // calculate/cache on first call
T := StructureConstants(C);        // return the cached value
```

Pending action/base-change recipes are not reported as completed computations.

## `Model(C)`

`Model(C)` is a constant-time accessor: it returns the model already stored on the cover and
never computes structure constants, equations, a discriminant, a resolution, or geometry.
For covers created from the Bhargava/Wood representations its return value is:

| degree | `Model(C)` |
|---:|---|
| 2 | homogeneous binary quadratic |
| 3 | homogeneous binary cubic |
| 4 | pair of `3 x 3` symmetric coefficient matrices |
| 5 | quadruple of `5 x 5` alternating matrices |

Thus a univariate polynomial input is homogenized first, and `Model(C)` returns that binary
form in the package coordinate ring `P<[X]>`.  For degree 4 and 5 polynomial input, it returns
the actual ordered matrix model used by the cover (including the FV ordering on a projective
base).  Explicit structure-constant input has no canonically determined Bhargava tensor, so
`Model(C)` returns the supplied multiplication table in that case. Higher-degree resolution
input returns the supplied resolution data; `ResolutionMaps(C)` is the accessor that may
complete it.

## Constructors

```magma
C := FiniteFlatCover(f);           // univariate or homogeneous binary f
C := FiniteFlatCover([A,B]);       // quartic coefficient matrices or ternary quadrics
C := FiniteFlatCover([A1,A2,A3,A4]); // quintic alternating matrices
C := FiniteFlatCover([* Phi1,...,PhiLast *]); // complete oriented resolution
C := FiniteFlatCoverFromQuadrics(Q);
C := FiniteFlatCoverFromStructureConstants(T,n);
C := IdentityFiniteFlatCover(R);
```

Common options are `ProjectiveBase := false`, `Twisted := true`, and
`CheckAlgebra := false`. Polynomial, tensor and resolution constructors all default to
`Embedding := "Model"`. For quintics, this is five Pfaffians in four fibre coordinates.
Use `Embedding := "Algebra"` explicitly for multiplication-table equations, especially
when a degenerate tensor's small zero locus is not finite. The explicit-table constructor
`FiniteFlatCoverFromStructureConstants` necessarily uses the algebra embedding.
`AssumeFiniteFlat := true` records a hypothesis; it is
not a certificate and does not invoke a checker. Shape, parent, and coefficient
grading checks always run.

`CoverDegree := n` disambiguates zero forms and homogenizes a univariate
polynomial to degree n. It must not be smaller than its actual degree.

Quartic matrix options: `ModelConvention := "Coefficients"` (default),
`"Hessian"`, or `"Gram"`. A coefficient table means
`sum_{i<=j} A[i,j] x_i x_j`; a Gram matrix means `x^T A x`.
Convert a Hessian over the integral ring **before** reducing modulo 2.

For `ProjectiveBase := true`, the supported homogeneous base ring is `k[s,t]` or
`Z[s,t]` with its standard grading. The specified bundles are split.
Use `VariableWeights`, `EquationWeights`; for quintics also `RowWeights`
and `MatrixTwist`; for complete resolutions `ResolutionWeights`; for table
input `AlgebraWeights`. The grading is `deg(s)=deg(t)=(1,0)`,
`deg(x_i)=(w_i,1)`. Polynomial input infers weights from the homogeneous
coefficient-degree progression when no explicit model grading is supplied.
Raw matrices still need their split weights specified. The old `Base` option
is removed. The library does not assume every vector bundle on `P^1_Z` is split.

## Splitting invariants on a projective base

```magma
e := TschirnhausenInvariants(C);        // E = direct sum O(e_i)
f := FirstSyzygyInvariants(C);          // quadratic-generator bundle F
// Read the actual frame orders:
e := TschirnhausenInvariants(C : Sorted := false);
f := FirstSyzygyInvariants(C : Sorted := false);
```

Sorted increasingly by default, cached privately, and no algebra/geometry is
computed. For automatically graded **polynomial** input in degrees 3--5 the
model itself is put into Frengley--Vemulapalli order, so `Sorted := false` is
already increasing. In degree 4 both quadratic generators are reordered; in
degree 5 both the four `E` coordinates and the five `F` rows/columns are
reordered. Thus a nonzero quintic entry satisfies
`deg(A[k][i,j])=f_i+f_j+e_k-sum(e)` literally with increasing indices.

`FirstSyzygyInvariants` returns `[]` in degrees 2 and 3, the two quadratic
generator degrees in degree 4, and the five FV degrees in degree 5. These are
invariants of the supplied split cover, not of its normalization. Both accessors
require a projective base. See [the grading reference](projective.md) for
automatic inference, manual weights, common twists, and the reported quintic.

## Algebra

```magma
T := StructureConstants(C);       // flat length n^3 table
L := MultiplicationMatrices(C);
v := TraceVector(C);
H := TracePairing(C);
d := Discriminant(C);
direct := TraceDiscriminant(C);   // determinant of the trace pairing
B := AlgebraBasisChange(D);       // when D records an algebra-frame change
```

The unit is basis element 0. With `0 <= i,j,k < n`,
`T[(i*n+j)*n+k+1]` is the coefficient of `e_k` in `e_i e_j`.
Multiplication matrices act on coordinate **columns**. Rows of an algebra
basis-change matrix give new basis elements in the old basis.

Trace data, multiplication matrices, and associativity are separate caches.
Requesting a table does not also compute a trace pairing or discriminant.
`Discriminant` may use a standard resolvent in degrees 3 and 4; a quintic
uses its trace pairing, not an automatically built sextic.

## Geometry and higher resolutions

```magma
Q := ModelPolynomials(C);         // small tensor/canonical equations
Y := ModelScheme(C);              // their zero locus, possibly not finite
Q := DefiningPolynomials(C);      // equations for C's selected embedding
X := UnderlyingScheme(C);
V := AmbientBundle(C);
w := BundleWeights(C);
P,Q,grading,irrelevant := CoxData(C); // Proj bases only
F := ResolutionMaps(C);           // all higher maps, cached
S := FirstSyzygies(C);            // Phi_2 only where possible
b := BettiNumbers(C);             // expected pure resolution ranks
q,dehom,U := LocalDefiningPolynomials(C,i);
```

`Model(C)` never completes F. For an incomplete model, requesting `F` or the
Fisher–Radicevic multiplication table can require polynomial-module kernels.
Even on a partial **projective** canonical resolution, the bundle weights and
splitting accessors use the recorded generator degrees; they do not compute
its top map. This uses, but does not verify, the canonical-resolution hypothesis.

Local equation simplification uses unit coefficients of first syzygies.
It returns `original_equations = U * retained_equations` on the selected fibre
chart. For a Proj base, take a base chart with `CoverPatch` first.

The algebra embedding uses `z_i z_j = c_ij^0 z_0^2 + sum c_ij^k z_0 z_k`.
The small-model embedding uses the binary form, two quadrics, five Pfaffians,
or the first resolution map. These are not interchangeable for degenerate data.

## Actions

```magma
D := ActBy(C,g);        D := C^g;
D := ActBy(C,g,h);      D := C^<g,h>;
ActBy(~C,g);           ActBy(~C,g,h);
D := ActBy(C,g,h : Twisted := false);
chi := DiscriminantMultiplier(C,g,h);
```

The stored default is determinant-twisted. Action matrices may have entries in either the
coefficient ring `R` or `FieldOfFractions(R)`. They must be invertible over the fraction field.
On a projective base, entries need only be homogeneous rational functions; the action is allowed
to **change the split bundle weights**. The target weight of each row is inferred from the degrees
of its nonzero entries. For a coordinate (dual) action, `deg(g_ij)+w_new[i]=w_old[j]`; for a
direct frame action, `deg(g_ij)+w_old[j]=w_new[i]`. A row whose nonzero entries imply inconsistent
target weights is rejected.

The action is formed over the fraction field and returned **only if every transformed model
coefficient descends exactly to `R`**. The result is then rebuilt using the inferred target weights,
which is the final bihomogeneity check. Thus matrices such as `DiagonalMatrix(K,[1/s,1/s])` are
allowed when their denominators cancel in the transformed model; they simply change the splitting
type. An integral but non-unimodular matrix is likewise permitted when its transformed model is
integral. This can change the integral model/order, so cached algebra and resolvent data are
transported only when the induced basis change is an actual integral automorphism; otherwise they
are recomputed lazily if requested.

For example, with `R<s,t> := PolynomialRing(QQ,2)` and
`F := s*(X^3+X^2*Y+X*Y^2+Y^3)`, the twisted action by
`DiagonalMatrix(FieldOfFractions(R),[1/s,1/s])` returns the constant binary cubic. Its
Tschirnhausen splitting changes from `[1,1]` to `[0,0]`; no separate target-weight option is
needed.

Conventions use variable substitution `g^T x` and quintic congruence `g A g^T`.
Quartic arguments are `(g3,h2)`; quintic arguments are `(g5,h4)`.

| Model | Twisted tensor action | Determinant constraint |
|---|---|---|
| Binary degree 2 or 3 | `f(g^T x)/det(g)` | None beyond invertibility |
| Quartic | `sum_b h_ab q_b(g^T x)/det(h)` | `det(g3)=det(h2)` |
| Quintic | `sum_b h_ab g5 A_b g5^T/det(h4)` | `det(g5)=det(h4)^2` |

`Twisted := false` removes the tensor scalar and the last two constraints.
Omitting one factor supplies its identity; it does not bypass the constraint.
These are left actions: `(C^g)^h = C^(h*g)`.

For a full resolution, use `ActBy(C,g,[* B1,...,BLast *])`. The maps transform
as `B_(i-1)^(-1) Phi_i(g^T x) B_i`, with `B_0=1`; the twisted convention also
multiplies the final map by `det(g)^(-1)`. A two-matrix resolution action changes
only the equation-generator frame and its compensating next frame.

A tensor action transforms the model immediately, but does not materialize
existing table/resolvent caches in the new coordinates until requested.
An already known discriminant scalar is transported immediately by its character.
No action computes a missing discriminant. If a discriminant was already cached, its generic
character value is required to descend to `R` before being cached on the result. Acting on an explicit-table model
must transform its table because that table **is** the model.

## Base change and fibres

```magma
D,phi := BaseChange(C,p);          // rational prime: use the fraction field
D,phi := BaseChange(C,p : ToField := false); // retain the vertical family
D,phi := BaseChange(C,pi);         // primitive irreducible polynomial prime
D,phi := BaseChange(C,pi : Homogeneous := false);
D,phi := BaseChange(C,K,[a,b]);    // fibre over a Proj point [a:b]
D,phi := BaseChange(C,phi);        // explicit coefficient homomorphism
A,phi := CoverPatch(C,2);         // t=1, s remains a parameter
A,phi := CoverPatch(C,1);         // s=1
D,phi := GenericFibre(C);
```

For `Z[t]`, the default vertical field is `GF(p)(t)`; for `Z[s,t]`, it is
`GF(p)(s,t)`. On Proj, `Homogeneous := false` instead uses a chart residue field,
removing the extra homogeneous scaling variable. Horizontal Proj primes use a
field isomorphic to `Frac(QQ[s,t]/pi)` by default. Integral horizontal Proj
quotient geometry is not implemented.

An explicit coefficient map defaults to an affine target. Set
`PreserveGrading := true` only for a homogeneous map of projective base rings.
It is a change of base, not a second request to describe the existing base.

The input model is specialized immediately. Existing derived caches are
specialized on demand. A chosen conjectural order is specialized as chosen,
not replaced by a fresh saturation of a degenerate fibre.

## Resolvents

```magma
D := Resolvent(C);                // standard: 3->2, 4->3, 5->6
D := QuadraticResolvent(C3);
D := CubicResolvent(C4);
D := SexticResolvent(C5);          // same as BhargavaResolvent(C5)
S := ConjecturalSexticResolvent(C5); // explicitly experimental
ok := VerifyResolvent(C);
ok := VerifyResolvent(C : CheckDiscriminant := true);
ok := VerifyResolvent(C : Conjectural := true);
```

All return ordinary covers and are cached. `Resolvent(C : Check := true)` and
`ConjecturalSexticResolvent(C : Check := true)` request the algebra consistency
checks, not discriminants. Standard and conjectural sextics have separate caches.
The standard sextic uses the historical normalization
`disc(S) = 4096*disc(C)^3`. No experimental normalization is selected implicitly.
Quartic/quintic input must retain the tensor determining the resolvent choice.

## Verification and hypotheses

`CheckAlgebra := true` asks for associativity and available grading checks.
It can compute a full resolution for higher-degree input. It is off by default.
`VerifyResolution(C)` checks adjacent compositions and exactness, including the
last kernel; it can be expensive. `StructureConstants` does not silently run it.
`IsModelFiniteFlat(C)` is a dimension-and-degree check over a **field**. Over a
nonfield it returns a recorded flatness assertion/certificate; it is not a global
arithmetic flatness decision procedure. With no recorded result it raises an
error over those bases. Do not use an assumed value as a proof.
A constructor returning successfully is not such a proof either.


## Naming conventions

All fibre polynomial rings created by the package use the Magma convention
`P<[X]> := PolynomialRing(R,n)`, hence their generators print as `X[1],...,X[n]`.
A base change copies the names of the source base coordinates whenever those coordinates
survive. Thus `R<s,t>` reduces to a polynomial/function-field base with generators named
`s,t`. On the standard projective charts, chart 1 (`s=1`) uses the affine coordinate `t`,
and chart 2 (`t=1`) uses `s`.

Homogeneous polynomial-prime base changes retain the original s,t in the field
`k(t)[s]/(pi(s,t))` (with separate coordinate-prime handling). The returned field
may therefore be `FldFun`; do not assume it is rational over a number field.
The option `Homogeneous := false` still takes the actual degree-zero Proj residue
field. See [prime-fibre conventions and the worked example](prime-fibres.md).
Native ambient schemes, not just the equation rings, retain the `X[i]` names.
