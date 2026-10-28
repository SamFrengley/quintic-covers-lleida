# FiniteFlatCover — Magma

Finite locally free algebras and their projective presentations: binary forms,
quartic/quintic Bhargava tensors, and higher-degree resolution models.

**Start here.** The package has a small public object, lazy computations, and
separate modules for algebra, geometry, actions, fibres, and resolvents.
The experimental sextic is **never** the default.

## Load and use

Run Magma from this directory, or give `AttachSpec` the full path to `spec`.
Do not attach individual implementation files.

```magma
AttachSpec("spec");
assert FiniteFlatCoverVersion() eq "16.0.1";
Z := Integers();
P<z> := PolynomialRing(Z);
C := FiniteFlatCover(z^5-z-1);

assert not C`ProjectiveBase;
assert not assigned C`StructureConstants;
assert not assigned C`Discriminant;

T := StructureConstants(C);   // computed once
assert T eq C`StructureConstants;
Q := DefiningPolynomials(C);  // uses the chosen presentation
X := UnderlyingScheme(C);     // geometry is constructed only here
D := Discriminant(C);         // first discriminant calculation
```

For monic input, the algebra is isomorphic to `Z[z]/(f)`. For nonmonic input,
this means the associated binary-form algebra, not the generally non-finite
naive polynomial quotient. Homogeneous binary input is also accepted.

`Model(C)` is deliberately cheap. For degrees 2 and 3 it returns the homogeneous binary
form; for degree 4 it returns the pair of `3 x 3` symmetric matrices; for degree 5 it returns
the four `5 x 5` alternating matrices. It never triggers algebra, geometry, resolution, or
discriminant computations.

## The base is set once

```magma
R<s,t> := PolynomialRing(Integers(),2);
P<x,y> := PolynomialRing(R,2);
C := FiniteFlatCover(x^3+s*x^2*y+t^2*x*y^2+s^3*y^3 :
    ProjectiveBase := true, Embedding := "Model");

assert C`ProjectiveBase;
Q := DefiningPolynomials(C);  // automatically uses the base's bigrading
D,phi := BaseChange(C,2);     // coefficient field GF(2)(s,t)
A,psi := CoverPatch(C,2);     // integral chart t=1
```

`ProjectiveBase := false` is the default. The old `Base` option is removed.
For polynomial input, the constructor infers the split grading from homogeneous
coefficient degrees. Explicit model weights remain available.

### Polynomial-prime fibres

For a homogeneous prime, the default field presentation now keeps the **actual**
base coordinates. For example, `BaseChange(C,3*s^2+14*s*t-t^2)` uses
`QQ(t)[s]/(3*s^2+14*s*t-t^2)`, not a ratio `s/t` secretly printed as s.
Use `Homogeneous := false` to work in the smaller Proj residue field with `t=1`.
See [prime fibres](docs/prime-fibres.md) for the exact reported quintic, its two
non-smooth fibre points, and the distinction from singularities of the total curve.

### Stable names

Fibre coordinate rings are created with `P<[X]>`, so model/defining equations use
`X[1], X[2], ...`. Base changes retain the names on the base you supplied. For example,
if the source is `R<s,t>`, reduction modulo `p` uses `GF(p)[s,t]` or `GF(p)(s,t)`,
not anonymous generators. On projective charts, `s=1` leaves a coordinate named `t`,
and `t=1` leaves one named `s`.

```magma
P<x> := PolynomialRing(R);
C := FiniteFlatCover(x^5+s*x^4+t^5 : ProjectiveBase := true);
e := TschirnhausenInvariants(C); // [1,2,3,4]
f := FirstSyzygyInvariants(C);   // [2,3,4,5,6]
```

The invariant accessors only read bundle degrees; they do not compute a table,
discriminant, or syzygies. For automatically graded polynomial input in degrees
3--5, the **actual model frame** is put into Frengley--Vemulapalli order: both
`e_i` and (when present) `f_i` increase left to right. Thus `Sorted := false`
already returns an increasing list. In degrees 2 and 3 the quadratic-generator
bundle is empty, so `FirstSyzygyInvariants(C)` returns `[]`. See
[projective gradings](docs/projective.md) for the degree 2--5 conventions and the
full reported quintic in [the runnable example](examples/projective_quintic.m).

## Actions and resolvents

```magma
P<z> := PolynomialRing(Integers());
C := FiniteFlatCover(z^5-z-1);
g := IdentityMatrix(Integers(),5);
g[1,2] := 1;
D := C^g;                   // determinant-twisted convention
ActBy(~C,g);                // replace C in place

B := Resolvent(C);          // Bhargava's STANDARD integral sextic
S := ConjecturalSexticResolvent(C); // explicit experimental alternative
```

`Resolvent` sends degrees 3 → 2, 4 → 3, 5 → 6 and returns a cover.
The named quadratic/cubic/sextic accessors are aliases. `Twisted := false`
selects the untwisted action. See [API](docs/api.md) for determinant constraints.

## Avoid accidental expensive work

`CachedComputations(C)` lists results already available; it computes nothing.
`Model(C)` returns the supplied model, even when its resolution is incomplete.
`ResolutionMaps(C)` explicitly completes a resolution. `CheckAlgebra := true`
explicitly asks a constructor to perform the algebra check; the default is false.

Construction checks shapes and grading, **not** global flatness or resolution
exactness. Use `IsModelFiniteFlat` over a field and `VerifyResolution` explicitly.
The small zero locus of a degenerate tensor need not be finite; the default `"Model"` embedding can therefore have a non-finite zero locus.
Use `Embedding := "Algebra"` explicitly for the finite-algebra presentation.
See [the API's verification section](docs/api.md#verification-and-hypotheses).

## Documentation

- [API and cost boundaries](docs/api.md): constructors, algebra, geometry, actions, fibres.
- [Migration from versions 5 and 6](docs/migration.md): renamed calls and removed attributes.
- [Conjectural sextic](docs/experimental.md): explicit opt-in and limitations.
- [Implementation map](docs/design.md): where to change each part of the package.

Runnable examples are in `examples/`. These are source examples, not recorded
Magma execution transcripts.

## Tests and execution status

```sh
magma -b tests/v12_only.m   # exact reported call order, ambient counts and caches
magma -b tests/smoke.m      # loading, constructors, scope fix, lazy caches
magma -b tests/run.m        # full native regression suite
magma -b tests/benchmark.m  # measured first-call and cache timings on your machine
python tests/validate.py   # independent arithmetic and structural checks
```

**Native Magma compilation and execution have not been performed in the authoring
environment.** Python arithmetic tests and source audits are not a substitute.
The exact executed checks are recorded in `tests/VALIDATION.json`.

### FV-ordered projective polynomial models

For polynomial, tensor and resolution input, the embedding defaults to the small model:

```magma
C := FiniteFlatCover(f : ProjectiveBase := true);
assert C`Embedding eq "Model";
```

Thus `DefiningPolynomials(C)`/`UnderlyingScheme(C)` use the FV-ordered
relative-canonical equations.  Request `Embedding := "Algebra"` only when the
multiplication-table projective embedding is wanted.

### Quintic dimensions and package loading

A quintic model has **five Pfaffians in four fibre variables**. For a Proj base
`R<s,t>`, its flattened Cox ring has six generators: `s,t,X[1],...,X[4]`.
The optional `"Algebra"` presentation instead has ten equations in five fibre
variables. Cover degree is algebra rank, not ambient projective dimension.

See [presentation diagnostics](docs/presentations.md) for the reported output,
the explicit workaround, and the discriminant-before-equations regression.
When changing releases, start a fresh Magma session with only this `spec` attached.

## Fraction-field actions

`ActBy` and the `^` operator accept matrices over `R` or `FieldOfFractions(R)`. The transformed
model is formed generically and then descended coefficient-by-coefficient to `R`. On a projective
base, homogeneous generic matrices may change the split bundle weights; the target weights are
inferred from the matrix-entry degrees. Failure of integral descent, nonhomogeneous entries, or an
inconsistent target grading raises an error. See `docs/api.md` and
`tests/fractional_actions.m`.
