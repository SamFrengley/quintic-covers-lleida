# Quintic presentation diagnostics

## What the reported output was

The pasted list is exactly the package's auxiliary multiplication-table presentation:
**ten quadratic equations in five fibre coordinates**. It is not a sextic or a
Pfaffian model. The first coordinate homogenizes the identity element of the algebra.
The cover still has rank five, so the degree and discriminant comparison are unchanged.

For a monic quintic `f=x^5+a4*x^4+...+a0`, its first equation is

```text
X[2]^2 + X[1]*X[3] - a4*X[1]*X[2] + a3*X[1]^2.
```

`tests/presentation_reference.py` identifies all ten pasted equations coefficient by
coefficient, not just their count. The original output is retained as a fixture.

## Get the relative P^3 model explicitly

```magma
AA := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true,
    Embedding := "Model");
assert AA`Embedding eq "Model";

Q := ModelPolynomials(AA : Cox := false);
assert #Q eq 5;
assert Rank(Parent(Q[1])) eq 4; // R[X[1],...,X[4]]

Qcox := DefiningPolynomials(AA);
assert #Qcox eq 5;
assert Rank(Parent(Qcox[1])) eq 6; // s,t plus four fibre variables
```

Reconstruct the object; do not directly change its `Embedding` attribute after
caching equations or a scheme. `ModelScheme(AA)` always requests the small model,
whereas `UnderlyingScheme(AA)` follows the embedding chosen at construction.

## What changed in version 11

The disk copy of version 10 already selected `"Model"` in its polynomial overloads,
but its tensor overload still defaulted to `"Algebra"`. Its algebra/discriminant
accessors do not assign the embedding. Thus the transcript alone does not establish
why that running session selected the algebra presentation; it is not proof that
`Discriminant` changed the model, nor proof of a Magma overload-resolution bug.

Version 11 removes the remaining inconsistent constructor default. All model
constructors now select `"Model"`. The multiplication-table embedding is an explicit
option. Equation getters reject invalid embedding strings and check the equation
count and coordinate-ring rank before returning either new or cached results.

No multiplication, invariant, Pfaffian, ordering or resolvent formula was changed.

## Check the loaded release and the precise call order

Start a fresh Magma session in the extracted package directory. Attach only this
release, not several historical versions together:

```magma
AttachSpec("spec");
assert FiniteFlatCoverVersion() eq "16.0.1";
```

Magma intrinsics are global, and `AttachSpec` adds their definitions to the session;
it does not create an isolated version namespace. See the official handbook:
https://magma.maths.usyd.edu.au/magma/handbook/text/24#164

The supplied regression uses the reported order, with the explicit degree parameter:

```magma
AA := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true);
assert AA`Embedding eq "Model";
assert Discriminant(AA) eq Discriminant(f);
assert AA`Embedding eq "Model";
Q := DefiningPolynomials(AA);
assert #Q eq 5 and Rank(Parent(Q[1])) eq 6;
```

Run `magma -b tests/v11_only.m` for this sequence, its reverse, homogeneous input,
explicit tensor input, algebra opt-in, cached equations, action and base change.
Over the generic field fibre it also checks ambient dimension three and cover degree five.

These native assertions have **not** been executed in the authoring environment.
Python validates the mathematical formulas and source structure, not Magma dispatch.
