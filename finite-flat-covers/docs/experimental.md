# ConjecturalSexticResolvent

This is the experimental trace-halving construction inherited from version 5,
now explicitly named and isolated. It is **not** Bhargava's standard sextic and
is not selected by `Resolvent`, `SexticResolvent`, or `Discriminant`.
The name deliberately does not assert a general characteristic-two extension or
a solution of an integral-realization conjecture.

## Use

```magma
C := FiniteFlatCover(f);           // retain the quintic tensor
B := Resolvent(C);                // standard historical order
S := ConjecturalSexticResolvent(C);
S := ConjecturalSexticResolvent(C : Check := true);
inclusion,factor,description := Explode(ConjecturalResolventCertificate(S));

assert VerifyResolvent(C : Conjectural := true);
assert VerifyResolvent(C : Conjectural := true, CheckDiscriminant := true);
```

The certificate records the historical-order inclusion, the factor in the stored
unevaluated discriminant recipe, and a description of the operation. It does not
constitute a proof of a universal moduli interpretation. The two objects are
cached separately. Asking for either does not evaluate a discriminant.

## Construction retained

Over a mixed-characteristic integral base, start with the historical sextic B,
form half-trace generators `(b - Tr(b)/2)/2` in `B[1/2]`, and compute the retained
integral envelope. The implementation checks the necessary divisibilities,
the rank-one defect condition, integrality of the returned table, and the
inclusion. Over one-variable polynomial bases it uses the previously implemented
reflexive-hull step; that is a distinct operation from unqualified ring closure.
When 2 is invertible it returns the same algebra in a renormalized basis.

Fresh characteristic-two construction lifts the original **quintic tensor**,
performs the integral operation, then reduces. That backend requires etale input
and checks the output trace-pairing rank. These are not hidden discriminant calls,
but they are genuine computations intrinsic to this requested experimental task.

The standard sextic's discriminant factor is 4096. The experimental factor is
recorded from the actual basis change; it is not unconditionally overwritten by 1.
The retained tests include split, nilpotent, monogenic, symbolic-family, and
finite-field examples, but do not establish general correctness for all bases.

## Fibres and limitations

```magma
S := ConjecturalSexticResolvent(C);
Cp,phi := BaseChange(C,2);
Sp := ConjecturalSexticResolvent(Cp);
```

This specializes the chosen family S, on demand. A fresh construction from only
the reduced tensor can be a different operation at degenerate fibres. Fresh
characteristic-two reconstruction there is rejected; use the family route.
Cached experimental action reconstruction in characteristic two likewise has
the inherited etaleness restriction.

A global Proj result is returned only when a compatible split frame can be
checked. Otherwise request the two affine-base charts explicitly:

```magma
S1,S2,transition := Explode(ConjecturalSexticResolventCharts(C));
```

The transition and its inverse are checked on the overlap. Native gluing of this
atlas to a global scheme is not implemented. This release is a refactor of the
experimental arithmetic, not a new proof or broader mathematical generalization.
