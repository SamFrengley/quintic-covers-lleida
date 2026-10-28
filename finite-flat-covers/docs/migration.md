# Version 12: homogeneous prime-fibre presentation

`BaseChange(C,pi)` still defaults to the full homogeneous fraction field.
For a projective base, this field now uses the actual images of the original
s,t, rather than an affine ratio named s and a separate scaling variable t.
Its Magma type may change from `FldFunRat` over a number field to `FldFun`
over `k(t)`. Always obtain the coordinate images from the returned map phi;
do not infer them by walking a particular coefficient-field tower.

`Homogeneous := false` is unchanged. There are no new attributes or flags.
Native scheme ambients now retain the equation ring's `X[i]` names.
See [the prime-fibre note](prime-fibres.md) for the corrected interpretation of
the reported two components. Restart with only version 12 attached.

# Version 11: one model default

All `FiniteFlatCover` overloads now use `Embedding := "Model"` by default.
For tensors, this changes the previous conservative `"Algebra"` default. Write
`Embedding := "Algebra"` explicitly to retain that presentation. Explicit algebra
constructors and the standard sextic resolvent still use their algebra models.

Do not fix an existing object by assigning ``C`Embedding``: its equations and scheme
may already be cached. Reconstruct with the desired option. A fresh session avoids
mixing attached releases; `FiniteFlatCoverVersion()` must return `"16.0.1"`.

See [presentation diagnostics](presentations.md) for a direct quintic check.

# Migration notes

## From version 8

Automatically graded polynomial input in degrees 3--5 now changes the **actual
model frame** to increasing Frengley--Vemulapalli order. Previously only the
default display of the `e_i` and `f_i` was sorted. Code which depended on the old
quintic matrix order `[e_4,e_3,e_2,e_1]` must now use the returned model directly
or supply explicit model weights to preserve a chosen frame.

`FirstSyzygyInvariants(C)` is now defined formally in all degrees 2--5: it returns
`[]` in degrees 2 and 3, two entries in degree 4, and five in degree 5.

## From version 6

Replace `Base := "proj"` by `ProjectiveBase := true` and `Base := "spec"` by
`ProjectiveBase := false` (or omit it). This applies to all constructor overloads.
Strings and the old parameter are no longer accepted. Actions and fibres keep
using the existing boolean attribute.

Weighted-homogeneous polynomial input now infers its split tensor grading instead
of defaulting to zero. `TschirnhausenInvariants(C)` and
`FirstSyzygyInvariants(C)` expose the e- and f-invariants without computing tables
or syzygies. They are sorted by default; `Sorted := false` gives frame order.
No public attribute was added. See [projective gradings](projective.md).

## From version 5 and earlier

The small-object changes from version 6 remain in force.

| Before | Now |
|---|---|
| Attach the single `src/FiniteFlatCover.m` | `AttachSpec("spec")` |
| `Base := "Spec"` / `"Proj"` | `ProjectiveBase := false` / `true` |
| `BaseKind(C)` / ``C`BaseKind`` | `ProjectiveBase(C)` / ``C`ProjectiveBase``, a boolean |
| ``C`MultiplicationMatrices``, trace-cache attributes | `MultiplicationMatrices(C)`, `TraceVector(C)`, `TracePairing(C)` |
| ``C`ResolutionMaps`` | `ResolutionMaps(C)` |
| ``C`Resolvent``, ``C`BhargavaResolvent`` | `Resolvent(C)` for the standard object |
| ``C`VariableWeights`` | `BundleWeights(C : Embedding := "Model")` |
| ``C`AlgebraWeights`` | `BundleWeights(C : Embedding := "Algebra")` |
| ``C`AlgebraBasisChange`` | `AlgebraBasisChange(C)` |
| Dozens of other implementation attributes | Accessors; inspect cache names with `CachedComputations(C)` |
| `CorrectedSexticResolvent(C)` | `ConjecturalSexticResolvent(C)` |
| `Resolvent(C5)` selected the experimental order | `Resolvent(C5)` selects **Bhargava's standard** order |
| `SexticResolvent(C5)` selected the experimental order | `SexticResolvent(C5)` is standard |
| `Normalization := "Bhargava"` | No mode flag; use `Resolvent` or `BhargavaResolvent` |
| `ResolventCharts(C5)` | `ConjecturalSexticResolventCharts(C5)` |
| Experimental verification implicitly selected | `VerifyResolvent(C5 : Conjectural := true)` |
| `AssumeResolution := true/false` | Removed; run `VerifyResolution(C)` explicitly |

The public `Degree`, `Model`, `CoefficientRing`, `Embedding`, `Twisted`,
`StructureConstants`, `Discriminant`, `DefiningPolynomials`, and
`UnderlyingScheme` attributes remain, and `ProjectiveBase` replaces `BaseKind`.
All are capitalized. `_Data` is implementation-only.

## Important changes in when work happens

`Model(C)` now means exactly that: retrieve the model. Use `ResolutionMaps(C)`
when the higher maps are required. `BundleWeights` no longer constructs equations.
The source constructor no longer runs geometric finiteness or resolution-exactness
checks implicitly. `CheckAlgebra` defaults to false, including for explicit tables.
The relevant mathematical hypotheses still have to hold; they have not been
removed merely because their verification has become explicit.

A transformed object need not have a previously populated cache immediately
assigned. Use its accessor, which performs the pending transformation and stores
the result. This applies to actions and fibres. An already computed discriminant
scalar is the exception: its cheap transformation is retained immediately.

## Experimental orders and fibres

```magma
C := FiniteFlatCover(f);
S := ConjecturalSexticResolvent(C); // explicitly choose the integral family
Cp,phi := BaseChange(C,2);
Sp := ConjecturalSexticResolvent(Cp); // specializes S, preserving the choice
```

The last call is not a fresh saturation. This matters at degenerate fibres.
The separate standard call `Resolvent(Cp)` still means Bhargava's order.

## Indexing fix

All triangular pair enumerations bind the outer index first:

```magma
pairs := &cat[[<i,j> : j in [i..n-2]] : i in [0..n-2]];
```

Both canonical-quadric constructors and the analogous equation-weight list use
nested enumeration. Native tests cover degrees 4 through 7 and both input forms.
