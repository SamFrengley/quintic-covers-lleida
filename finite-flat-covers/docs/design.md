# Implementation map

Every Magma source file is at most 500 lines. Algorithms and numerical formula
data are separate; `spec` lists dependencies in attachment order. Each ordinary
helper imports its actual dependencies. Public intrinsics provide the cross-module
API. There is no monolithic loader containing the algorithms.

| Directory | Responsibility |
|---|---|
| `src/core` | Type, private records, arithmetic, coefficient maps, grading |
| `src/constructors` | Input validation and cheap model construction |
| `src/models` | Binary/tensor conversion and low-degree multiplication |
| `src/algebra` | Tables, trace data, discriminants, lazy basis transport |
| `src/geometry` | Equation getters, chart simplification, native scheme backends |
| `src/resolution` | Kernels, resolution format, syzygies, FR contractions |
| `src/actions` | Characters, operators, tensor and resolution actions |
| `src/base_change` | Coefficient maps, primes, projective charts |
| `src/resolvents` | Standard resolvents and deferred transport |
| `src/experimental` | The conjectural sextic, lift/envelope backends, atlas |
| `src/data` | Generated seed constants and labels, not algorithms |

The projective polynomial regression is handled by
`src/constructors/polynomial_weights.m`: it infers coefficient degrees before
tensor conversion. `src/core/bundles.m` translates the stored model grading into
the e- and f-invariants, including common-twist corrections.

## Object ownership

Ten public attributes expose identity/configuration and the four most important
computed results. One private record `_Data` groups presentation metadata, bundle
data, algebra caches, geometry caches, resolution caches, and resolvent caches.
No public code should navigate it. Tests may inspect it to establish that a
computation did **not** run.

A helper that creates an object uses `FFCNewCover`, which initializes empty
records only. Constructors set identity and model data. Never add a trace,
scheme, resolution, or resolvent computation to that factory.

## Cost boundaries

| Request | Work it is allowed to trigger |
|---|---|
| Constructor, ordinary default | Shape/grading checks and input model conversion |
| `Model`, `Degree`, `BaseRing`, `CachedComputations` | Inspection only |
| `BundleWeights`, `TschirnhausenInvariants`, `FirstSyzygyInvariants` | Integer arithmetic on stored split degrees only |
| `ModelPolynomials` | Tensor-to-equation conversion, once |
| `StructureConstants` | The selected algebra reconstruction or pending table map |
| `MultiplicationMatrices`, trace getters | Their own data, using cached tables |
| `Discriminant` | Discriminant route, explicitly requested |
| `FirstSyzygies` | The next required map, not the full resolution when avoidable |
| `ResolutionMaps` | Completion of the full resolution |
| `UnderlyingScheme` | Equations plus the selected native scheme backend |
| `Resolvent` | Standard resolvent; no experimental enlargement |
| `ConjecturalSexticResolvent` | Experimental trace/lattice/lift operations |

For a higher-degree binary form, explicit canonical quadrics are part of input
conversion; computing their syzygies is not. The arithmetic primitive-form test
is deliberately only a cheap sufficient test: unit coefficients or integral gcd.
There is no polynomial ideal-membership computation during default construction.

## Deferred transport

A tensor action records a source object and a basis-map recipe when derived
algebra data already exists. Base change similarly records its coefficient map.
The relevant getter materializes the result, caches it, and discards the recipe.
Partial-resolution actions transform the first equations without completing
higher maps. Their eventual completion preserves the source resolution's
orientation rather than choosing an unrelated new one.

A pending experimental fibre retains the already chosen order. Do not replace
this recipe with fresh characteristic-two reconstruction: saturation and
specialization are different operations on degenerate families.

Explicit-table models necessarily transform their table when acted upon or
specialized, because the table is their defining model rather than a derived cache.

Quartic actions transform coefficient tables directly, without dividing by two
or constructing a fibre polynomial ring. This is checked against the universal
quadratic substitution identity, including characteristic two by integrality.

## Formula data

The sextic arithmetic uses four integral seed polynomials in 210 minors.
`src/data/seed_*.m` contains tuples `<coefficient,minor1,minor2,minor3>` with
one-based minor labels. `src/resolvents/minors.m` evaluates them. It caches
permuted minor lists and uses arithmetic ranks rather than repeatedly searching
through all labels.

Regenerate the formulas from the offline derivation:

```sh
python tools/build_resolvent_formulas.py
```

Or rewrite the data modules from the checked fixture alone:

```sh
python tools/write_resolvent_data.py
```

The offline reference programs use zero-based JSON labels. The emitter converts
these to one-based Magma labels. The arithmetic tests check the complete tuples
against an independent rederivation, not just their count.

## Validation boundaries

`tests/static_audit.py` checks module size, imports, declared fields, entrypoints,
index rankings, and explicit expensive-call locations. It is not a Magma parser.
`tests/validate.py` runs independent exact-arithmetic computations. Native tests
and the benchmark must still be run in an actual Magma installation. Neither
source text checks nor Python timing establishes Magma compilation or speed.
