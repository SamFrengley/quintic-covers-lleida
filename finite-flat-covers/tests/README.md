# Version 11 targeted regression

`magma -b tests/v11_only.m` runs the exact reported quintic call sequence.
This native test has not been executed here. It checks the embedding before and
AFTER Discriminant, then checks five Pfaffians, four fibre variables, and six Cox
variables. It also tests the explicit algebra opt-in and a deliberately bad cache.

`python tests/presentation_reference.py` independently identifies all ten pasted
polynomials with the algebra presentation. It checks the five universal Pfaffians
and their restriction to `[x^3:x^2:x:1]` as `[-x*f,-f,0,0,0]`.

`VALIDATION.json` records only checks run for the current release. Existing output
files for omitted suites are historical, not newly passed tests.
`VALIDATION-v10.json` is the inherited prior report.

# Tests

Run native commands from the package directory:

```sh
magma -b tests/smoke.m
magma -b tests/run.m
magma -b tests/benchmark.m
```

`smoke.m` checks loading, both canonical-quadric index loops, constructors,
boolean base state, and lazy action/fibre caches. `run.m` adds algebra, geometry,
grading, oriented resolutions, monogenic quotient-ring comparisons, standard
resolvents, and the opt-in conjectural sextic. The optional integral projective
elimination test is `optional_projective_embedding.m`.

`benchmark.m` prints actual CPU times from the machine running it. It separates
construction, first table calculation, cached access, action, deferred transport,
discriminant, and explicit standard sextic construction. It does not impose a
machine-independent timing threshold.

**Native compilation and native tests have not been run in the authoring
environment.** Assertions in these files are tests to execute, not recorded results.

## Independent tests that were executed

```sh
python -m pip install -r tests/requirements-validation.txt
python tests/validate.py
```

The runner performs eleven independent suites: low-degree arithmetic, action
covariance, geometry formulas, monogenic comparisons in low and high degree,
twisted characters, constructor formulas, integral resolvent formulas, the
experimental sextic arithmetic, the universal direct quadratic-action identity, and source-structure checks. It writes
`VALIDATION.json` with explicit execution status and per-suite results.

`static_audit.py` checks the module graph, private record names, public attributes,
size limits, getter call sites, and all 25,200 permuted minor-label cases. This is
textual inspection, **not** a Magma parser or proof that a native call will succeed.

The two monogenic suites construct actual unimodular basis isomorphisms and
compare every product with an independently reduced polynomial quotient. They
do not merely compare discriminants. The native equivalents reconstruct fresh
covers from the tensors/resolutions, so a polynomial constructor's cache cannot
supply the answer being tested.

`corrected_resolvent_reference.py` retains its historical filename for the
independent experimental arithmetic. Its production API is now exclusively
`ConjecturalSexticResolvent` and is not the default.
