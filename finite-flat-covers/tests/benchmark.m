// Run from the package directory. These are measured native timings, not estimates.
AttachSpec("spec");
R<t> := PolynomialRing(Integers());
P<z> := PolynomialRing(R);
f := z^5+t*z^4+(t^2+1)*z+1;

start := Cputime();
for i in [1..100] do
    C := FiniteFlatCover(f);
end for;
printf "100 default constructors: %o CPU seconds\n", Cputime(start);
assert not assigned C`StructureConstants and not assigned C`Discriminant;

start := Cputime();
M := Model(C);
printf "Model: %o CPU seconds\n", Cputime(start);
assert not assigned C`StructureConstants;

start := Cputime();
Q := ModelPolynomials(C);
printf "ModelPolynomials, first: %o CPU seconds\n", Cputime(start);
start := Cputime();
Q := ModelPolynomials(C);
printf "ModelPolynomials, cached: %o CPU seconds\n", Cputime(start);

start := Cputime();
T := StructureConstants(C);
printf "StructureConstants, first: %o CPU seconds\n", Cputime(start);
start := Cputime();
for i in [1..1000] do
    T := StructureConstants(C);
end for;
printf "1000 cached table accesses: %o CPU seconds\n", Cputime(start);
assert not assigned C`Discriminant;

g := IdentityMatrix(R,5);
g[1,2] := 1;
start := Cputime();
D := C^g;
printf "Tensor action (table deferred): %o CPU seconds\n", Cputime(start);
assert not assigned D`StructureConstants and not assigned D`Discriminant;
start := Cputime();
TD := StructureConstants(D);
printf "Deferred table transport: %o CPU seconds\n", Cputime(start);

start := Cputime();
d := Discriminant(C);
printf "Discriminant, first: %o CPU seconds\n", Cputime(start);
start := Cputime();
d := Discriminant(C);
printf "Discriminant, cached: %o CPU seconds\n", Cputime(start);

// The standard sextic is an explicit, separate cost centre.
start := Cputime();
S := Resolvent(C);
printf "Standard sextic, first: %o CPU seconds\n", Cputime(start);
start := Cputime();
S := Resolvent(C);
printf "Standard sextic, cached: %o CPU seconds\n", Cputime(start);
print CachedComputations(C);
quit;
