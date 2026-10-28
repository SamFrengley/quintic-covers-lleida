// Native regressions: absence of work is an observable part of the API.
// Loaded by smoke.m and run.m; these tests have not run in the authoring environment.
procedure AssertCold(C)
    assert not assigned C`StructureConstants;
    assert not assigned C`Discriminant;
    assert not assigned C`UnderlyingScheme;
    names := CachedComputations(C);
    for name in ["MultiplicationMatrices", "TraceVector", "TracePairing",
                 "TraceDiscriminant", "ResolutionMaps", "FirstSyzygies",
                 "Resolvent", "ConjecturalSexticResolvent"] do
        assert name notin names;
    end for;
end procedure;

Z := Integers();
U<z> := PolynomialRing(Z);
for n in [2..7] do
    C := FiniteFlatCover(z^n-z-1 : Embedding := "Model");
    AssertCold(C);
    M := Model(C);
    w := BundleWeights(C);
    AssertCold(C);
    Q := DefiningPolynomials(C);
    AssertCold(C); // equations do not need the table or a scheme
    D,phi := BaseChange(C,2);
    AssertCold(D);
end for;

// The reported i-scope failure: exercise both triangular enumerations.
P<x,y> := PolynomialRing(Z,2);
for n in [4..7] do
    f := z^n-z-1;
    Q := CanonicalQuadrics(f);
    assert #Q eq n*(n-3) div 2;
    assert forall{q : q in Q |
        Evaluate(q,[z^j : j in [0..n-2]]) mod f eq 0};
    H := CanonicalQuadrics(x^n-x*y^(n-1)-y^n);
    assert #H eq #Q;
    assert forall{q : q in H |
        Evaluate(q,[z^j : j in [0..n-2]]) mod f eq 0};
end for;

// The algebra table is a dependency only when requested.
C := FiniteFlatCover(z^3-z-1);
AssertCold(C);
T := StructureConstants(C);
assert T eq C`StructureConstants;
assert "TracePairing" notin CachedComputations(C);
assert "MultiplicationMatrices" notin CachedComputations(C);
assert not assigned C`Discriminant;

g := Matrix(Z,2,2,[1,1,0,1]);
D := C^g;
AssertCold(D); // an available source table is a deferred map, not eager work
Fresh := FiniteFlatCover(Model(D));
assert StructureConstants(D) eq StructureConstants(Fresh);
assert StructureConstants(C) eq T;
assert not assigned D`Discriminant;

E,phi := BaseChange(D,2);
AssertCold(E);
assert StructureConstants(E) eq [phi(a) : a in StructureConstants(D)];
assert "TracePairing" notin CachedComputations(E);

// Populated trace caches do not cause eager target trace computations.
H := TracePairing(C);
A := MultiplicationMatrices(C);
D := C^g;
AssertCold(D);
TD := StructureConstants(D);
assert "TracePairing" notin CachedComputations(D);
assert "MultiplicationMatrices" notin CachedComputations(D);
assert TracePairing(D) eq TracePairing(FiniteFlatCover(Model(D)));

// An already evaluated scalar discriminant remains cheap to transport.
d := Discriminant(C);
D := C^g;
assert assigned D`Discriminant and D`Discriminant eq d;
assert not assigned D`StructureConstants;

// Partial higher resolutions stay partial through actions and fibres.
K := Rationals();
V<z> := PolynomialRing(K);
for n in [6,7] do
    C := FiniteFlatCover(z^n-z-1 : Embedding := "Model");
    g := IdentityMatrix(K,n-1);
    g[1,1] := 2;
    g[1,2] := 1;
    D := C^g;
    AssertCold(C);
    AssertCold(D);
    assert #Model(D) eq 1;
    assert DiscriminantMultiplier(C,g) eq K!4;
    AssertCold(C);
    E,phi := GenericFibre(D);
    AssertCold(E);
end for;

// Proj is stored once as a boolean; metadata inspection stays cheap.
R<s,t> := PolynomialRing(Z,2);
P<x,y> := PolynomialRing(R,2);
C := FiniteFlatCover(x^3+s*x^2*y+t^2*x*y^2+s^3*y^3 :
    ProjectiveBase := true, VariableWeights := [0,-1], EquationWeights := [0],
    Embedding := "Model");
assert C`ProjectiveBase and ProjectiveBase(C);
w := BundleWeights(C);
assert w eq [0,-1];
AssertCold(C);
g := Matrix(R,2,2,[1,0,s,1]);
D := C^g;
AssertCold(D);
A,phi := CoverPatch(D,2);
assert not A`ProjectiveBase and phi(t) eq 1;
AssertCold(A);
print "Constructor, scope, base-state and lazy-cache regressions passed.";

// Quartic actions need neither equations nor multiplication tables.
U<z> := PolynomialRing(Integers());
C := FiniteFlatCover(z^4-z-1);
g := IdentityMatrix(Integers(),3);
g[1,2] := 1;
D := C^g;
AssertCold(C);
AssertCold(D);
assert "ModelPolynomials" notin CachedComputations(C);
assert "ModelPolynomials" notin CachedComputations(D);
assert StructureConstants(D) eq StructureConstants(FiniteFlatCover(Model(D)));

// A trace determinant already obtained is reused, without making a resolvent.
C := FiniteFlatCover(z^4-z-1);
d := TraceDiscriminant(C);
assert "Resolvent" notin CachedComputations(C);
assert Discriminant(C) eq d;
assert "Resolvent" notin CachedComputations(C);
