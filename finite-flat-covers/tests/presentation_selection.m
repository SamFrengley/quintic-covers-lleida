// Regression for the reported sequence: constructor, discriminant, equations.
// Run via v11_only.m or run.m. This file contains assertions, not a transcript.

function ExpectedQuinticPfaffians(f,P)
    a := [Coefficient(f,i) : i in [0..4]];
    x1,x2,x3,x4 := Explode([P.i : i in [1..4]]);
    return [
        -x1^2-a[5]*x1*x2-a[3]*x1*x4-a[4]*x2^2-a[2]*x2*x4-a[1]*x3*x4,
        -x1*x2-a[4]*x1*x4-a[5]*x2^2-a[3]*x2*x4-a[2]*x3*x4-a[1]*x4^2,
        -x1*x3+x2^2,
        -x1*x4+x2*x3,
        -x2*x4+x3^2
    ];
end function;

procedure CheckQuinticPresentation(C,f)
    assert C`Embedding eq "Model";
    assert Degree(C) eq 5;
    assert TschirnhausenInvariants(C : Sorted := false) eq [1,2,3,4];
    assert FirstSyzygyInvariants(C : Sorted := false) eq [2,3,4,5,6];
    Q := ModelPolynomials(C : Cox := false);
    P4 := Parent(Q[1]);
    assert #Q eq 5 and Rank(P4) eq 4;
    assert Q eq ExpectedQuinticPfaffians(f,P4);
    assert [Sprint(Name(P4,i)) : i in [1..4]] eq
        [Sprintf("X[%o]",i) : i in [1..4]];

    // The Cox ring has two BASE coordinates and four FIBRE coordinates.
    Qcox := DefiningPolynomials(C);
    PC := Parent(Qcox[1]);
    assert #Qcox eq 5 and Rank(PC) eq 6;
    assert [Sprint(Name(PC,i)) : i in [1..6]] eq
        ["s","t"] cat [Sprintf("X[%o]",i) : i in [1..4]];
    assert Qcox eq ModelPolynomials(C);
end procedure;

assert FiniteFlatCoverVersion() eq "16.0.1";
ZZ := Integers();
R<s,t> := PolynomialRing(ZZ,2);
P<x> := PolynomialRing(R);
f := x^5 - 2*(9*t - 128*s)*x^4 + (9*t - 128*s)*(17*t - 54*s)*x^3
     - 18*(5*t + 4*s)*(9*t - 128*s)^2*x^2
     - 27*(33*t^2 - 488*t*s - 60*s^2)*(9*t - 128*s)^2*x
     - 27*(27*t^2 - 92*t*s - 3*s^2)*(9*t - 128*s)^3;

// The exact reported path, including explicit CoverDegree and discriminant FIRST.
AA := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true);
assert AA`Embedding eq "Model";
assert not assigned AA`DefiningPolynomials;
assert not assigned AA`StructureConstants;
assert not assigned AA`Discriminant;
M := Model(AA);
d := Discriminant(AA);
assert d eq Discriminant(f);
assert AA`Embedding eq "Model" and Model(AA) eq M;
assert not assigned AA`DefiningPolynomials;
CheckQuinticPresentation(AA,f);
Q := DefiningPolynomials(AA);
assert Discriminant(AA) eq d and DefiningPolynomials(AA) eq Q;

// Reverse the call order: equations alone must not ask for a table or discriminant.
C := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true);
CheckQuinticPresentation(C,f);
assert not assigned C`StructureConstants and not assigned C`Discriminant;
Q := DefiningPolynomials(C);
assert Discriminant(C) eq d;
assert DefiningPolynomials(C) eq Q and C`Embedding eq "Model";

// Homogeneous-binary input, including the explicit degree override.
B<u,v> := PolynomialRing(R,2);
fhom := &+[Coefficient(f,i)*u^i*v^(5-i) : i in [0..5]];
CB := FiniteFlatCover(fhom : CoverDegree := 5, ProjectiveBase := true);
assert Discriminant(CB) eq d;
CheckQuinticPresentation(CB,f);

// Matrix input has the same default. Explicit frames are not reordered.
CM := FiniteFlatCover(Model(AA) : CoverDegree := 5, ProjectiveBase := true,
    VariableWeights := [-1,-2,-3,-4], RowWeights := [2,3,4,5,6], MatrixTwist := -10);
CheckQuinticPresentation(CM,f);
assert not assigned CM`Discriminant;

// Reproduce the auxiliary presentation explicitly. It is not the default.
CA := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true, Embedding := "Algebra");
assert Discriminant(CA) eq d;
QA := DefiningPolynomials(CA);
assert #QA eq 10 and Rank(Parent(QA[1])) eq 7;
assert CA`Embedding eq "Algebra";
PA := Parent(QA[1]);
ss,tt,z0,z1,z2,z3,z4 := Explode([PA.i : i in [1..7]]);
assert QA[1] eq (6912*ss^2-2662*ss*tt+153*tt^2)*z0^2
    -(256*ss-18*tt)*z0*z1+z0*z2+z1^2;
// Even after an explicit Algebra choice, ModelPolynomials is the four-variable model.
assert #ModelPolynomials(CA : Cox := false) eq 5;
assert Rank(Parent(ModelPolynomials(CA : Cox := false)[1])) eq 4;

// A stale/incompatible public cache must not silently pass as model equations.
Cbad := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true);
Cbad`DefiningPolynomials := QA;
failed := false;
try
    wrong := DefiningPolynomials(Cbad);
catch err
    failed := true;
end try;
assert failed;

// Base change and action preserve the selected embedding, with a populated table.
g := IdentityMatrix(R,5);
g[2,1] := s;
CD := ActBy(AA,g);
assert CD`Embedding eq "Model";
assert #DefiningPolynomials(CD) eq 5;
assert Rank(Parent(ModelPolynomials(CD : Cox := false)[1])) eq 4;
CF,phi := BaseChange(AA,7);
assert CF`Embedding eq "Model";
assert #DefiningPolynomials(CF) eq 5;
assert Rank(Parent(DefiningPolynomials(CF)[1])) eq 4;
// Over a field, the relative ambient becomes an ordinary P^3.
assert Dimension(AmbientBundle(CF)) eq 3;
assert Dimension(UnderlyingScheme(CF)) eq 0 and Degree(UnderlyingScheme(CF)) eq 5;

print "Presentation-selection regressions passed: five Pfaffians in four fibre coordinates.";
