// Regression for automatic polynomial gradings and the FV splitting data.
// Run through v10_only.m or run.m. No native execution is claimed here.
procedure AssertGradingOnly(C)
    assert not assigned C`StructureConstants;
    assert not assigned C`Discriminant;
    assert not assigned C`DefiningPolynomials;
    assert not assigned C`UnderlyingScheme;
    for name in ["TracePairing", "MultiplicationMatrices",
                 "ResolutionMaps", "FirstSyzygies", "Resolvent"] do
        assert name notin CachedComputations(C);
    end for;
end procedure;

ZZ := Integers();
R<s,t> := PolynomialRing(ZZ,2);
P<x> := PolynomialRing(R);
f := x^5 - 2*(9*t - 128*s)*x^4 + (9*t - 128*s)*(17*t - 54*s)*x^3
     - 18*(5*t + 4*s)*(9*t - 128*s)^2*x^2
     - 27*(33*t^2 - 488*t*s - 60*s^2)*(9*t - 128*s)^2*x
     - 27*(27*t^2 - 92*t*s - 3*s^2)*(9*t - 128*s)^3;

C := FiniteFlatCover(f : ProjectiveBase := true);
assert C`ProjectiveBase;
AssertGradingOnly(C);
assert "ModelPolynomials" notin CachedComputations(C);
assert TschirnhausenInvariants(C) eq [1,2,3,4];
assert FirstSyzygyInvariants(C) eq [2,3,4,5,6];
e := TschirnhausenInvariants(C : Sorted := false);
fdegrees := FirstSyzygyInvariants(C : Sorted := false);
assert e eq [1,2,3,4];
assert fdegrees eq [2,3,4,5,6];
assert BundleWeights(C : Embedding := "Model") eq [-1,-2,-3,-4];
assert BundleWeights(C : Embedding := "Algebra") eq [0,1,2,3,4];
AssertGradingOnly(C);

// Inspect every nonzero matrix coefficient in FV order.
A := Model(C);
assert #A eq 4;
for k in [1..4] do
    for i in [1..5] do
        for j in [i+1..5] do
            a := A[k][i,j];
            if a ne 0 then
                assert IsHomogeneous(a);
                assert Degree(a) eq fdegrees[i]+fdegrees[j]+e[k]-(&+e);
            end if;
        end for;
    end for;
end for;
AssertGradingOnly(C);

// Explicit model weights are respected, even in a noncanonical common twist.
D := FiniteFlatCover(A : ProjectiveBase := true,
    VariableWeights := [-1,-2,-3,-4], RowWeights := [2,3,4,5,6], MatrixTwist := -10);
assert TschirnhausenInvariants(D) eq [1,2,3,4];
assert FirstSyzygyInvariants(D) eq [2,3,4,5,6];
AssertGradingOnly(D);

// Homogeneous binary input and the univariate constructor agree.
H<X,Y> := PolynomialRing(R,2);
F := &+[(H!Coefficient(f,i))*X^i*Y^(5-i) : i in [0..5]];
D := FiniteFlatCover(F : ProjectiveBase := true);
assert Model(D) eq A;
assert TschirnhausenInvariants(D : Sorted := false) eq e;
assert FirstSyzygyInvariants(D : Sorted := false) eq fdegrees;
AssertGradingOnly(D);

// Graded FV action, still without computing a table or a discriminant.
g := IdentityMatrix(R,5);
g[2,1] := s;
D := C^g;
assert TschirnhausenInvariants(D : Sorted := false) eq e;
assert FirstSyzygyInvariants(D : Sorted := false) eq fdegrees;
AssertGradingOnly(D);

// Vertical projective fibres retain the grading even when coefficients vanish.
Cp,phi := BaseChange(C,2 : ToField := false);
assert Cp`ProjectiveBase;
assert TschirnhausenInvariants(Cp : Sorted := false) eq e;
assert FirstSyzygyInvariants(Cp : Sorted := false) eq fdegrees;
AssertGradingOnly(Cp);
Ct,psi := CoverPatch(C,2);
assert not Ct`ProjectiveBase;
assert not assigned Ct`Discriminant;

// Asking for equations is separate from asking for a multiplication table.
Q := ModelPolynomials(C : Cox := false);
w := BundleWeights(C : Embedding := "Model");
assert #Q eq 5;
for i in [1..5] do
    cc,mm := CoefficientsAndMonomials(Q[i]);
    for j in [1..#cc] do
        ex := Exponents(mm[j]);
        assert Degree(cc[j])+(&+[ex[k]*w[k] : k in [1..4]]) eq -fdegrees[i];
    end for;
end for;
assert not assigned C`StructureConstants;
assert not assigned C`Discriminant;

// An explicit table request; its basis now follows the ordered projective frame.
T := StructureConstants(C);
aw := [0] cat e;
for i,j,k in [0..4] do
    a := T[(i*5+j)*5+k+1];
    if a ne 0 then
        assert IsHomogeneous(a);
        assert Degree(a) eq aw[i+1]+aw[j+1]-aw[k+1];
    end if;
end for;
assert not assigned C`Discriminant;

// All polynomial formats get coefficient-degree inference, including sparse ones.
for n in [2..7] do
    h := x^n+s*x^(n-1)+t^n;
    D := FiniteFlatCover(h : ProjectiveBase := true, Embedding := "Model");
    assert TschirnhausenInvariants(D) eq [1..n-1];
    fs := FirstSyzygyInvariants(D);
    if n le 3 then
        assert fs eq [];
    else
        assert #fs eq n*(n-3) div 2;
        assert (&+fs) eq (n-3)*(&+[1..n-1]);
    end if;
    if n le 5 then
        assert TschirnhausenInvariants(D : Sorted := false) eq TschirnhausenInvariants(D);
        assert FirstSyzygyInvariants(D : Sorted := false) eq fs;
    end if;
    AssertGradingOnly(D);
    if n ge 6 then
        assert #Model(D) eq 1;  // no completion of the resolution
    end if;
end for;

// Quartic coordinates and its two quadratic generators are also physically reordered.
Q4 := FiniteFlatCover(x^4+s*x^3+t^4 : ProjectiveBase := true, Embedding := "Model");
assert TschirnhausenInvariants(Q4 : Sorted := false) eq [1,2,3];
assert FirstSyzygyInvariants(Q4 : Sorted := false) eq [2,4];
assert BundleWeights(Q4 : Embedding := "Model") eq [-1,-2,-3];
q4 := ModelPolynomials(Q4 : Cox := false);
assert #q4 eq 2;
w4 := [-1,-2,-3];
f4 := [2,4];
for i in [1..2] do
    cc,mm := CoefficientsAndMonomials(q4[i]);
    for j in [1..#cc] do
        ex := Exponents(mm[j]);
        assert Degree(cc[j])+(&+[ex[k]*w4[k] : k in [1..3]]) eq -f4[i];
    end for;
end for;

failed := false;
try
    Bad := FiniteFlatCover(x^5+s*x^4+t^3*x^3+1 : ProjectiveBase := true);
catch err
    failed := true;
end try;
assert failed;
failed := false;
try
    Bad := FiniteFlatCover(x^5+s+t^2 : ProjectiveBase := true);
catch err
    failed := true;
end try;
assert failed;
failed := false;
try
    Bad := FiniteFlatCover(x^5+1 : ProjectiveBase := "proj");
catch err
    failed := true;
end try;
assert failed;
print "Projective polynomial grading and FV splitting-data regressions passed.";
