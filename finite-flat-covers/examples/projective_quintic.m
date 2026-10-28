AttachSpec("spec");
ZZ := Integers();
R<s,t> := PolynomialRing(ZZ,2);
P<x> := PolynomialRing(R);
f := x^5 - 2*(9*t - 128*s)*x^4 + (9*t - 128*s)*(17*t - 54*s)*x^3
     - 18*(5*t + 4*s)*(9*t - 128*s)^2*x^2
     - 27*(33*t^2 - 488*t*s - 60*s^2)*(9*t - 128*s)^2*x
     - 27*(27*t^2 - 92*t*s - 3*s^2)*(9*t - 128*s)^3;

C := FiniteFlatCover(f : ProjectiveBase := true);
A := Model(C);

// The ACTUAL tensor frame, not merely the sorted display, is FV ordered.
assert TschirnhausenInvariants(C : Sorted := false) eq [1,2,3,4];
assert FirstSyzygyInvariants(C : Sorted := false) eq [2,3,4,5,6];
assert BundleWeights(C : Embedding := "Model") eq [-1,-2,-3,-4];

// Hence A[k] corresponds to e_k and row/column i to f_i.
e := TschirnhausenInvariants(C : Sorted := false);
fdeg := FirstSyzygyInvariants(C : Sorted := false);
for k in [1..4] do
    for i in [1..5] do
        for j in [i+1..5] do
            if A[k][i,j] ne 0 then
                assert Degree(A[k][i,j]) eq fdeg[i]+fdeg[j]+e[k]-(&+e);
            end if;
        end for;
    end for;
end for;

// Geometry remains lazy.
assert not assigned C`StructureConstants;
assert not assigned C`Discriminant;
Q := ModelPolynomials(C);
print Q;
quit;

// Polynomial input selects the FV relative-canonical model by default.
assert C`Embedding eq "Model";
Qdef := DefiningPolynomials(C);
assert #Qdef eq 5;
