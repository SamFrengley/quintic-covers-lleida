// Model(C) API contract. No derived computation should occur.
Z := Integers();
U<z> := PolynomialRing(Z);

f2 := z^2 + 3*z + 5;
C2 := FiniteFlatCover(f2);
M2 := Model(C2);
assert Type(M2) eq RngMPolElt;
assert Rank(Parent(M2)) eq 2;
assert Degree(M2) eq 2;
assert Evaluate(M2,[U.1,1]) eq f2;
assert not assigned C2`StructureConstants;
assert not assigned C2`Discriminant;

f3 := z^3 - 2*z + 7;
C3 := FiniteFlatCover(f3);
M3 := Model(C3);
assert Type(M3) eq RngMPolElt;
assert Rank(Parent(M3)) eq 2;
assert Degree(M3) eq 3;
assert Evaluate(M3,[U.1,1]) eq f3;
assert not assigned C3`StructureConstants;
assert not assigned C3`Discriminant;

f4 := z^4 + z^2 - z + 2;
C4 := FiniteFlatCover(f4);
M4 := Model(C4);
assert Type(M4) eq SeqEnum and #M4 eq 2;
assert forall{A : A in M4 | Type(A) eq AlgMatElt and Nrows(A) eq 3 and Ncols(A) eq 3 and Transpose(A) eq A};
assert not assigned C4`StructureConstants;
assert not assigned C4`Discriminant;

f5 := z^5 - z - 1;
C5 := FiniteFlatCover(f5);
M5 := Model(C5);
assert Type(M5) eq SeqEnum and #M5 eq 4;
assert forall{A : A in M5 |
    Type(A) eq AlgMatElt and Nrows(A) eq 5 and Ncols(A) eq 5 and
    Transpose(A) eq -A and forall{i : i in [1..5] | A[i,i] eq 0}};
assert not assigned C5`StructureConstants;
assert not assigned C5`Discriminant;

// Homogeneous binary input is returned as a binary form, not dehomogenized.
P<X,Y> := PolynomialRing(Z,2);
F3 := X^3 + 2*X*Y^2 - 5*Y^3;
H3 := FiniteFlatCover(F3);
assert Model(H3) eq F3;

// Projective polynomial input returns the ordered matrix model without computing invariants.
R<s,t> := PolynomialRing(Z,2);
PR<x> := PolynomialRing(R);
g := x^5 + s*x^4 + t*x^3 + s^2*x^2 + s*t*x + t^2;
G := FiniteFlatCover(g : CoverDegree := 5, ProjectiveBase := true);
MG := Model(G);
assert #MG eq 4;
assert not assigned G`StructureConstants;
assert not assigned G`Discriminant;

print "Model accessor tests passed.";
