// Run from the package directory, in a fresh Magma session.
AttachSpec("spec");
assert FiniteFlatCoverVersion() eq "13.0.0";
ZZ := Integers();
R<s,t> := PolynomialRing(ZZ,2);
P<x> := PolynomialRing(R);
f := x^5 - 2*(9*t - 128*s)*x^4 + (9*t - 128*s)*(17*t - 54*s)*x^3
     - 18*(5*t + 4*s)*(9*t - 128*s)^2*x^2
     - 27*(33*t^2 - 488*t*s - 60*s^2)*(9*t - 128*s)^2*x
     - 27*(27*t^2 - 92*t*s - 3*s^2)*(9*t - 128*s)^3;
AA := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true);
assert AA`Embedding eq "Model";
assert Discriminant(AA) eq Discriminant(f);
assert AA`Embedding eq "Model";
Q := ModelPolynomials(AA : Cox := false);
assert #Q eq 5 and Rank(Parent(Q[1])) eq 4;
Qcox := DefiningPolynomials(AA);
assert #Qcox eq 5 and Rank(Parent(Qcox[1])) eq 6;
printf "Degree %o; embedding %o; %o Pfaffians in four fibre variables.\n",
    Degree(AA), AA`Embedding, #Q;
Q;
