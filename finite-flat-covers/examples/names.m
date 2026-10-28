AttachSpec("spec");
Z := Integers();
R<s,t> := PolynomialRing(Z,2);
P<x> := PolynomialRing(R);
C := FiniteFlatCover(x^5+s*x^4+t^5 : ProjectiveBase := true, Embedding := "Model");

ModelPolynomials(C : Cox := false); // parent has X[1],...,X[4]
Cp,phi := BaseChange(C,2 : ToField := false);
BaseRing(Cp);                       // GF(2)[s,t]
Cg,psi := BaseChange(C,2);
BaseRing(Cg);                       // GF(2)(s,t)
Cs,_ := CoverPatch(C,1);
BaseRing(Cs);                       // Z[t]
Ct,_ := CoverPatch(C,2);
BaseRing(Ct);                       // Z[s]
