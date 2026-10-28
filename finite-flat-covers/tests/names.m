// Naming regressions: fibre coordinates are X[i], base changes retain user base names.
Z := Integers();
R<s,t> := PolynomialRing(Z,2);
U<x> := PolynomialRing(R);
f := x^5 + s*x^4 + t^5;
C := FiniteFlatCover(f : ProjectiveBase := true, Embedding := "Model");

Q := ModelPolynomials(C : Cox := false);
P := Parent(Q[1]);
assert [Sprint(Name(P,i)) : i in [1..Rank(P)]] eq
       [Sprintf("X[%o]",i) : i in [1..Rank(P)]];

Cp,phip := BaseChange(C,2 : ToField := false);
Rp := BaseRing(Cp);
assert [Sprint(Name(Rp,i)) : i in [1..Rank(Rp)]] eq ["s","t"];
Qp := ModelPolynomials(Cp : Cox := false);
PP := Parent(Qp[1]);
assert [Sprint(Name(PP,i)) : i in [1..Rank(PP)]] eq
       [Sprintf("X[%o]",i) : i in [1..Rank(PP)]];

Cg,phig := BaseChange(C,2);
Kg := BaseRing(Cg);
assert [Sprint(Name(Kg,i)) : i in [1..Rank(Kg)]] eq ["s","t"];

G,phiG := GenericFibre(C);
KG := BaseRing(G);
assert [Sprint(Name(KG,i)) : i in [1..Rank(KG)]] eq ["s","t"];

Ga,phiGa := GenericFibre(C : Homogeneous := false);
assert Sprint(Name(BaseRing(Ga),1)) eq "s";

Cs,phis := CoverPatch(C,1);
assert Sprint(Name(BaseRing(Cs),1)) eq "t";
Ct,phit := CoverPatch(C,2);
assert Sprint(Name(BaseRing(Ct),1)) eq "s";

// Low-degree homogeneous input is copied into a standard X-coordinate ring too.
B<u,v> := PolynomialRing(R,2);
C3 := FiniteFlatCover(u^3+s*u^2*v+t^2*u*v^2+s^3*v^3 : ProjectiveBase := true,
    Embedding := "Model");
q3 := ModelPolynomials(C3 : Cox := false)[1];
P3 := Parent(q3);
assert [Sprint(Name(P3,i)) : i in [1..2]] eq ["X[1]","X[2]"];
