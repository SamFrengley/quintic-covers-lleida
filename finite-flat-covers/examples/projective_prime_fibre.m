// Run from the package directory after AttachSpec("spec").
R<s,t> := PolynomialRing(Rationals(),2);
P<x> := PolynomialRing(R);
f := x^5-2*(9*t-128*s)*x^4+(9*t-128*s)*(17*t-54*s)*x^3
    -18*(5*t+4*s)*(9*t-128*s)^2*x^2
    -27*(33*t^2-488*t*s-60*s^2)*(9*t-128*s)^2*x
    -27*(27*t^2-92*t*s-3*s^2)*(9*t-128*s)^3;
A := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true);
pi := 3*s^2+14*s*t-t^2;
B,phi := BaseChange(A,pi);
BaseRing(B);                    // QQ(t)[s]/(s^2+14/3*t*s-1/3*t^2)
[phi(s),phi(t)];                // [s,t], the original homogeneous coordinates
assert phi(pi) eq 0;
Y := UnderlyingScheme(B);
IrreducibleComponents(ReducedSubscheme(SingularSubscheme(Y)));
// Same abstract fibre over its smaller Proj residue field (t=1).
B0,phi0 := BaseChange(A,pi : Homogeneous := false);
BaseRing(B0);                   // QQ[s]/(s^2+14/3*s-1/3)
assert phi0(t) eq 1;
IrreducibleComponents(ReducedSubscheme(SingularSubscheme(UnderlyingScheme(B0))));
