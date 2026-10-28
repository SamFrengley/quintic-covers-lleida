AttachSpec("spec");
R<s,t> := PolynomialRing(Integers(),2);
P<x,y> := PolynomialRing(R,2);
C := FiniteFlatCover(x^3+s*x^2*y+t^2*x*y^2+s^3*y^3 :
    ProjectiveBase := true, VariableWeights := [0,-1],
    EquationWeights := [0], Embedding := "Model");
assert C`ProjectiveBase;
g := Matrix(R,2,2,[1,0,s,1]); // g^T substitutes x -> x+s*y
D := C^g;
Q := DefiningPolynomials(D);
print Q;
Cp,phi := BaseChange(C,2);
print BaseRing(Cp);
Ct,psi := CoverPatch(C,2);
assert psi(t) eq 1;
print CachedComputations(C);
quit;
