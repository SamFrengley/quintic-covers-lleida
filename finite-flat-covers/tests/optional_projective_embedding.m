/* Optional, more expensive elimination backend. Run from package directory.
   NOT EXECUTED in the authoring environment. */
AttachSpec("spec");
R<s,t> := PolynomialRing(Integers(),2);
P<x,y> := PolynomialRing(R,2);
C := FiniteFlatCover(x^2+s*x*y+t^2*y^2 : ProjectiveBase := true,
    VariableWeights := [0,-1], EquationWeights := [0],
    Embedding := "Model", AssumeFiniteFlat := true);
X,V := ProjectiveScrollEmbedding(C);
assert Type(BaseRing(X)) eq RngInt;
assert NumberOfGradings(X) eq 1;
print X;
print "Optional integral projective embedding constructed.";
quit;
