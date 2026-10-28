AttachSpec("spec");
P<z> := PolynomialRing(Rationals());
C := FiniteFlatCover(z^6-z-1 : Embedding := "Model");
Q := DefiningPolynomials(C);
assert #Q eq 9;
assert "ResolutionMaps" notin CachedComputations(C);
g := IdentityMatrix(Rationals(),5);
g[1,2] := 1;
D := C^g;
assert "ResolutionMaps" notin CachedComputations(D);
S := FirstSyzygies(D); // asks for the first map, not completion
print Nrows(S),Ncols(S);
F := ResolutionMaps(D); // explicit completion
print [<Nrows(A),Ncols(A)> : A in F];
quit;
