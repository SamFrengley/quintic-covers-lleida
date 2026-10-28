/* Native API/action tests. Load after AttachSpec("spec").
   This file has NOT been executed in the authoring environment. */
procedure CompareFreshAction(D)
    M := Model(D);
    E := FiniteFlatCover(M : Twisted := IsTwisted(D),
        AssumeFiniteFlat := true);
    assert StructureConstants(D) eq StructureConstants(E);
    assert MultiplicationMatrices(D) eq MultiplicationMatrices(E);
    assert TracePairing(D) eq TracePairing(E);
    assert Discriminant(D) eq Discriminant(E);
end procedure;
procedure PopulateAlgebraCaches(C)
    T := StructureConstants(C);
    L := MultiplicationMatrices(C);
    v := TraceVector(C);
    H := TracePairing(C);
    d := Discriminant(C);
    assert C`StructureConstants eq T and C`_Data`Algebra`Matrices eq L;
    assert C`_Data`Algebra`Traces eq v and C`_Data`Algebra`Pairing eq H and C`Discriminant eq d;
end procedure;
print "public constructor, capitalized caches, default determinant twists";
K := Rationals();
U<z> := PolynomialRing(K);
P<X,Y> := PolynomialRing(K,2);
for n in [2..5] do
    f := z^n+2*z^(n-1)-z+3;
    F := &+[Coefficient(f,i)*X^i*Y^(n-i) : i in [0..n]];
    C := FiniteFlatCover(f);
    D := FiniteFlatCover(F);
    assert Type(C) eq FinFlatCov and IsTwisted(C) and C`Twisted;
    assert not assigned C`StructureConstants and not assigned C`Discriminant;
    assert StructureConstants(C) eq StructureConstants(D);
    PopulateAlgebraCaches(C);
end for;
print "quadratic invariance, cubic determinant squared, untwisted flag";
g := Matrix(K,2,2,[2,1,1,2]);
// nontriangular, determinant 3
for n in [2,3] do
    C := FiniteFlatCover(z^n+2*z+3);
    PopulateAlgebraCaches(C);
    D := C^g;
    assert IsTwisted(D) and assigned D`Discriminant;
    chi := n eq 2 select K!1 else Determinant(g)^2;
    assert DiscriminantMultiplier(C,g) eq chi and D`Discriminant eq chi*C`Discriminant;
    CompareFreshAction(D);
    E := ActBy(C,g : Twisted := false);
    assert not IsTwisted(E);
    assert E`Discriminant eq Determinant(g)^(n*(n-1))*C`Discriminant;
    CompareFreshAction(E);
    C0 := FiniteFlatCover(Model(C) : Twisted := false);
    assert Model(C0^g) eq Model(E);
    Alias := C;
    ActBy(~C,g : Twisted := false);
    assert Model(C) eq Model(E) and IsTwisted(Alias) and not IsTwisted(C);
    h := Matrix(K,2,2,[1,2,0,1]);
    assert Model((Alias^g)^h) eq Model(Alias^(h*g));
end for;
print "Wood quartic determinant-line subgroup and exact tensor convention";
C := FiniteFlatCover(z^4+2*z^3-z+1);
PopulateAlgebraCaches(C);
g3 := Matrix(K,3,3,[2,1,0,0,1,1,0,0,1]);
h2 := Matrix(K,2,2,[2,1,0,1]);
D := C^<g3,h2>;
assert D`Discriminant eq 4*C`Discriminant;
assert DiscriminantMultiplier(C,g3,h2) eq K!4;
CompareFreshAction(D);
/* Wood's original parameter hW has det(g3)*det(hW)=1. */
hW := Determinant(h2)^-1*h2;
assert Determinant(g3)*Determinant(hW) eq 1;
E := ActBy(C,g3,hW : Twisted := false);
assert Model(E) eq Model(D) and StructureConstants(E) eq StructureConstants(D);
Q := ModelPolynomials(C);
A := Parent(Q[1]);
xx := [&+[(A!g3[i,j])*A.i : i in [1..3]] : j in [1..3]];
expected := [Determinant(h2)^-1*(&+[(A!h2[i,j])*Evaluate(Q[j],xx) : j in [1..2]]) : i in [1..2]];
QD := ModelPolynomials(D);
PD := Parent(QD[1]);
assert QD eq [Evaluate(q,[PD.i : i in [1..Rank(PD)]]) : q in expected];
failed := false;
try
    Bad := C^g3;
catch e
    failed := true;
end try;
assert failed;
// the omitted h2 is identity, not an invented determinant companion
U4 := ActBy(C,g3 : Twisted := false);
CompareFreshAction(U4);
assert U4`Discriminant eq 2^8*C`Discriminant;
good3 := IdentityMatrix(K,3);
good3[1,2] := 2;
assert Model(C^good3) eq Model(ActBy(C,good3,IdentityMatrix(K,2)));
print "FV quintic is default; both transposes checked on tensor entries";
C := FiniteFlatCover(z^5+2*z^4-z+1);
PopulateAlgebraCaches(C);
g5 := IdentityMatrix(K,5);
g5[1,1] := 9;
g5[1,2] := 1;
g5[3,4] := -1;
h4 := IdentityMatrix(K,4);
h4[2,2] := 3;
h4[1,3] := 2;
assert Determinant(g5) eq Determinant(h4)^2;
D := C^<g5,h4>;
assert D`Discriminant eq 9*C`Discriminant;
assert DiscriminantMultiplier(C,g5,h4) eq K!9;
CompareFreshAction(D);
A := Model(C);
expected := [Determinant(h4)^-1*(&+[h4[i,j]*g5*A[j]*Transpose(g5) : j in [1..4]]) : i in [1..4]];
assert Model(D) eq expected;
E := ActBy(C,g5,h4 : Twisted := false);
CompareFreshAction(E);
assert E`Discriminant eq 9^16*3^10*C`Discriminant;
Alias := C;
ActBy(~C,g5,h4);
assert Model(C) eq Model(D) and Model(Alias) ne Model(C);
failed := false;
try
    Bad := ActBy(Alias,IdentityMatrix(K,5),h4);
catch e
    failed := true;
end try;
assert failed;
print "primitive sextic/septic constructor and resolution determinant-line twist";
for n in [6,7] do
    C := FiniteFlatCover(z^n-z-1 : Embedding := "Model");
    assert C`_Data`Presentation`Kind eq "Resolution" and not assigned C`_Data`Resolution`Maps;
    Q := DefiningPolynomials(C);
    assert #Q eq n*(n-3) div 2 and not assigned C`_Data`Resolution`Maps;
    PopulateAlgebraCaches(C);
    F := ResolutionMaps(C);
    g := IdentityMatrix(K,n-1);
    g[1,1] := 2;
    g[1,2] := 1;
    H := [* IdentityMatrix(K,Ncols(A)) : A in F *];
    H[#H][1,1] := 3;
    D := C^<g,H>;
    E := ActBy(C,g,H : Twisted := false);
    assert D`Discriminant eq 3^(2*n-2)*2^2*C`Discriminant;
    assert E`Discriminant eq 3^(2*n-2)*2^(2*n)*C`Discriminant;
    CompareFreshAction(D);
    CompareFreshAction(E);
    FD := Model(D);
    FE := Model(E);
    for i in [1..#F-1] do
        assert FD[i] eq FE[i];
    end for;
    assert 2*FD[#F] eq FE[#F];
end for;
print "stored untwisted choice survives fibre maps and unit checks";
R<s,t> := PolynomialRing(Integers(),2);
B<X,Y> := PolynomialRing(R,2);
C := FiniteFlatCover(X^3+s*X^2*Y+t^2*X*Y^2+s^3*Y^3 : ProjectiveBase := true,
    VariableWeights := [0,-1], EquationWeights := [0],Twisted := false);
D,phi := BaseChange(C,3);
assert not IsTwisted(D);
E,psi := CoverPatch(C,2);
assert not IsTwisted(E);
g := Matrix(R,2,2,[1,0,s,1]);
D := C^g;
assert not IsTwisted(D);
failed := false;
try
    D := ActBy(C,Transpose(g));
catch e
    failed := true;
end try;
assert failed;
D := ActBy(C,DiagonalMatrix(R,[2,1]) : Twisted := false);
assert Type(D) eq FinFlatCov;
print "Native action tests passed.";
