/* Run from the package directory: magma -b tests/run.m
   These tests are provided for a licensed Magma installation.
   They were NOT executed in the authoring environment. */
SetSeed(20261002);
procedure CheckRank(C)
    X := UnderlyingScheme(C);
    assert Dimension(X) eq 0;
    assert Degree(X) eq Degree(C);
    assert IsAssociative(C);
end procedure;
procedure CheckReduction(C,p)
    D,phi := BaseChange(C,p);
    assert StructureConstants(D) eq [phi(c) : c in StructureConstants(C)];
    assert Discriminant(D) eq phi(Discriminant(C));
    CheckRank(D);
end procedure;
Z := Integers();
P<x> := PolynomialRing(Z);
print "Degrees 1--5, integral structure constants and small characteristics";
C1 := IdentityFiniteFlatCover(Z);
assert Degree(C1) eq 1;
CheckReduction(C1,2);
for d in [2..5] do
    f := x^d-x-1;
    C := FiniteFlatCover(f : CheckAlgebra := true);
    assert Degree(C) eq d;
    assert Discriminant(C) eq Discriminant(f);
    for p in [2,3,5,7] do
        CheckReduction(C,p);
    end for;
    D,phi := GenericFibre(C);
    CheckRank(D);
    assert IsModelFiniteFlat(D);
end for;
print "Quintic generator convention and integral cubic resolvent";
f := x^5+5*x^4+4*x^3+3*x^2+2*x+1;
C5 := FiniteFlatCover(f);
L := MultiplicationMatrices(C5);
assert P!CharacteristicPolynomial(-L[5]) eq f;
C4 := FiniteFlatCover(x^4+4*x^3+3*x^2+2*x+1);
D3 := CubicResolvent(C4);
assert Degree(D3) eq 3 and Discriminant(D3) eq Discriminant(C4);
print "Zero tensors: the algebra remains finite, the small model does not";
F := GF(2);
B<X,Y> := PolynomialRing(F,2);
for d in [2,3] do
    C := FiniteFlatCover(B!0 : CoverDegree := d, Embedding := "Algebra");
    CheckRank(C);
    assert not IsModelFiniteFlat(C);
    assert Dimension(ModelScheme(C)) eq 1;
end for;
for d in [4,5] do
    n := d eq 4 select 3 else 5;
    count := d eq 4 select 2 else 4;
    C := FiniteFlatCover([ZeroMatrix(F,n,n) : j in [1..count]] : Embedding := "Algebra");
    CheckRank(C);
    assert not IsModelFiniteFlat(C);
    assert Dimension(ModelScheme(C)) eq d-2;
end for;
C := FiniteFlatCover(B!0 : CoverDegree := 3, Embedding := "Model");
assert not assigned C`UnderlyingScheme;
assert not IsModelFiniteFlat(C);
// Geometry is explicit, not a constructor side effect.
print "Quadratic coefficient tables, Hessians, and characteristic 2";
T<a,b,c> := PolynomialRing(Z,3);
Q := [a^2-b*c,b^2+a*c+c^2];
C := FiniteFlatCover(Q);
H := [Matrix(Z,3,3,[Integers()!Derivative(Derivative(q,i),j) : i,j in [1..3]]) : q in Q];
D := FiniteFlatCover(H : ModelConvention := "Hessian");
assert Model(C) eq Model(D);
D2,phi := BaseChange(D,2);
assert IsModelFiniteFlat(D2);
assert #ModelPolynomials(D2) eq 2;
print "Affine polynomial bases: vertical, horizontal, and evaluation fibres";
R<t> := PolynomialRing(Z);
U<z> := PolynomialRing(R);
C := FiniteFlatCover(z^4+t*z+1 : CheckAlgebra := true);
D,phi := BaseChange(C,3);
assert IsField(BaseRing(D));
CheckRank(D);
assert Characteristic(BaseRing(D)) eq 3;
D,phi := BaseChange(C,t^2+1);
assert phi(t^2+1) eq 0;
CheckRank(D);
D,phi := BaseChange(C,GF(5),[2]);
assert phi(t) eq GF(5)!2;
CheckRank(D);
D,phi := BaseChange(C,3 : ToField := false);
assert Type(BaseRing(D)) eq RngUPol;
assert Characteristic(BaseRing(D)) eq 3;
assert StructureConstants(D) eq [phi(a) : a in StructureConstants(C)];
print "Bihomogeneous cubic over P^1_Z and graded actions";
R<s,t> := PolynomialRing(Z,2);
U<x,y> := PolynomialRing(R,2);
f := x^3+s*x^2*y+t^2*x*y^2+s^3*y^3;
C := FiniteFlatCover(f : ProjectiveBase := true, VariableWeights := [0,-1],
    EquationWeights := [0], CheckAlgebra := true, Embedding := "Algebra");
assert C`_Data`Bundle`Algebra eq [0,1,2];
P,Q,grading,irrelevant := CoxData(C);
assert grading eq [[1,1,0,1,2],[0,0,1,1,1]];
assert #irrelevant eq 2;
g := Matrix(R,2,2,[1,0,s,1]);
D := ActBy(C,g);
assert IsAssociative(D);
assert Discriminant(D) eq Discriminant(C);
failed := false;
try
    D := ActBy(C,Transpose(g));
catch err
    failed := true;
end try;
assert failed;
failed := false;
try
    D := ActBy(C,DiagonalMatrix(R,[2,1]));
catch err
    failed := true;
end try;
assert failed;
print "Proj residue fields versus homogeneous fraction fields";
D,phi := BaseChange(C,2);
assert IsField(BaseRing(D));
assert Rank(BaseRing(D)) eq 2;
CheckRank(D);
E,psi := BaseChange(C,2 : Homogeneous := false);
assert psi(t) eq 1;
assert Rank(BaseRing(E)) eq 1;
CheckRank(E);
D,phi := BaseChange(C,s^2+t^2);
assert phi(s^2+t^2) eq 0;
CheckRank(D);
E,psi := BaseChange(C,s^2+t^2 : Homogeneous := false);
assert psi(t) eq 1 and psi(s)^2+1 eq 0;
CheckRank(E);
D,phi := BaseChange(C,t : Homogeneous := false);
assert phi(s) eq 1 and phi(t) eq 0;
CheckRank(D);
D,phi := BaseChange(C,GF(3),[1,0]);
CheckRank(D);
failed := false;
try
    D,phi := BaseChange(C,GF(3),[0,0]);
catch err
    failed := true;
end try;
assert failed;
D,phi := CoverPatch(C,2);
assert Type(BaseRing(D)) eq RngUPol and Type(BaseRing(BaseRing(D))) eq RngInt;
assert phi(t) eq 1;
assert StructureConstants(D) eq [phi(a) : a in StructureConstants(C)];
D,phi := BaseChange(C,3 : ToField := false);
assert ProjectiveBase(D) and D`_Data`Bundle`Variables eq C`_Data`Bundle`Variables;
assert Characteristic(BaseRing(D)) eq 3;
X := UnderlyingScheme(D);
assert NumberOfGradings(X) eq 2;
print "Integral scroll backend (native Rng-valued constructor)";
X := UnderlyingScheme(C);
assert Type(BaseRing(X)) eq RngInt;
assert NumberOfGradings(X) eq 2;
assert (#DefiningPolynomials(C)) eq 3;
print "Nontrivial quintic row grading and graded GL5 action";
U<z> := PolynomialRing(Z);
A := Model(FiniteFlatCover(z^5-z-1));
A := [ChangeRing(a,R) : a in A];
h := DiagonalMatrix(R,[1,s,1,1,1]);
A := [Transpose(h)*a*h : a in A];
C := FiniteFlatCover(A : ProjectiveBase := true, VariableWeights := [0,0,0,0],
    RowWeights := [0,1,0,0,0], MatrixTwist := 0, CheckAlgebra := true, Embedding := "Algebra");
assert C`_Data`Bundle`Algebra eq [0,2,2,2,2];
g := IdentityMatrix(R,5);
g[2,1] := t;
D := ActBy(C,g);
assert IsAssociative(D);
assert Discriminant(D) eq Discriminant(C);
D,phi := BaseChange(C,2);
CheckRank(D);
