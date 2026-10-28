/* Native regression tests for generic-field actions followed by exact descent.
   This file has not been executed in the authoring environment. */
print "fraction-field binary actions: accept exactly when the transformed form descends";
Z := Integers();
P<X,Y> := PolynomialRing(Z,2);
C := FiniteFlatCover(2*(X^3+X^2*Y+X*Y^2+Y^3));
K := Rationals();
g := DiagonalMatrix(K,[K!1/2,K!1/2]);
D := C^g;
Q<U,V> := PolynomialRing(Z,2);
PD := Parent(Model(D));
assert Model(D) eq PD.1^3+PD.1^2*PD.2+PD.1*PD.2^2+PD.2^3;
assert not assigned D`Discriminant;
failed := false;
try
    Bad := C^DiagonalMatrix(K,[K!1/3,K!1/3]);
catch e
    failed := true;
end try;
assert failed;

print "fraction-field projective actions: rational homogeneity and integral descent";
R<s,t> := PolynomialRing(Rationals(),2);
B<X,Y> := PolynomialRing(R,2);
F := s*(X^3+X^2*Y+X*Y^2+Y^3);
C := FiniteFlatCover(F : ProjectiveBase := true);
L := FieldOfFractions(R);
r := (L!t)/(L!s);
g := DiagonalMatrix(L,[r,r]);
D := C^g;
MD := Model(D);
assert MD eq t*(Parent(MD).1^3+Parent(MD).1^2*Parent(MD).2
    +Parent(MD).1*Parent(MD).2^2+Parent(MD).2^3);
// Homogeneous of degree zero, but the transformed form has a genuine denominator.
failed := false;
r := (L!t)/(L!(s+t));
try
    Bad := C^DiagonalMatrix(L,[r,r]);
catch e
    failed := true;
end try;
assert failed;
// A genuinely nonhomogeneous rational entry is still rejected.
failed := false;
r := (L!(s+t^2))/(L!s);
try
    Bad := C^DiagonalMatrix(L,[r,r]);
catch e
    failed := true;
end try;
assert failed;


print "projective actions may change the split bundle weights";
R2<s,t> := PolynomialRing(Rationals(),2);
B2<X,Y> := PolynomialRing(R2,2);
F2 := s*(X^3+X^2*Y+X*Y^2+Y^3);
C2 := FiniteFlatCover(F2 : ProjectiveBase := true);
assert TschirnhausenInvariants(C2) eq [1,1];
L2 := FieldOfFractions(R2);
g2 := DiagonalMatrix(L2,[1/(L2!s),1/(L2!s)]);
D2 := C2^g2;
M2 := Model(D2);
assert M2 eq Parent(M2).1^3+Parent(M2).1^2*Parent(M2).2
    +Parent(M2).1*Parent(M2).2^2+Parent(M2).2^3;
assert TschirnhausenInvariants(D2) eq [0,0];
assert not assigned D2`Discriminant;
// One row cannot mix source summands in two incompatible target degrees.
failed := false;
badg := Matrix(L2,2,2,[1,1/(L2!s),0,1]);
try
    Bad := C2^badg;
catch e
    failed := true;
end try;
assert failed;

print "fraction-field quintic tensor action";
U<z> := PolynomialRing(Z);
C0 := FiniteFlatCover(z^5-z-1);
M0 := Model(C0);
C := FiniteFlatCover([2*A : A in M0]);
r := K!1/2;
g5 := DiagonalMatrix(K,[r^8 : i in [1..5]]);
h4 := DiagonalMatrix(K,[r^5 : i in [1..4]]);
D := C^<g5,h4>;
assert Model(D) eq M0;
failed := false;
try
    Bad := C0^<g5,h4>;
catch e
    failed := true;
end try;
assert failed;


print "projective quintic actions may change both E and F splittings";
Rq<s,t> := PolynomialRing(Rationals(),2);
Kq := FieldOfFractions(Rq);
Uq<z> := PolynomialRing(Rationals());
Q0 := FiniteFlatCover(z^5-z-1);
Mq0 := Model(Q0);
Cq := FiniteFlatCover([s*ChangeRing(A,Rq) : A in Mq0] :
    ProjectiveBase := true, VariableWeights := [0,0,0,0],
    RowWeights := [0,0,0,0,0], MatrixTwist := 1);
assert TschirnhausenInvariants(Cq) eq [5,5,5,5];
assert FirstSyzygyInvariants(Cq) eq [8,8,8,8,8];
rq := 1/(Kq!s);
gq := DiagonalMatrix(Kq,[rq^8 : i in [1..5]]);
hq := DiagonalMatrix(Kq,[rq^5 : i in [1..4]]);
Dq := Cq^<gq,hq>;
assert Model(Dq) eq [ChangeRing(A,Rq) : A in Mq0];
assert TschirnhausenInvariants(Dq) eq [0,0,0,0];
assert FirstSyzygyInvariants(Dq) eq [0,0,0,0,0];
assert not assigned Dq`Discriminant;

print "operator and in-place forms use the same descent path";
E := ActBy(C,g5,h4);
assert Model(E) eq Model(D);
ActBy(~C,g5,h4);
assert Model(C) eq Model(D);
print "Fraction-field action tests passed.";
