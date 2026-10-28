/* Standard Bhargava-normalized resolvent tests.
   Loaded by tests/run.m. Native execution has not been performed here. */
procedure CheckResolventImages(T,B)
    n := Nrows(B);
    assert Ncols(B) eq n and #T eq n^3;
    for i,j in [0..n-1] do
        for a in [1..n] do
            assert B[i+1,a]*B[j+1,a] eq &+[T[(i*n+j)*n+k+1]*B[k+1,a] : k in [0..n-1]];
        end for;
    end for;
end procedure;
function SplitTensorForResolvent(R)
    A := [];
    for i in [1..4] do
        M := ZeroMatrix(R,5,5);
        for j in [((i+3) mod 5)+1,(i mod 5)+1] do
            M[i,j] +:= 1;
            M[j,i] -:= 1;
        end for;
        Append(~A,M);
    end for;
    return A;
end function;
procedure CompareFreshResolvent(C)
    D := Resolvent(C);
    Fresh := FiniteFlatCover(Model(C) : Twisted := IsTwisted(C));
    E := Resolvent(Fresh : Check := true);
    assert StructureConstants(D) eq StructureConstants(E);
    assert TracePairing(D) eq TracePairing(E);
    assert Discriminant(D) eq TraceDiscriminant(E);
end procedure;
print "unified cached resolver and discriminant routing";
Z := Integers();
U<z> := PolynomialRing(Z);
C3 := FiniteFlatCover(z^3-z-1);
C4 := FiniteFlatCover(z^4-z-1);
for C in [C3,C4] do
    assert not assigned C`_Data`Resolvents`Standard and not assigned C`StructureConstants;
    d := Discriminant(C);
    assert assigned C`_Data`Resolvents`Standard and not assigned C`StructureConstants;
    D := Resolvent(C);
    assert Type(D) eq FinFlatCov and Degree(D) eq ResolventDegree(C);
    assert d eq Discriminant(D) and IsTwisted(D);
    assert VerifyResolvent(C : CheckDiscriminant := true) and D`_Data`Resolvents`Verified;
    assert d eq TraceDiscriminant(C) and d eq TraceDiscriminant(D);
end for;
assert StructureConstants(QuadraticResolvent(C3)) eq StructureConstants(Resolvent(C3));
assert StructureConstants(CubicResolvent(C4)) eq StructureConstants(Resolvent(C4));
assert Degree(Resolvent(Resolvent(C4))) eq 2;
assert Discriminant(Resolvent(Resolvent(C4))) eq Discriminant(C4);
print "arbitrary cubic unit bases and explicit characteristic-two distinction";
T := StructureConstants(C3);
A3 := FiniteFlatCoverFromStructureConstants(T,3);
assert StructureConstants(Resolvent(A3)) eq StructureConstants(Resolvent(C3));
F := GF(2);
P<x,y> := PolynomialRing(F,2);
A := FiniteFlatCover(x^3+x*y^2+y^3);
B := FiniteFlatCover(x^3+x^2*y+x*y^2);
Q1 := Resolvent(A : Check := true);
Q2 := Resolvent(B : Check := true);
W<v> := PolynomialRing(F);
f1 := Evaluate(Model(Q1),[v,W!1]);
f2 := Evaluate(Model(Q2),[v,W!1]);
assert f1 eq v^2+v and f2 eq v^2+v+1;
assert Discriminant(A) eq Discriminant(B) and Discriminant(A) eq 1;
print "zero quartic resolvent retains rank three, not degree minus infinity";
for p in [2,3,5] do
    F := GF(p);
    C := FiniteFlatCover([ZeroMatrix(F,3,3),ZeroMatrix(F,3,3)]);
    D := Resolvent(C : Check := true);
    assert Degree(D) eq 3 and Model(D) eq 0;
    assert Degree(UnderlyingScheme(D)) eq 3;
    C := FiniteFlatCover([ZeroMatrix(F,5,5) : i in [1..4]]);
    D := Resolvent(C : Check := true);
    assert Degree(D) eq 6 and #StructureConstants(D) eq 216;
    assert Degree(UnderlyingScheme(D)) eq 6 and Discriminant(D) eq 0;
end for;
print "Bhargava sextic discriminant and actual split lattice ring";
C5 := FiniteFlatCover(z^5-z-1);
d := Discriminant(C5);
assert not assigned C5`_Data`Resolvents`Standard and not assigned C5`_Data`Resolvents`Minors;
S := SexticResolvent(C5 : Check := true);
assert Type(S) eq FinFlatCov and Degree(S) eq 6;
assert assigned C5`_Data`Resolvents`Standard and #C5`_Data`Resolvents`Minors eq 210;
assert S`Discriminant eq (16*d)^3 and TraceDiscriminant(S) eq (16*d)^3;
assert #DefiningPolynomials(S) eq 15 and not assigned S`_Data`Resolution`Maps;
assert StructureConstants(Resolvent(C5)) eq S`StructureConstants;
Split := FiniteFlatCover(SplitTensorForResolvent(Z));
S := Resolvent(Split : Check := true);
assert Discriminant(Split) eq 1 and Discriminant(S) eq 4096;
Images := Matrix(Z,6,6,[
    1,1,1,1,1,1,
    -1,1,-1,-1,1,-1,
    -1,1,1,-1,-1,-1,
    -1,-1,1,1,-1,-1,
    -1,-1,-1,1,-1,1,
    -1,-1,-1,-1,1,1
]);
assert Abs(Determinant(Images)) eq 64;
CheckResolventImages(StructureConstants(S),Images);
for row in Rows(Images) do
    assert forall{v : v in Eltseq(row) | (v-row[1]) mod 2 eq 0};
    assert ((&+Eltseq(row))-2*row[1]) mod 4 eq 0;
end for;
print "fresh characteristic 2/3 formulas and cached base-change compatibility";
S := Resolvent(C5);
for p in [2,3,5,7] do
    Cp,phi := BaseChange(C5,p);
    Sp := Resolvent(Cp);
    assert StructureConstants(Sp) eq [phi(v) : v in StructureConstants(S)];
    Fresh := FiniteFlatCover(Model(Cp));
    FreshS := Resolvent(Fresh : Check := true);
    assert StructureConstants(FreshS) eq StructureConstants(Sp);
    X := UnderlyingScheme(Sp);
    assert Dimension(X) eq 0 and Degree(X) eq 6;
    assert IsEmpty(SingularSubscheme(X)) eq (p ne 2);
end for;
K := GF(4);
hZ := map<Z -> K | a :-> K!a>;
CK,phi := BaseChange(C5,hZ);
SK := Resolvent(CK);
Fresh := FiniteFlatCover(Model(CK));
FS := Resolvent(Fresh : Check := true);
assert StructureConstants(SK) eq StructureConstants(FS);
print "cached transport under Wood/FV and untwisted actions";
K := Rationals();
U<z> := PolynomialRing(K);
for n in [4,5] do
    C := FiniteFlatCover(z^n-z-1);
    E := Resolvent(C : Check := true);
    L := MultiplicationMatrices(E);
    H := TracePairing(E);
    t := TraceDiscriminant(E);
    if n eq 4 then
        g := Matrix(K,3,3,[2,1,0,0,1,1,0,0,1]);
        h := Matrix(K,2,2,[2,1,0,1]);
    else
        g := IdentityMatrix(K,5);
        g[1,1] := 4;
        g[1,2] := 1;
        g[3,4] := -1;
        h := IdentityMatrix(K,4);
        h[2,2] := 2;
        h[1,3] := 1;
        h[2,4] := 2;
    end if;
    for tw in [true,false] do
        D := ActBy(C,g,h : Twisted := tw);
        assert not assigned D`_Data`Resolvents`Standard;
        assert assigned D`_Data`Resolvents`Pending;
        if n eq 5 then
            assert not assigned D`_Data`Resolvents`Minors;
        end if;
        CompareFreshResolvent(D);
        DD := C^<g,h>;
        CompareFreshResolvent(DD);
        Copy := C;
        ActBy(~Copy,g,h : Twisted := tw);
        CompareFreshResolvent(Copy);
    end for;
end for;
print "polynomial base and Proj split-bundle grading";
R<s,t> := PolynomialRing(Z,2);
A := SplitTensorForResolvent(R);
rw := [0,1,0,0,0];
A := [Matrix(R,5,5,[M[i,j]*s^(rw[i]+rw[j]) : i,j in [1..5]]) : M in A];
C := FiniteFlatCover(A : ProjectiveBase := true,VariableWeights := [0,0,0,0],RowWeights := rw);
S := Resolvent(C : Check := true);
assert S`ProjectiveBase and S`_Data`Bundle`Algebra eq [0,5,4,5,5,5];
assert Discriminant(C) eq s^16 and Discriminant(S) eq 4096*s^48;
PP,Q,Zgr,irrelevant := CoxData(S);
assert #Q eq 15;
Ct,phi := CoverPatch(C,2);
St := Resolvent(Ct);
assert BaseRing(St) eq Codomain(phi);
assert StructureConstants(St) eq [phi(v) : v in StructureConstants(S)];
Cf,phi := BaseChange(C,3 : ToField := false);
Sf := Resolvent(Cf : Check := true);
assert Sf`ProjectiveBase and Sf`_Data`Bundle`Algebra eq S`_Data`Bundle`Algebra;
Cg,phi := GenericFibre(C : Homogeneous := false);
Sg := Resolvent(Cg : Check := true);
assert Degree(UnderlyingScheme(Sg)) eq 6;
Cpt,phi := BaseChange(C,GF(2),[1,1]);
assert Degree(UnderlyingScheme(Resolvent(Cpt))) eq 6;
print "no unrequested resolvent choice for an arbitrary quartic algebra";
U<z> := PolynomialRing(Z);
C := FiniteFlatCover(z^4-z-1);
A := FiniteFlatCoverFromStructureConstants(StructureConstants(C),4);
failed := false;
try
    D := Resolvent(A);
catch e
    failed := true;
end try;
assert failed;
print "Resolvent tests completed.";
