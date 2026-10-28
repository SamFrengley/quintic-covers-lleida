/* Native experimental-resolvent tests. Supplied for Magma; NOT executed during authoring. */
procedure AssertNoDiscriminant(C)
    assert not assigned C`Discriminant;
    assert not assigned C`_Data`Algebra`TraceDiscriminant;
    if assigned C`_Data`Resolvents`Conjectural then
        D := C`_Data`Resolvents`Conjectural;
        assert not assigned D`Discriminant and not assigned D`_Data`Algebra`TraceDiscriminant;
    end if;
    if assigned C`_Data`Resolvents`Standard then
        B := C`_Data`Resolvents`Standard;
        assert not assigned B`Discriminant and not assigned B`_Data`Algebra`TraceDiscriminant;
    end if;
end procedure;
function SplitQuinticTensor(R)
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
print "no first discriminant calculation through algebra, geometry, actions or resolvents";
Z := Integers();
P<z> := PolynomialRing(Z);
for n in [2..5] do
    C := FiniteFlatCover(z^n-z-1);
    T := StructureConstants(C);
    Q := DefiningPolynomials(C);
    AssertNoDiscriminant(C);
    if n gt 2 then
        E := Resolvent(C : Check := true);
        AssertNoDiscriminant(C);
        assert VerifyResolvent(C);
        AssertNoDiscriminant(C);
    end if;
    if n le 3 then
        g := IdentityMatrix(Z,2);
        g[1,2] := 1;
        D := C^g;
    elif n eq 4 then
        g := IdentityMatrix(Z,3);
        g[1,2] := 1;
        D := C^g;
    else
        g := IdentityMatrix(Z,5);
        g[1,2] := 1;
        D := C^g;
    end if;
    AssertNoDiscriminant(C);
    AssertNoDiscriminant(D);
    E,phi := BaseChange(D,2);
    X := UnderlyingScheme(E);
    AssertNoDiscriminant(E);
    ActBy(~C,g);
    AssertNoDiscriminant(C);
    d := Discriminant(C);
    assert assigned C`Discriminant;
    D := C^g;
    assert D`Discriminant eq d;
end for;
print "split sextic is Z^6, rather than its index-64 suborder";
C := FiniteFlatCover(SplitQuinticTensor(Z));
S := ConjecturalSexticResolvent(C : Check := true);
B := BhargavaResolvent(C);
AssertNoDiscriminant(C);
Images := Matrix(Rationals(),6,6,[
    1,1,1,1,1,1, -1,1,-1,-1,1,-1, -1,1,1,-1,-1,-1,
    -1,-1,1,1,-1,-1, -1,-1,-1,1,-1,1, -1,-1,-1,-1,1,1]);
NewImages := S`_Data`Resolvents`BasisChange*Images;
assert Abs(Determinant(NewImages)) eq 1 and forall{a : a in Eltseq(NewImages) | IsIntegral(a)};
T := StructureConstants(S);
for i,j in [0..5] do
    for a in [1..6] do
        assert NewImages[i+1,a]*NewImages[j+1,a] eq
        &+[T[(i*6+j)*6+k+1]*NewImages[k+1,a] : k in [0..5]];
    end for;
end for;
assert Discriminant(S) eq 1 and Discriminant(B) eq 4096;
assert VerifyResolvent(C : Conjectural := true, CheckDiscriminant := true);
print "good reduction, not merely a formally divided discriminant";
C := FiniteFlatCover(z^5-z-1);
S := ConjecturalSexticResolvent(C);
B := BhargavaResolvent(C);
AssertNoDiscriminant(C);
Cp,phi := BaseChange(C,2);
Sp := ConjecturalSexticResolvent(Cp);
Bp := BhargavaResolvent(Cp);
assert StructureConstants(Sp) eq [phi(a) : a in StructureConstants(S)];
assert Rank(TracePairing(Sp)) eq 6 and Rank(TracePairing(Bp)) lt 6;
assert IsEmpty(SingularSubscheme(UnderlyingScheme(Sp)));
AssertNoDiscriminant(Cp);
assert Discriminant(C) eq 2869 and Discriminant(S) eq 2869^3;
assert Discriminant(B) eq 4096*2869^3;
print "fresh characteristic-two construction from the original tensor";
for d in [1,2,3] do
    K := GF(2^d);
    U<x> := PolynomialRing(K);
    C := FiniteFlatCover(x^5-x-1);
    S := ConjecturalSexticResolvent(C : Check := true);
    assert Rank(TracePairing(S)) eq 6 and IsAssociative(S);
    AssertNoDiscriminant(C);
    assert VerifyResolvent(C : Conjectural := true, CheckDiscriminant := true);
end for;
for d in [1,2] do
    K := FunctionField(GF(2),d);
    U<x> := PolynomialRing(K);
    C := FiniteFlatCover(x^5-x-K.1);
    S := ConjecturalSexticResolvent(C : Check := true);
    assert Rank(TracePairing(S)) eq 6;
    AssertNoDiscriminant(C);
end for;
K := GF(2);
U<x> := PolynomialRing(K);
C := FiniteFlatCover(x^5);
failed := false;
try
    S := ConjecturalSexticResolvent(C);
catch e
    failed := true;
end try;
assert failed;
// No claim of lift-independent reconstruction on the degenerate locus.
assert Degree(BhargavaResolvent(C)) eq 6;
print "Z[u] and explicit distinction between specialization and fresh saturation";
R<u> := PolynomialRing(Z);
U<x> := PolynomialRing(R);
C := FiniteFlatCover(x^5-x-u);
S := ConjecturalSexticResolvent(C : Check := true);
assert BaseRing(S) eq R and S`_Data`Resolvents`DiscriminantFactor eq 1;
AssertNoDiscriminant(C);
C2,phi := BaseChange(C,2);
S2 := ConjecturalSexticResolvent(C2);
assert Rank(TracePairing(S2)) eq 6;
AssertNoDiscriminant(C2);
ev := hom<R -> Z | 0>;
C0,phi := BaseChange(C,ev);
S0 := ConjecturalSexticResolvent(C0);
Fresh := FiniteFlatCover(P.1^5-P.1);
FreshS := ConjecturalSexticResolvent(Fresh);
assert S0`_Data`Resolvents`DiscriminantFactor eq 1 and FreshS`_Data`Resolvents`DiscriminantFactor eq 4;
assert Discriminant(FreshS) eq 4*Discriminant(S0);
print "one-variable multivariate coefficient parent";
Rm<v> := PolynomialRing(Z,1);
Um<x> := PolynomialRing(Rm);
Cm := FiniteFlatCover(x^5+v*x^4+v^2*x^3+(v+1)*x^2+v*x+(v+1));
Sm := ConjecturalSexticResolvent(Cm : Check := true);
assert BaseRing(Sm) eq Rm and Sm`_Data`Resolvents`DiscriminantFactor eq 1;
AssertNoDiscriminant(Cm);
print "experimental integral action is a lattice isomorphism";
C := FiniteFlatCover(P.1^5-P.1-1);
S := ConjecturalSexticResolvent(C);
H := TracePairing(S);
g := IdentityMatrix(Z,5);
g[1,2] := 1;
g[3,5] := -1;
h := IdentityMatrix(Z,4);
h[2,3] := 1;
D := C^<g,h>;
E := ConjecturalSexticResolvent(D);
AssertNoDiscriminant(C);
AssertNoDiscriminant(D);
_ := AlgebraBasisChange(E);
J := AlgebraBasisChange(E);
assert Abs(Determinant(J)) eq 1 and TracePairing(E) eq J*H*Transpose(J);
print "Proj atlas, without inventing a global split frame";
R<s,t> := PolynomialRing(Z,2);
rw := [0,1,0,0,0];
A := SplitQuinticTensor(R);
A := [Matrix(R,5,5,[M[i,j]*s^(rw[i]+rw[j]) : i,j in [1..5]]) : M in A];
C := FiniteFlatCover(A : ProjectiveBase := true,VariableWeights := [0,0,0,0],RowWeights := rw);
Atlas := ConjecturalSexticResolventCharts(C);
A1,A2,J := Explode(Atlas);
assert Degree(A1) eq 6 and Degree(A2) eq 6 and Nrows(J) eq 6;
assert IsAssociative(A1) and IsAssociative(A2);
AssertNoDiscriminant(C);
print "Conjectural-resolvent tests completed.";
