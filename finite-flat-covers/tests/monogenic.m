/* Native tests. Run after AttachSpec("spec"). Not executed in the authoring environment. */
load "tests/monogenic_helpers.m";
load "tests/fixtures/monogenic_6_mixed.m";
load "tests/fixtures/monogenic_6_nilpotent.m";
load "tests/fixtures/monogenic_7_mixed.m";
load "tests/fixtures/monogenic_7_nilpotent.m";
print "explicit quotient-ring isomorphisms, including nilpotent rings";
Z := Integers();
U<z> := PolynomialRing(Z);
for n in [2..5] do
    for f in [z^n-z-1,z^n,(z-1)^n,z^n+2*z^(n-1)+3*z+4] do
        C := FiniteFlatCover(f);
        assert Type(C) eq FinFlatCov and IsTwisted(C);
        assert not assigned C`StructureConstants;
        B := CheckMonogenicIsomorphism(C,f,TestCoordinates(f));
        assert Abs(Determinant(B)) eq 1;
        CheckMonogenicChart(C,f,TestCoordinates(f));
        /* Rebuild from the embedded tensor, with no polynomial metadata or
           copied multiplication table, then compare ALL products again. */
        Fresh := FiniteFlatCover(Model(C));
        assert not assigned Fresh`StructureConstants;
        BF := CheckMonogenicIsomorphism(Fresh,f,TestCoordinates(f));
        assert BF eq B and StructureConstants(Fresh) eq StructureConstants(C);
        for p in [2,3,5,7] do
            D,phi := BaseChange(C,p);
            V<t> := PolynomialRing(GF(p));
            fp := V![phi(Coefficient(f,i)) : i in [0..n]];
            Fresh := FiniteFlatCover(Model(D));
            BP := CheckMonogenicIsomorphism(Fresh,fp,TestCoordinates(fp));
            assert StructureConstants(Fresh) eq StructureConstants(D);
            CheckMonogenicChart(Fresh,fp,TestCoordinates(fp));
        end for;
    end for;
end for;
print "monogenic comparisons over Z[u], without fraction-field substitution";
R<u> := PolynomialRing(Z);
U<z> := PolynomialRing(R);
for n in [2..5] do
    f := z^n+u*z^(n-1)+(u^2+1)*z+u+2;
    C := FiniteFlatCover(f);
    B := CheckMonogenicIsomorphism(C,f,TestCoordinates(f));
    assert BaseRing(B) eq R and TestUnit(Determinant(B));
    F<X,Y> := PolynomialRing(R,2);
    fh := &+[(F!Coefficient(f,i))*X^i*Y^(n-i) : i in [0..n]];
    D := FiniteFlatCover(fh);
    assert StructureConstants(C) eq StructureConstants(D);
end for;
print "explicit degree-six and degree-seven resolution tables vs polynomial quotients";
U<z> := PolynomialRing(Z);
for n in [6,7] do
    for nilpotent in [false,true] do
        if n eq 6 then
            F := nilpotent select MonogenicResolution6_nilpotent(Z) else MonogenicResolution6_mixed(Z);
        else
            F := nilpotent select MonogenicResolution7_nilpotent(Z) else MonogenicResolution7_mixed(Z);
        end if;
        f := nilpotent select z^n else z^n+2*z^(n-2)-3*z^2+z+1;
        C := FiniteFlatCover(F : AssumeFiniteFlat := true);
        B := CheckMonogenicIsomorphism(C,f,TestCoordinates(f));
        CheckMonogenicChart(C,f,TestCoordinates(f));
        for p in [2,3,5,7] do
            D,phi := BaseChange(C,p);
            /* Reconstruct from specialized resolution matrices, so the FR
               formulas are executed IN characteristic p, not just reduced. */
            Fresh := FiniteFlatCover(Model(D) : AssumeFiniteFlat := true);
            V<t> := PolynomialRing(GF(p));
            fp := V![phi(Coefficient(f,i)) : i in [0..n]];
            BP := CheckMonogenicIsomorphism(Fresh,fp,TestCoordinates(fp));
            assert StructureConstants(Fresh) eq StructureConstants(D);
        end for;
        /* Exercise the new polynomial constructor and native completion too. */
        E := FiniteFlatCover(f : Embedding := "Model");
        assert not assigned E`_Data`Resolution`Maps;
        Q := DefiningPolynomials(E);
        assert not assigned E`_Data`Resolution`Maps;
        BE := CheckMonogenicIsomorphism(E,f,TestCoordinates(f));
        assert Abs(Determinant(BE)) eq 1;
    end for;
end for;
print "polynomial input edge cases retain homogeneous degree";
R := Rationals();
P<X,Y> := PolynomialRing(R,2);
U<z> := PolynomialRing(R);
for n in [2..7] do
    C := FiniteFlatCover(Y^n );
    assert Degree(C) eq n and IsAssociative(C) and Discriminant(C) eq 0;
    E := FiniteFlatCover(U!1 : CoverDegree := n);
    assert Degree(E) eq n and StructureConstants(E) eq StructureConstants(C);
end for;
P<x> := PolynomialRing(Z,1);
C := FiniteFlatCover(x^3-x-1);
assert Degree(C) eq 3;
P<X,Y> := PolynomialRing(Z,2);
C := FiniteFlatCover(P!0 : CoverDegree := 7);
assert Degree(C) eq 7 and Discriminant(C) eq 0;
C := FiniteFlatCover(2*X^6+2*Y^6);
assert C`_Data`Presentation`Kind eq "Algebra" and IsAssociative(C) and Degree(C) eq 6;
failed := false;
try
    C := FiniteFlatCover(X^3+Y+1);
catch e
    failed := true;
end try;
assert failed;
print "Monogenic tests passed.";
