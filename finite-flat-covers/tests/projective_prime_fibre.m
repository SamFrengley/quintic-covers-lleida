// Native regression for the reported prime 3*s^2+14*s*t-t^2.
// These are assertions to run in Magma, not an execution transcript.

function PrimeFibreExample(R)
    s,t := Explode([R.1,R.2]);
    U<x> := PolynomialRing(R);
    return x^5-2*(9*t-128*s)*x^4+(9*t-128*s)*(17*t-54*s)*x^3
        -18*(5*t+4*s)*(9*t-128*s)^2*x^2
        -27*(33*t^2-488*t*s-60*s^2)*(9*t-128*s)^2*x
        -27*(27*t^2-92*t*s-3*s^2)*(9*t-128*s)^3;
end function;

procedure CheckPrimeFibreGeometry(B,phi,f)
    R := Domain(phi);
    s := phi(R.1); t := phi(R.2);
    K := BaseRing(B);
    U<z> := PolynomialRing(K);
    fK := &+[phi(Coefficient(f,i))*z^i : i in [0..5]];
    r1 := (17*t-249*s)/4;
    r2 := (141*s-9*t)/4;
    r3 := 14*t-202*s;
    assert fK eq (z-r1)^2*(z-r2)^2*(z-r3);
    assert #SequenceToSet([r1,r2,r3]) eq 3;

    Q := DefiningPolynomials(B);
    assert #Q eq 5 and Rank(Parent(Q[1])) eq 4;
    V := UnderlyingScheme(B);
    P := AmbientSpace(V);
    H := CoordinateRing(P);
    assert Dimension(P) eq 3 and Dimension(V) eq 0 and Degree(V) eq 5;
    assert [Sprint(Name(H,i)) : i in [1..4]] eq
        [Sprintf("X[%o]",i) : i in [1..4]];

    // The user's exact composite operation, not only polynomial evaluations.
    S := ReducedSubscheme(SingularSubscheme(V));
    parts := IrreducibleComponents(S);
    assert #parts eq 2 and Degree(S) eq 2;
    for r in [r1,r2] do
        E := Scheme(P,[H.1-r^3*H.4,H.2-r^2*H.4,H.3-r*H.4]);
        assert exists{W : W in parts | W eq E};
    end for;
    for W in parts do
        assert [Sprint(Name(CoordinateRing(AmbientSpace(W)),i)) : i in [1..4]] eq
            [Sprintf("X[%o]",i) : i in [1..4]];
    end for;
end procedure;

assert FiniteFlatCoverVersion() eq "16.0.1";
for k in [* Integers(),Rationals() *] do
    R<s,t> := PolynomialRing(k,2);
    f := PrimeFibreExample(R);
    pi := 3*s^2+14*s*t-t^2;
    A := FiniteFlatCover(f : CoverDegree := 5, ProjectiveBase := true);

    // Match the reported call order. Known discriminants specialize; no extras run.
    assert Discriminant(f) eq Discriminant(A);
    B,phi := BaseChange(A,pi);
    K := BaseRing(B);
    assert phi(pi) eq 0 and not B`ProjectiveBase;
    assert Type(K) eq FldFun;
    assert phi(s) eq K.1 and phi(t) eq K!BaseRing(K).1;
    assert Sprint(phi(s)) eq "s" and Sprint(phi(t)) eq "t";
    assert phi(s)^2+14/3*phi(s)*phi(t)-1/3*phi(t)^2 eq 0;
    assert assigned B`Discriminant and B`Discriminant eq 0;
    CheckPrimeFibreGeometry(B,phi,f);

    // No extra discriminant or multiplication cache for an uncomputed source.
    C := FiniteFlatCover(f : ProjectiveBase := true);
    D,psi := BaseChange(C,pi);
    Y := UnderlyingScheme(D);
    assert not assigned C`Discriminant and not assigned D`Discriminant;
    assert not assigned C`StructureConstants and not assigned D`StructureConstants;

    // Dehomogenizing is an explicit request for the true Proj residue field.
    D0,psi0 := BaseChange(C,pi : Homogeneous := false);
    assert psi0(t) eq 1 and psi0(pi) eq 0;
    assert Type(BaseRing(D0)) eq FldNum;
    CheckPrimeFibreGeometry(D0,psi0,f);

    // Homogeneous binary input gives exactly the same geometric result.
    U<u,v> := PolynomialRing(R,2);
    fh := &+[Coefficient(f,i)*u^i*v^(5-i) : i in [0..5]];
    Ch := FiniteFlatCover(fh : CoverDegree := 5, ProjectiveBase := true);
    Dh,psih := BaseChange(Ch,pi);
    CheckPrimeFibreGeometry(Dh,psih,f);

    // Coordinate divisors and linear primes must not create spurious extensions.
    Dt,pt := BaseChange(C,t);
    assert pt(t) eq 0 and pt(s) eq BaseRing(Dt).1;
    assert Sprint(pt(s)) eq "s";
    Ds,ps := BaseChange(C,s);
    assert ps(s) eq 0 and ps(t) eq BaseRing(Ds).1;
    assert Sprint(ps(t)) eq "t";
    Dl,pl := BaseChange(C,s-2*t);
    assert pl(s) eq 2*pl(t) and Sprint(pl(t)) eq "t";
    Dt0,pt0 := BaseChange(C,t : Homogeneous := false);
    assert pt0(s) eq 1 and pt0(t) eq 0;
end for;

// The names must come from the supplied base, not hard-coded strings s,t.
R<a,b> := PolynomialRing(Rationals(),2);
f := PrimeFibreExample(R);
C := FiniteFlatCover(f : ProjectiveBase := true);
D,phi := BaseChange(C,3*a^2+14*a*b-b^2);
assert Sprint(phi(a)) eq "a" and Sprint(phi(b)) eq "b";
assert phi(3*a^2+14*a*b-b^2) eq 0;

// A separable prime in small characteristic uses the same homogeneous map.
R<s,t> := PolynomialRing(GF(2),2);
U<x> := PolynomialRing(R);
C := FiniteFlatCover(x^5+s*x^4+t^5 : ProjectiveBase := true);
D,phi := BaseChange(C,s^2+s*t+t^2);
assert phi(s^2+s*t+t^2) eq 0;
assert Sprint(phi(s)) eq "s" and Sprint(phi(t)) eq "t";
assert #DefiningPolynomials(D) eq 5;
assert not assigned C`Discriminant and not assigned D`Discriminant;
print "Projective-prime fibres: homogeneous maps, named ambients and singular components passed.";
