// Base changes at rational and polynomial primes.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/maps.m": FFCCoefficientImage, FFCMapWithImages;
import "../core/names.m": FFCBaseCoordinateNames, FFCNamedExtension,
    FFCNamedFunctionField, FFCNamedPolynomialRing;

function FFCGroundField(R)
    k := BaseRing(R);
    if Type(k) eq RngInt then
        return Rationals();
    end if;
    if not IsField(k) then
        error "The prime-fibre backend needs Z or a field as the ground ring";
    end if;
    return k;
end function;

function FFCPolynomialPrimeMap(C,pi,homogeneous)
    if pi eq 0 then
        error "The zero polynomial does not define a prime divisor";
    end if;
    R := BaseRing(C);
    names := FFCBaseCoordinateNames(R);
    k := FFCGroundField(R);
    n := Type(R) eq RngUPol select 1 else Rank(R);
    if n notin {1,2} then
        error "Polynomial-prime fibres are implemented for one or two base variables";
    end if;
    if Type(BaseRing(R)) eq RngInt then
        ct := GCD([Integers()!a : a in Coefficients(pi)]);
        if Abs(ct) ne 1 then
            error "The polynomial prime must be primitive over Z";
        end if;
    end if;
    if n eq 1 then
        U := FFCNamedPolynomialRing(k,1,names);
        g := FFCCoefficientImage(pi,[U.1],U);
        if Degree(g) le 0 or not IsIrreducible(g) then
            error "Expected a nonconstant irreducible polynomial";
        end if;
        K,a := FFCNamedExtension(k,g,names[1]);
        return FFCMapWithImages(R,K,[a]);
    end if;

    P := FFCNamedPolynomialRing(k,2,names);
    f := FFCCoefficientImage(pi,[P.1,P.2],P);
    if Degree(f) le 0 or not IsIrreducible(f) then
        error "Expected a nonconstant irreducible polynomial";
    end if;

    if C`ProjectiveBase then
        if not IsHomogeneous(pi) then
            error "A prime on Proj must be homogeneous";
        end if;
        if homogeneous then
            /* Use the ACTUAL homogeneous coordinates, not a ratio called s.
               For pi(s,t), this is k(t)[s]/(pi(s,t)); the returned images
               satisfy pi and retain simultaneous base degree one.
               The prime (t) is the only homogeneous case with deg_s pi = 0. */
            if Degree(f,1) eq 0 then
                K := FFCNamedFunctionField(k,1,[names[1]]);
                return FFCMapWithImages(R,K,[K.1,K!0]);
            end if;
            F := FFCNamedFunctionField(k,1,[names[2]]);
            U := FFCNamedPolynomialRing(F,1,[names[1]]);
            g := Evaluate(f,[U.1,U!F.1]);
            if Degree(g) gt 1 and Derivative(g) eq 0 then
                error "This function-field backend requires a separable polynomial prime; use an explicit coefficient map for an inseparable prime";
            end if;
            K,a := FFCNamedExtension(F,g,names[1]);
            return FFCMapWithImages(R,K,[a,K!F.1]);
        end if;

        /* The genuine Proj residue field is the degree-zero field.
           Here the name s denotes the affine chart coordinate s/t,
           but t is SET TO ONE, not retained as another field variable. */
        U := FFCNamedPolynomialRing(k,1,[names[1]]);
        g := Evaluate(f,[U.1,U!1]);
        if Degree(g) eq 0 then
            return FFCMapWithImages(R,k,[k!1,k!0]);
        end if;
        K,a := FFCNamedExtension(k,g,names[1]);
        return FFCMapWithImages(R,K,[a,K!1]);
    end if;

    /* Affine bivariate prime: retain the original coordinate names in the tower. */
    if Degree(f,2) eq 0 then
        U := FFCNamedPolynomialRing(k,1,[names[1]]);
        g := Evaluate(f,[U.1,U!0]);
        k0,a := FFCNamedExtension(k,g,names[1]);
        K := FFCNamedFunctionField(k0,1,[names[2]]);
        return FFCMapWithImages(R,K,[K!a,K.1]);
    end if;
    F := FFCNamedFunctionField(k,1,[names[1]]);
    U := FFCNamedPolynomialRing(F,1,[names[2]]);
    g := Evaluate(f,[U!F.1,U.1]);
    K,b := FFCNamedExtension(F,g,names[2]);
    return FFCMapWithImages(R,K,[K!F.1,b]);
end function;

intrinsic BaseChange(C::FinFlatCov, p::RngIntElt : ToField := true, Homogeneous := true) -> FinFlatCov,
    Map
{Reduce modulo a rational prime. Base-variable names are preserved. Proj: homogeneous field by
 default, genuine residue field with Homogeneous := false.}
    require IsPrime(p): "The integer must be a positive rational prime";
    R := BaseRing(C);
    F := GF(p);
    if Type(R) eq RngInt then
        phi := FFCMapWithImages(R,F,[]);
        D,phi := BaseChange(C,phi);
    else
        require Type(R) in {RngUPol,RngMPol} and Type(BaseRing(R)) eq RngInt:
            "Rational-prime reduction requires an integral coefficient ring, not Q or a characteristic-zero field";
        n := Type(R) eq RngUPol select 1 else Rank(R);
        names := FFCBaseCoordinateNames(R);
        if not ToField then
            S := FFCNamedPolynomialRing(F,n,names);
            phi := FFCMapWithImages(R,S,[S.i : i in [1..n]]);
            D,phi := BaseChange(C,phi : PreserveGrading := C`ProjectiveBase);
        elif C`ProjectiveBase and not Homogeneous then
            K := FFCNamedFunctionField(F,1,[names[1]]);
            phi := FFCMapWithImages(R,K,[K.1,K!1]);
            D,phi := BaseChange(C,phi);
        else
            K := FFCNamedFunctionField(F,n,names);
            phi := FFCMapWithImages(R,K,[K.i : i in [1..n]]);
            D,phi := BaseChange(C,phi);
        end if;
    end if;
    return D,phi;
end intrinsic;

intrinsic BaseChange(C::FinFlatCov, pi::RngMPolElt : Homogeneous := true) -> FinFlatCov, Map
{Field fibre at a primitive irreducible polynomial. On Proj: Homogeneous := true retains
 the original homogeneous coordinates in Frac(k[s,t]/(pi)); false takes the chart residue field.}
    require Parent(pi) eq BaseRing(C): "The prime polynomial must belong to the coefficient ring";
    if pi ne 0 and Degree(pi) eq 0 and Type(BaseRing(Parent(pi))) eq RngInt then
        return BaseChange(C,Abs(Integers()!Coefficients(pi)[1]) : Homogeneous := Homogeneous);
    end if;
    phi := FFCPolynomialPrimeMap(C,pi,Homogeneous);
    D,phi := BaseChange(C,phi);
    return D,phi;
end intrinsic;

intrinsic BaseChange(C::FinFlatCov, pi::RngUPolElt : Homogeneous := true) -> FinFlatCov, Map
{Field fibre at a primitive irreducible polynomial in one base variable.}
    require Parent(pi) eq BaseRing(C): "The prime polynomial must belong to the coefficient ring";
    if Degree(pi) eq 0 and Type(BaseRing(Parent(pi))) eq RngInt then
        return BaseChange(C,Abs(Integers()!Coefficient(pi,0)) : Homogeneous := Homogeneous);
    end if;
    phi := FFCPolynomialPrimeMap(C,pi,Homogeneous);
    D,phi := BaseChange(C,phi);
    return D,phi;
end intrinsic;

intrinsic BaseChange(C::FinFlatCov, K::Fld, values::SeqEnum) -> FinFlatCov, Map
{Evaluation fibre, including a closed point above a rational prime. Proj coordinates must not
 both vanish.}
    R := BaseRing(C);
    require Type(R) in {RngUPol,RngMPol}: "Evaluation requires a polynomial base ring";
    n := Type(R) eq RngUPol select 1 else Rank(R);
    require #values eq n: "Supply one value per base variable";
    vals := [K!a : a in values];
    require not C`ProjectiveBase or exists{a : a in vals | a ne 0}:
        "[0:0] is not a projective base point";
    phi := FFCMapWithImages(R,K,vals);
    D,phi := BaseChange(C,phi);
    return D,phi;
end intrinsic;
