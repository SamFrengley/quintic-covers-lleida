// Standard cubic/quartic/quintic resolvents. No experimental default.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/invariants.m": FFCAssignResolventRecipe;
import "../algebra/tables.m": FFCGet;
import "deferred.m": FFCMaterializeResolvent;
import "minors.m": FFCSexticResolventConstants;

function FFCCubicCoefficientsForResolvent(C)
    if C`_Data`Presentation`Kind eq "Bhargava" then
        f := C`Model;
        P := Parent(f);
        return [MonomialCoefficient(f,P.1^(3-i)*P.2^i) : i in [0..3]];
    end if;
    // Translate any cubic unit basis to the Delone--Faddeev normalization.
    // The translation has determinant 1 and uses no division.
    T := StructureConstants(C);
    return [-FFCGet(T,3,1,1,2),
        FFCGet(T,3,1,1,1)-2*FFCGet(T,3,1,2,2),
        -FFCGet(T,3,2,2,2)+2*FFCGet(T,3,1,2,1),
        FFCGet(T,3,2,2,1)];
end function;

intrinsic ResolventDegree(C::FinFlatCov) -> RngIntElt
{The next resolvent degree: 3->2, 4->3, 5->6.}
    require Degree(C) in {3,4,5}: "Resolvents are implemented for source degrees 3, 4 and 5";
    return Degree(C) eq 3 select 2 else (Degree(C) eq 4 select 3 else 6);
end intrinsic;

intrinsic BhargavaResolvent(C::FinFlatCov) -> FinFlatCov
{The historical integral sextic order, without the characteristic-two correction. Cached
 separately; never computes a discriminant.}
    require Degree(C) eq 5 and C`_Data`Presentation`Kind eq "Bhargava": "A quintic Bhargava tensor is required";
    FFCMaterializeResolvent(C);
    if assigned C`_Data`Resolvents`Standard then
        return C`_Data`Resolvents`Standard;
    end if;
    R := BaseRing(C);
    T := FFCSexticResolventConstants(C);
    if C`ProjectiveBase then
        e := 12*C`_Data`Bundle`Twist+5*(&+C`_Data`Bundle`Rows)-3*(&+C`_Data`Bundle`Variables);
        aw := [0] cat [e-r : r in C`_Data`Bundle`Rows];
    else
        aw := [0 : i in [1..6]];
    end if;
    D := FiniteFlatCoverFromStructureConstants(T,6 : ProjectiveBase := C`ProjectiveBase,
        Twisted := C`Twisted, AlgebraWeights := aw, CheckAlgebra := false);
    D`_Data`Resolvents`SourceDegree := 5;
    D`_Data`Resolvents`Normalization := "Bhargava";
    FFCAssignResolventRecipe(C,D,R!4096);
    C`_Data`Resolvents`Standard := D;
    return D;
end intrinsic;

intrinsic Resolvent(C::FinFlatCov : Check := false) -> FinFlatCov
{Return the standard quadratic, cubic or Bhargava sextic resolvent. Never computes a
 discriminant.}
    require Type(Check) eq BoolElt: "Check must be a boolean";
    n := Degree(C);
    m := ResolventDegree(C);
    R := BaseRing(C);
    require n eq 3 or C`_Data`Presentation`Kind eq "Bhargava":
        "Quartic/quintic resolvents require their Bhargava tensor, which includes the resolvent choice";
    if n eq 5 then
        D := BhargavaResolvent(C);
        if Check then
            require VerifyResolvent(C): "The resolvent failed the algebra consistency check";
        end if;
        return D;
    end if;
    FFCMaterializeResolvent(C);
    if not assigned C`_Data`Resolvents`Standard then
        if n eq 3 then
            a,b,c,d := Explode(FFCCubicCoefficientsForResolvent(C));
            tr := b*c-9*a*d;
            norm := a*c^3+b^3*d+27*a^2*d^2-9*a*b*c*d;
            P<u,v> := PolynomialRing(R,2);
            f := u^2-tr*u*v+norm*v^2;
            if C`ProjectiveBase then
                e := &+C`_Data`Bundle`Algebra;
                w := [e,0];
                q := [2*e];
            else
                w := [];
                q := [];
            end if;
            D := FiniteFlatCover(f : CoverDegree := m, ProjectiveBase := C`ProjectiveBase, Twisted := C`Twisted,
                VariableWeights := w, EquationWeights := q);
            D`_Data`Resolvents`Normalization := "Integral discriminant algebra; generator trace bc-9ad";
        else
            P<u,v> := PolynomialRing(R,2);
            A,B := Explode(C`Model);
            T := Matrix(P,3,3,[u*A[i,j]+v*B[i,j] : i,j in [1..3]]);
            f := 4*T[1,1]*T[2,2]*T[3,3]+T[1,2]*T[1,3]*T[2,3]
            -T[1,1]*T[2,3]^2-T[2,2]*T[1,3]^2-T[3,3]*T[1,2]^2;
            if C`ProjectiveBase then
                w := [-a : a in C`_Data`Bundle`Equations];
                q := [-2*(&+C`_Data`Bundle`Variables)];
            else
                w := [];
                q := [];
            end if;
            D := FiniteFlatCover(f : CoverDegree := m, ProjectiveBase := C`ProjectiveBase, Twisted := C`Twisted,
                VariableWeights := w, EquationWeights := q);
            D`_Data`Resolvents`Normalization := "Wood: 4 det(Gram(uA+vB))";
        end if;
        D`_Data`Resolvents`SourceDegree := n;
        if assigned C`Discriminant then
            D`Discriminant := C`Discriminant;
        end if;
        C`_Data`Resolvents`Standard := D;
    end if;
    if Check then
        require VerifyResolvent(C): "The resolvent failed the algebra consistency check";
    end if;
    return C`_Data`Resolvents`Standard;
end intrinsic;

intrinsic QuadraticResolvent(C::FinFlatCov : Check := false) -> FinFlatCov
{Alias of Resolvent for a cubic cover.}
    require Degree(C) eq 3: "QuadraticResolvent requires a cubic cover";
    return Resolvent(C : Check := Check);
end intrinsic;

intrinsic CubicResolvent(C::FinFlatCov : Check := false) -> FinFlatCov
{Alias of Resolvent for a Bhargava quartic model.}
    require Degree(C) eq 4: "CubicResolvent requires a quartic cover";
    return Resolvent(C : Check := Check);
end intrinsic;

intrinsic SexticResolvent(C::FinFlatCov : Check := false) -> FinFlatCov
{The standard Bhargava sextic. Use ConjecturalSexticResolvent for the experimental alternative.}
    require Degree(C) eq 5: "SexticResolvent requires a quintic cover";
    return Resolvent(C : Check := Check);
end intrinsic;
