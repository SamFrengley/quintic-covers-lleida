// ConjecturalSexticResolvent: opt-in experimental trace-halving order.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/basis.m": FFCBasisTransform;
import "../algebra/invariants.m": FFCAssignResolventRecipe;
import "../core/arithmetic.m": FFCIntegralInverse, FFCIsUnit;
import "characteristic_two.m": FFCCharacteristicTwoCorrection;
import "deferred.m": FFCMaterializeConjectural;
import "envelope.m": FFCIntegralTraceEnvelope;

intrinsic ConjecturalSexticResolvent(C::FinFlatCov : Check := false) -> FinFlatCov
{Experimental trace-halving sextic, explicitly opt-in. See docs/experimental.md for limitations.}
    require Degree(C) eq 5 and C`_Data`Presentation`Kind eq "Bhargava": "A quintic Bhargava tensor is required";
    require Type(Check) eq BoolElt: "Check must be a boolean";
    FFCMaterializeConjectural(C);
    if assigned C`_Data`Resolvents`Conjectural then
        if Check then
            require VerifyResolvent(C : Conjectural := true):
                "The experimental resolvent failed its consistency check";
        end if;
        return C`_Data`Resolvents`Conjectural;
    end if;
    R := BaseRing(C);
    if Characteristic(R) eq 2 then
        V,inc := FFCCharacteristicTwoCorrection(C);
        D := FiniteFlatCoverFromStructureConstants(V,6 : Twisted := C`Twisted, CheckAlgebra := false);
        require Rank(TracePairing(D)) eq 6: "The experimental characteristic-two output is not etale";
        D`_Data`Resolvents`Inclusion := inc;
        D`_Data`Resolvents`Certificate := "Lift, trace-halving, reduction; input and output trace-pairing ranks certified";
        factor := R!1;
    else
        B := BhargavaResolvent(C);
        if FFCIsUnit(R!2) then
            // Over R[1/2] the order is unchanged. Pick a frame of determinant
            // 1/64 so the discriminant SECTION has the corrected normalization.
            N := IdentityMatrix(R,6);
            for i in [2..6] do
                N[i,i] := R!(1/(R!2));
            end for;
            N[2,2] := R!(1/(R!4));
            V := FFCBasisTransform(StructureConstants(B),N,6);
            inc := FFCIntegralInverse(N);
            factor := R!1;
            cert := "Same algebra with 2 invertible; basis determinant 1/64";
        else
            V,N,inc,factor,cert := FFCIntegralTraceEnvelope(B);
        end if;
        D := FiniteFlatCoverFromStructureConstants(V,6 : ProjectiveBase := C`ProjectiveBase,
            Twisted := C`Twisted, AlgebraWeights := B`_Data`Bundle`Algebra, CheckAlgebra := false);
        // Graded constructors check every coefficient; no ungraded Proj frame is silently used.
        D`_Data`Resolvents`BasisChange := N;
        D`_Data`Resolvents`Inclusion := inc;
        D`_Data`Resolvents`Certificate := cert;
    end if;
    D`_Data`Resolvents`SourceDegree := 5;
    D`_Data`Resolvents`Normalization := "ConjecturalTraceHalving";
    FFCAssignResolventRecipe(C,D,factor);
    C`_Data`Resolvents`Conjectural := D;
    if Check then
        require VerifyResolvent(C : Conjectural := true):
            "The experimental resolvent failed its consistency check";
    end if;
    return D;
end intrinsic;

intrinsic ConjecturalResolventCertificate(S::FinFlatCov) -> Tup
{For an experimental sextic already constructed, return <inclusion, factor, description>. Does
 not construct a resolvent.}
    require assigned S`_Data`Resolvents`Certificate: "No experimental resolvent certificate is recorded";
    return <S`_Data`Resolvents`Inclusion,S`_Data`Resolvents`DiscriminantFactor,S`_Data`Resolvents`Certificate>;
end intrinsic;
