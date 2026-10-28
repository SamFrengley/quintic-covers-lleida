// Tensor and algebra actions, formed over Frac(R) and descended exactly to R.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "characters.m": FFCResolveTwist, FFCTensorActionData;
import "descent.m": FFCActionPolynomialRing, FFCDescendMatrix, FFCDescendPolynomial,
    FFCLiftPolynomialToActionField, FFCIntegralAutomorphismOverR;
import "partial_resolution.m": FFCActPartialResolution;
import "../algebra/basis.m": FFCBasisTransform, FFCTransportAlgebra, FFCTransportQuadratic;
import "../algebra/invariants.m": FFCTransportDiscriminantRecipe;
import "../constructors/rebuild.m": FFCRebuild, FFCRebuildWithWeights;
import "../core/arithmetic.m": FFCDescendElement;
import "../core/grading.m": FFCPrepareActionMatrixWithWeights, FFCRationalDegree;
import "../models/forms.m": FFCTransformQuadratic;
import "../resolvents/deferred.m": FFCTransportResolvent;

procedure FFCAssignTransportedScalar(~D,C,chi)
    R := BaseRing(C);
    if assigned C`Discriminant then
        D`Discriminant := FFCDescendElement(chi*C`Discriminant,R,
            "transformed discriminant");
    end if;
    FFCTransportDiscriminantRecipe(C,D,chi);
    if assigned C`_Data`Algebra`TraceDiscriminant then
        D`_Data`Algebra`TraceDiscriminant := FFCDescendElement(
            chi*C`_Data`Algebra`TraceDiscriminant,R,"transformed trace discriminant");
    end if;
end procedure;

intrinsic ActBy(C::FinFlatCov,g::Mtrx,h::Mtrx : Twisted := "Stored") -> FinFlatCov
{Left tensor action, object first. Matrices may be over R or Frac(R). The result is returned only
 when every transformed model coefficient descends to R; homogeneous generic matrices may change the stored splitting type.}
    n := Degree(C);
    R := BaseRing(C);
    projective := C`ProjectiveBase;
    tw := FFCResolveTwist(C,Twisted);
    if C`_Data`Presentation`Kind eq "Resolution" then
        if #C`Model eq 1 and Degree(C) ge 6 then
            return FFCActPartialResolution(C,g,h,tw);
        end if;
        F := ResolutionMaps(C);
        H := [* IdentityMatrix(R,Ncols(A)) : A in F *];
        H[1] := Transpose(h);
        return ActBy(C,g,H : Twisted := tw);
    end if;
    require C`_Data`Presentation`Kind eq "Bhargava" and n in {4,
        5}: "The two-matrix tensor action requires degree 4 or 5";
    gK,hK,s,L,chi,wnew,qnew,rnew,tnew := FFCTensorActionData(C,g,h,tw);
    K := BaseRing(gK);
    if n eq 4 then
        AA := [FFCTransformQuadratic(ChangeRing(A,K),gK) : A in C`Model];
        MK := [s*(&+[hK[i,j]*AA[j] : j in [1..2]]) : i in [1..2]];
    else
        AA := [gK*ChangeRing(A,K)*Transpose(gK) : A in C`Model];
        MK := [s*(&+[hK[i,j]*AA[j] : j in [1..4]]) : i in [1..4]];
    end if;
    M := [FFCDescendMatrix(MK[i],R,Sprintf("transformed model matrix %o",i))
        : i in [1..#MK]];
    // Rebuild with the target splitting type inferred from the homogeneous generic action.
    D := FFCRebuildWithWeights(C,M,R,projective,wnew,qnew,rnew,tnew,[],[]);
    D`Twisted := tw;
    FFCAssignTransportedScalar(~D,C,chi);

    // Cached algebra/resolvent transport is valid only for a genuine integral
    // basis automorphism.  Otherwise the new integral model recomputes lazily.
    okL,LR := FFCIntegralAutomorphismOverR(L,R);
    if okL then
        FFCTransportAlgebra(C,D,LR);
    end if;
    okg,gR := FFCIntegralAutomorphismOverR(gK,R);
    okh,hR := FFCIntegralAutomorphismOverR(hK,R);
    if okg and okh then
        FFCTransportResolvent(C,D,gR,hR,R!s);
    end if;
    return D;
end intrinsic;

intrinsic ActBy(C::FinFlatCov,g::Mtrx : Twisted := "Stored") -> FinFlatCov
{Single-factor action. Fraction-field matrices are allowed when the transformed model descends
 integrally and respects the grading.}
    n := Degree(C);
    R := BaseRing(C);
    tw := FFCResolveTwist(C,Twisted);
    if C`_Data`Presentation`Kind eq "Resolution" then
        if #C`Model eq 1 and Degree(C) ge 6 then
            h := IdentityMatrix(R,Ncols(C`Model[1]));
            return FFCActPartialResolution(C,g,h,tw);
        end if;
        F := ResolutionMaps(C);
        H := [* IdentityMatrix(R,Ncols(A)) : A in F *];
        return ActBy(C,g,H : Twisted := tw);
    end if;
    if C`_Data`Presentation`Kind eq "Algebra" then
        gK,awtail := FFCPrepareActionMatrixWithWeights(g,R,C`_Data`Bundle`Algebra[2..n],C`ProjectiveBase,false);
        K := BaseRing(gK);
        B := IdentityMatrix(K,n);
        for i,j in [1..n-1] do
            B[i+1,j+1] := gK[i,j];
        end for;
        TK := FFCBasisTransform([K!a : a in StructureConstants(C)],B,n);
        T := [FFCDescendElement(a,R,"transformed structure constant") : a in TK];
        D := FFCRebuildWithWeights(C,T,R,C`ProjectiveBase,[],[],[],0,[],[0] cat awtail);
        D`Twisted := tw;
        chi := Determinant(gK)^2;
        FFCAssignTransportedScalar(~D,C,chi);
        okB,BR := FFCIntegralAutomorphismOverR(B,R);
        if okB then
            D`_Data`Algebra`BasisChange := BR;
        end if;
        return D;
    end if;
    require C`_Data`Presentation`Kind ne "BinaryAlgebra":
        "For this higher binary algebra, first request StructureConstants and use FiniteFlatCoverFromStructureConstants";
    if n in {2,3} then
        gK,wnew := FFCPrepareActionMatrixWithWeights(g,R,C`_Data`Bundle`Variables,C`ProjectiveBase,true);
        K := BaseRing(gK);
        P := Parent(C`Model);
        Q := FFCActionPolynomialRing(P,K);
        fK := FFCLiftPolynomialToActionField(C`Model,Q);
        xx := [&+[gK[i,j]*Q.i : i in [1..2]] : j in [1..2]];
        s := tw select Determinant(gK)^-1 else K!1;
        ds := 0;
        if C`ProjectiveBase then
            ok,ds := FFCRationalDegree(s,R);
            if not ok then
                error "The determinant twist is not a homogeneous rational function";
            end if;
        end if;
        MK := s*Evaluate(fK,xx);
        M := FFCDescendPolynomial(MK,P,"transformed binary form");
        qnew := [C`_Data`Bundle`Equations[1]+ds];
        D := FFCRebuildWithWeights(C,M,R,C`ProjectiveBase,wnew,qnew,[],0,[],[]);
        D`Twisted := tw;
        chi := s^(2*n-2)*Determinant(gK)^(n*(n-1));
        FFCAssignTransportedScalar(~D,C,chi);
        okg,gR := FFCIntegralAutomorphismOverR(gK,R);
        if okg then
            if n eq 2 then
                FFCTransportQuadratic(C,D,gR,R!s);
            else
                FFCTransportAlgebra(C,D,R!(s*Determinant(gK))*gR);
            end if;
        end if;
        return D;
    end if;
    require n in {4,5}: "The identity cover has no tensor action";
    if n eq 4 then
        if Nrows(g) eq 3 then
            return ActBy(C,g,IdentityMatrix(R,2) : Twisted := tw);
        end if;
        require Nrows(g) eq 2: "A quartic factor has size 3 or 2";
        return ActBy(C,IdentityMatrix(R,3),g : Twisted := tw);
    end if;
    if Nrows(g) eq 5 then
        return ActBy(C,g,IdentityMatrix(R,4) : Twisted := tw);
    end if;
    require Nrows(g) eq 4: "A quintic factor has size 5 or 4";
    return ActBy(C,IdentityMatrix(R,5),g : Twisted := tw);
end intrinsic;
