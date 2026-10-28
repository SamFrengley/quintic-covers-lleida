// Full resolution actions over the generic coefficient field, followed by exact descent.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "characters.m": FFCResolveTwist;
import "descent.m": FFCActionPolynomialRing, FFCDescendPolynomialMatrix,
    FFCLiftPolynomialToActionField, FFCIntegralAutomorphismOverR;
import "../algebra/basis.m": FFCTransportAlgebra;
import "../algebra/invariants.m": FFCTransportDiscriminantRecipe;
import "../constructors/rebuild.m": FFCRebuildWithWeights;
import "../core/arithmetic.m": FFCDescendElement;
import "../core/grading.m": FFCPrepareActionMatrixWithWeights;

intrinsic ActBy(C::FinFlatCov,g::Mtrx,H::List : Twisted := "Stored") -> FinFlatCov
{Resolution action Phi_i'=B_(i-1)^(-1) Phi_i(g^t x) B_i. Matrices may lie in Frac(R);
 every transformed map must descend to R; homogeneous generic matrices may change the split bundle weights.}
    require C`_Data`Presentation`Kind eq "Resolution": "A list action requires a resolution model";
    tw := FFCResolveTwist(C,Twisted);
    n := Degree(C);
    R := BaseRing(C);
    F := ResolutionMaps(C);
    require #H eq #F: "Supply a basis matrix for every resolution module after F_0";

    gK,wnew := FFCPrepareActionMatrixWithWeights(g,R,C`_Data`Bundle`Variables,C`ProjectiveBase,true);
    HH := [* *];
    for i in [1..#H] do
        Hi,target := FFCPrepareActionMatrixWithWeights(H[i],R,C`_Data`Resolution`Weights[i+1],C`ProjectiveBase,true);
        Append(~HH,Hi);
    end for;
    K := BaseRing(gK);
    P := BaseRing(F[1]);
    Q := FFCActionPolynomialRing(P,K);
    r := n-1;
    xx := [&+[gK[i,j]*Q.i : i in [1..r]] : j in [1..r]];
    FFK := [* *];
    prev := IdentityMatrix(K,1);
    for i in [1..#F] do
        A := Matrix(Q,Nrows(F[i]),Ncols(F[i]),[
            Evaluate(FFCLiftPolynomialToActionField(f,Q),xx) : f in Eltseq(F[i])
        ]);
        A := ChangeRing(prev^-1,Q)*A*ChangeRing(HH[i],Q);
        if tw and i eq #F then
            A := Determinant(gK)^-1*A;
        end if;
        Append(~FFK,A);
        prev := HH[i];
    end for;
    FF := [* FFCDescendPolynomialMatrix(FFK[i],P,
        Sprintf("transformed resolution map %o",i)) : i in [1..#FFK] *];
    // Infer the transformed resolution-module weights from the descended maps.
    D := FFCRebuildWithWeights(C,FF,R,C`ProjectiveBase,wnew,[],[],0,[],[]);
    D`Twisted := tw;

    u := HH[#HH][1,1];
    chi := u^(2*n-2)*Determinant(gK)^(tw select 2 else 2*n);
    if assigned C`Discriminant then
        D`Discriminant := FFCDescendElement(chi*C`Discriminant,R,"transformed discriminant");
    end if;
    FFCTransportDiscriminantRecipe(C,D,chi);
    if assigned C`_Data`Algebra`TraceDiscriminant then
        D`_Data`Algebra`TraceDiscriminant := FFCDescendElement(
            chi*C`_Data`Algebra`TraceDiscriminant,R,"transformed trace discriminant");
    end if;

    L := (tw select u else u*Determinant(gK))*gK;
    okL,LR := FFCIntegralAutomorphismOverR(L,R);
    if okL then
        FFCTransportAlgebra(C,D,LR);
    end if;

    // Exactness is invariant under genuine bundle automorphisms, but an
    // integral model obtained from a non-unimodular generic change must be
    // checked again if the user asks for VerifyResolution.
    okg,gR := FFCIntegralAutomorphismOverR(gK,R);
    all_integral := okg;
    if all_integral then
        for i in [1..#HH] do
            oki,Hi := FFCIntegralAutomorphismOverR(HH[i],R);
            if not oki then
                all_integral := false;
                break;
            end if;
        end for;
    end if;
    if all_integral and assigned C`_Data`Resolution`Exact then
        D`_Data`Resolution`Exact := C`_Data`Resolution`Exact;
    end if;
    return D;
end intrinsic;

intrinsic ActBy(C::FinFlatCov,g::Mtrx,H::SeqEnum : Twisted := "Stored") -> FinFlatCov
{Sequence variant of the resolution-basis action.}
    return ActBy(C,g,[* B : B in H *] : Twisted := Twisted);
end intrinsic;
