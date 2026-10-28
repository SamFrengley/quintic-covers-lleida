// Transform initial equations now; transform higher maps only when requested.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "descent.m": FFCActionPolynomialRing, FFCDescendPolynomialMatrix,
    FFCLiftPolynomialToActionField, FFCIntegralAutomorphismOverR;
import "../algebra/basis.m": FFCTransportAlgebra;
import "../algebra/invariants.m": FFCTransportDiscriminantRecipe;
import "../constructors/rebuild.m": FFCRebuildWithWeights;
import "../core/arithmetic.m": FFCDescendElement;
import "../core/grading.m": FFCPrepareActionMatrixWithWeights;

function FFCActPartialResolution(C,g,h,tw)
    R := BaseRing(C);
    n := Degree(C);
    gK,wnew := FFCPrepareActionMatrixWithWeights(g,R,C`_Data`Bundle`Variables,C`ProjectiveBase,true);
    hK,qnew := FFCPrepareActionMatrixWithWeights(h,R,C`_Data`Bundle`Equations,C`ProjectiveBase,false);
    K := BaseRing(gK);
    A := C`Model[1];
    P := BaseRing(A);
    Q := FFCActionPolynomialRing(P,K);
    images := [&+[gK[i,j]*Q.i : i in [1..n-1]] : j in [1..n-1]];
    AK := Matrix(Q,1,Ncols(A),[
        Evaluate(FFCLiftPolynomialToActionField(q,Q),images) : q in Eltseq(A)
    ]);
    AK := AK*ChangeRing(Transpose(hK),Q);
    Anew := FFCDescendPolynomialMatrix(AK,P,"transformed initial resolution map");
    // The transformed quadrics determine their new equation weights from wnew.
    D := FFCRebuildWithWeights(C,[* Anew *],R,C`ProjectiveBase,wnew,[],[],0,[],[]);
    D`Twisted := tw;
    D`_Data`Resolution`Pending := <C,gK,hK,tw>;
    chi := Determinant(gK)^(tw select 2 else 2*n);
    if assigned C`Discriminant then
        D`Discriminant := FFCDescendElement(chi*C`Discriminant,R,"transformed discriminant");
    end if;
    FFCTransportDiscriminantRecipe(C,D,chi);
    L := (tw select K!1 else Determinant(gK))*gK;
    okL,LR := FFCIntegralAutomorphismOverR(L,R);
    if okL then
        FFCTransportAlgebra(C,D,LR);
    end if;
    return D;
end function;
