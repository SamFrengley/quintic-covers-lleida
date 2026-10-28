// Equation getters and Cox data; all derived presentations are cached.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCGet;
import "shape.m": FFCCheckEquationShape;
import "../core/bundles.m": FFCAlgebraBundleWeights;
import "../core/maps.m": FFCFlatten;
import "../models/forms.m": FFCModelEquations;
import "../core/names.m": FFCCoordinateRing;

function FFCAlgebraEquations(C)
    if assigned C`_Data`Geometry`AlgebraEquations then
        return Explode(C`_Data`Geometry`AlgebraEquations);
    end if;
    d := C`Degree;
    R := C`CoefficientRing;
    if d eq 1 then
        P := FFCCoordinateRing(R,2);
        C`_Data`Geometry`AlgebraEquations := <[P.2],[0,0]>;
        return Explode(C`_Data`Geometry`AlgebraEquations);
    end if;
    P := FFCCoordinateRing(R,d);
    T := StructureConstants(C);
    Q := [];
    for i in [1..d-1] do
        for j in [i..d-1] do
            z := P.(i+1)*P.(j+1)-FFCGet(T,d,i,j,0)*P.1^2;
            for k in [1..d-1] do
                z -:= FFCGet(T,d,i,j,k)*P.1*P.(k+1);
            end for;
            Append(~Q,z);
        end for;
    end for;
    C`_Data`Geometry`AlgebraEquations := <Q,C`_Data`Bundle`Algebra>;
    return Explode(C`_Data`Geometry`AlgebraEquations);
end function;

function FFCRawModelEquations(C)
    if not assigned C`_Data`Presentation`Polynomials then
        if C`_Data`Presentation`Kind in {"Algebra","BinaryAlgebra"} then
            Q,w := FFCAlgebraEquations(C);
        elif C`_Data`Presentation`Kind eq "Resolution" then
            Q := Eltseq(C`Model[1]);
        else
            Q := FFCModelEquations(C`Model,Degree(C),BaseRing(C));
        end if;
        C`_Data`Presentation`Polynomials := Q;
    end if;
    return C`_Data`Presentation`Polynomials;
end function;

function FFCChosenEquations(C,which)
    if which eq "Model" then
        Q := FFCRawModelEquations(C);
        w := C`_Data`Bundle`Variables;
    elif which eq "Algebra" then
        Q,w := FFCAlgebraEquations(C);
    else
        error "Embedding must be Model or Algebra";
    end if;
    FFCCheckEquationShape(C,Q,which,false);
    return Q,w;
end function;

intrinsic ModelPolynomials(C::FinFlatCov : Cox := true) -> SeqEnum
{Small binary-form, quadric or Pfaffian equations. These do NOT always define a finite cover.}
    if C`ProjectiveBase and Cox then
        P,Q,Z,B := CoxData(C : Embedding := "Model");
        return Q;
    end if;
    Q,w := FFCChosenEquations(C,"Model");
    return Q;
end intrinsic;

intrinsic DefiningPolynomials(C::FinFlatCov) -> SeqEnum
{Equations of the chosen underlying scheme; Cox equations on a Proj base.}
    if assigned C`DefiningPolynomials then
        FFCCheckEquationShape(C,C`DefiningPolynomials,C`Embedding,C`ProjectiveBase);
        return C`DefiningPolynomials;
    end if;
    Q,w := FFCChosenEquations(C,C`Embedding);
    if C`ProjectiveBase then
        P,Q,Z,B := CoxData(C);
    end if;
    FFCCheckEquationShape(C,Q,C`Embedding,C`ProjectiveBase);
    C`DefiningPolynomials := Q;
    return Q;
end intrinsic;

intrinsic BundleWeights(C::FinFlatCov : Embedding := "Chosen") -> SeqEnum
{Coordinate degrees. This does not construct equations or a scheme.}
    which := Embedding eq "Chosen" select C`Embedding else Embedding;
    require which in {"Algebra","Model"}: "Embedding must be Chosen, Algebra or Model";
    if which eq "Model" then
        return C`_Data`Bundle`Variables;
    end if;
    return FFCAlgebraBundleWeights(C);
end intrinsic;

intrinsic CoxData(C::FinFlatCov : Embedding := "Chosen") -> RngMPol, SeqEnum, SeqEnum, SeqEnum
{The Cox polynomial ring, equations, two grading rows, and two irrelevant components.}
    require C`ProjectiveBase: "CoxData requires a Proj base";
    which := Embedding eq "Chosen" select C`Embedding else Embedding;
    require which in {"Algebra","Model"}: "Unknown embedding";
    if which eq "Model" and assigned C`_Data`Geometry`CoxModel then
        return Explode(C`_Data`Geometry`CoxModel);
    end if;
    if which eq "Algebra" and assigned C`_Data`Geometry`CoxAlgebra then
        return Explode(C`_Data`Geometry`CoxAlgebra);
    end if;
    Q,w := FFCChosenEquations(C,which);
    Q := FFCFlatten(Q);
    P := Parent(Q[1]);
    Z := [[1,1] cat w,[0,0] cat [1 : v in w]];
    B := [ideal<P|P.1,P.2>,ideal<P|[P.i : i in [3..Rank(P)]]>];
    if which eq "Model" then
        C`_Data`Geometry`CoxModel := <P,Q,Z,B>;
    else
        C`_Data`Geometry`CoxAlgebra := <P,Q,Z,B>;
    end if;
    return P,Q,Z,B;
end intrinsic;
