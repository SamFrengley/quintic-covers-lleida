// base change / maps
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../constructors/rebuild.m": FFCRebuild;
import "../core/arithmetic.m": FFCIsHomogeneousOfDegree, FFCIsUnit;
import "../core/maps.m": FFCMapPolynomial;
import "../core/names.m": FFCCoordinateRing;

intrinsic BaseChange(C::FinFlatCov, phi::Map : PreserveGrading := false) -> FinFlatCov, Map
{Base change along an explicit coefficient homomorphism; target is Spec unless PreserveGrading is
 requested.}
    require Domain(phi) eq BaseRing(C): "The map domain must be the coefficient ring";
    S := Codomain(phi);
    d := Degree(C);
    require phi(BaseRing(C)!1) eq S!1: "The coefficient map must preserve 1";
    if PreserveGrading then
        require C`ProjectiveBase and Type(S) eq RngMPol and Rank(S) eq 2:
            "PreserveGrading requires a map between homogeneous two-variable base rings";
        require forall{i : i in [1..2] | FFCIsHomogeneousOfDegree(phi(BaseRing(C).i),1)}:
            "The base variables must map to homogeneous linear forms";
        /* To define P^1 -> P^1, their coefficient matrix must be invertible. */
        H := Matrix(BaseRing(S),2,2,[MonomialCoefficient(phi(BaseRing(C).i),S.j) : i,j in [1..2]]);
        require FFCIsUnit(Determinant(H)): "The base map has a projective base point";
        projective := true;
    else
        projective := false;
    end if;
    if C`_Data`Presentation`Kind eq "Resolution" then
        P := FFCCoordinateRing(S,d-1);
        /* Do not complete a partial resolution just to take a fibre. */
        M := [* Matrix(P,Nrows(A),Ncols(A),
            [FFCMapPolynomial(f,phi,P) : f in Eltseq(A)]) : A in C`Model *];
    elif C`_Data`Presentation`Kind eq "BinaryAlgebra" then
        P := FFCCoordinateRing(S,2);
        M := FFCMapPolynomial(C`Model,phi,P);
    elif C`_Data`Presentation`Kind eq "Algebra" then
        M := [phi(a) : a in C`StructureConstants];
    elif d eq 1 then
        M := [S!1];
    elif d in {2,3} then
        P := FFCCoordinateRing(S,2);
        M := FFCMapPolynomial(C`Model,phi,P);
    else
        M := [Matrix(S,Nrows(A),Ncols(A),[phi(a) : a in Eltseq(A)]) : A in C`Model];
    end if;
    D := FFCRebuild(C,M,S,projective,PreserveGrading);
    if assigned C`_Data`Resolution`Pending then
        D`_Data`Resolution`Pending := <"BaseChange",C,phi,PreserveGrading>;
    end if;
    if assigned C`StructureConstants and C`_Data`Presentation`Kind ne "Algebra" then
        D`_Data`Algebra`Pending := <"BaseChange",C,phi>;
    elif assigned C`_Data`Algebra`Pending then
        D`_Data`Algebra`Pending := <"BaseChange",C,phi>;
    end if;
    if assigned C`Discriminant then
        D`Discriminant := phi(C`Discriminant);
    end if;
    if assigned C`_Data`Resolvents`Standard or assigned C`_Data`Resolvents`Pending then
        D`_Data`Resolvents`Pending := <"BaseChange",C,phi,PreserveGrading>;
    end if;
    if assigned C`_Data`Resolvents`Conjectural or assigned C`_Data`Resolvents`PendingConjectural then
        D`_Data`Resolvents`PendingConjectural := <"BaseChange",C,phi,PreserveGrading>;
    end if;
    if assigned C`_Data`Resolvents`DiscriminantFactor then
        D`_Data`Resolvents`DiscriminantFactor := phi(C`_Data`Resolvents`DiscriminantFactor);
    end if;
    if assigned C`_Data`Resolvents`Inclusion then
        A := C`_Data`Resolvents`Inclusion;
        D`_Data`Resolvents`Inclusion := Matrix(S,Nrows(A),Ncols(A),[phi(a) : a in Eltseq(A)]);
    end if;
    if assigned C`_Data`Resolvents`Certificate then
        D`_Data`Resolvents`Certificate := "Specialized experimental order, not a fresh saturation";
    end if;
    if assigned C`_Data`Resolvents`SourceDegree then
        D`_Data`Resolvents`SourceDegree := C`_Data`Resolvents`SourceDegree;
    end if;
    if assigned C`_Data`Resolvents`Normalization then
        D`_Data`Resolvents`Normalization := C`_Data`Resolvents`Normalization;
    end if;
    if assigned C`_Data`Algebra`Associative and C`_Data`Algebra`Associative then
        D`_Data`Algebra`Associative := true;
    end if;
    return D,phi;
end intrinsic;
