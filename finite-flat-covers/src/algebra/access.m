// algebra / access
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "basis.m": FFCMaterializeAlgebra;
import "tables.m": FFCBlank, FFCGet, FFCPut;
import "../models/multiplication.m": FFCBinaryRingConstants, FFCQuarticConstants, FFCQuinticConstants;
import "../resolution/constants.m": FFCFRConstants;

intrinsic StructureConstants(C::FinFlatCov) -> SeqEnum
{Full d^3 table; coefficient of e_k in e_i e_j is at ((i*d+j)*d+k)+1, indices 0 based.}
    if assigned C`StructureConstants then
        return C`StructureConstants;
    end if;
    if FFCMaterializeAlgebra(C) then
        return C`StructureConstants;
    end if;
    d := C`Degree;
    R := C`CoefficientRing;
    M := C`Model;
    if C`_Data`Presentation`Kind eq "Resolution" then
        T := FFCFRConstants(C);
    elif C`_Data`Presentation`Kind eq "BinaryAlgebra" then
        P := Parent(M);
        a := [MonomialCoefficient(M,P.1^i*P.2^(d-i)) : i in [0..d]];
        T := FFCBinaryRingConstants(a,d);
    elif C`_Data`Presentation`Kind eq "Algebra" then
        T := C`Model;
    elif d le 3 then
        T := FFCBlank(R,d);
        if d eq 2 then
            P := Parent(M);
            a := MonomialCoefficient(M,P.1^2);
            b := MonomialCoefficient(M,P.1*P.2);
            c := MonomialCoefficient(M,P.2^2);
            FFCPut(~T,2,1,1,0,-a*c);
            FFCPut(~T,2,1,1,1,-b);
        elif d eq 3 then
            P := Parent(M);
            a := MonomialCoefficient(M,P.1^3);
            b := MonomialCoefficient(M,P.1^2*P.2);
            c := MonomialCoefficient(M,P.1*P.2^2);
            e := MonomialCoefficient(M,P.2^3);
            FFCPut(~T,3,1,1,0,-a*c);
            FFCPut(~T,3,1,1,1,b);
            FFCPut(~T,3,1,1,2,-a);
            FFCPut(~T,3,1,2,0,-a*e);
            FFCPut(~T,3,2,2,0,-b*e);
            FFCPut(~T,3,2,2,1,e);
            FFCPut(~T,3,2,2,2,-c);
        end if;
    elif d eq 4 then
        T := FFCQuarticConstants(M[1],M[2]);
    else
        T := FFCQuinticConstants(M);
    end if;
    C`StructureConstants := T;
    return T;
end intrinsic;

intrinsic MultiplicationMatrices(C::FinFlatCov) -> SeqEnum
{Matrices of multiplication by 1,e_1,...,e_(d-1), acting on column vectors.}
    if assigned C`_Data`Algebra`Matrices then
        return C`_Data`Algebra`Matrices;
    end if;
    T := StructureConstants(C);
    d := Degree(C);
    R := BaseRing(C);
    L := [Matrix(R,d,d,[FFCGet(T,d,i,j,k) : k in [0..d-1], j in [0..d-1]]) : i in [0..d-1]];
    C`_Data`Algebra`Matrices := L;
    return L;
end intrinsic;

intrinsic IsAssociative(C::FinFlatCov) -> BoolElt
{Check the structure constants exactly; not a numerical or generic-fibre check.}
    if assigned C`_Data`Algebra`Associative then
        return C`_Data`Algebra`Associative;
    end if;
    L := MultiplicationMatrices(C);
    T := StructureConstants(C);
    d := Degree(C);
    for i in [0..d-1] do
        for j in [0..d-1] do
            if L[i+1]*L[j+1] ne &+[FFCGet(T,d,i,j,k)*L[k+1] : k in [0..d-1]] then
                C`_Data`Algebra`Associative := false;
                return false;
            end if;
        end for;
    end for;
    C`_Data`Algebra`Associative := true;
    return true;
end intrinsic;

intrinsic AlgebraBasisChange(C::FinFlatCov) -> Mtrx
{Rows express the acted algebra basis in the source basis. Materializes a deferred table
 transport if needed.}
    if not assigned C`_Data`Algebra`BasisChange then
        T := StructureConstants(C);
    end if;
    require assigned C`_Data`Algebra`BasisChange: "No algebra basis change is recorded for this cover";
    return C`_Data`Algebra`BasisChange;
end intrinsic;
