// Explicit-table and lazy binary-algebra constructors.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCGet;
import "../core/arithmetic.m": FFCIsHomogeneousOfDegree;
import "../core/type.m": FFCNewCover;

function FFCBinaryAlgebraCover(f,n,R)
    // Used when primitivity is not cheaply certified. Wood's table is lazy.
    C := FFCNewCover();
    C`Degree := n;
    C`CoefficientRing := R;
    C`ProjectiveBase := false;
    C`Model := f;
    C`_Data`Presentation`Kind := "BinaryAlgebra";
    C`Twisted := true;
    C`Embedding := "Algebra";
    C`_Data`Bundle`Algebra := [0 : i in [1..n]];
    C`_Data`Bundle`Variables := C`_Data`Bundle`Algebra;
    C`_Data`Bundle`Equations := [0 : i in [1..n*(n-1) div 2]];
    C`_Data`Bundle`Rows := [];
    C`_Data`Bundle`Twist := 0;
    C`_Data`Presentation`Flatness := "Verified";
    return C;
end function;

intrinsic FiniteFlatCoverFromStructureConstants(T::SeqEnum, n::RngIntElt : ProjectiveBase := false,
    Twisted := true, AlgebraWeights := [], CheckAlgebra := false) -> FinFlatCov
{Unrestricted-rank finite free algebra fallback, including non-Gorenstein covers. T has n^3
 entries and unit e_0.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    require n ge 1 and #T eq n^3: "Expected n^3 structure constants";
    R := Universe(T);
    w := AlgebraWeights;
    if #w eq 0 then
        w := [0 : i in [1..n]];
    end if;
    require #w eq n and w[1] eq 0: "AlgebraWeights must have n entries, starting with zero";
    if ProjectiveBase then
        require Type(R) eq RngMPol and Rank(R) eq 2: "Proj requires R=k[s,t]";
    else
        require forall{a : a in w | a eq 0}: "Nonzero weights require Proj";
    end if;
    for i,j in [0..n-1] do
        require FFCGet(T,n,0,i,j) eq (i eq j select R!1 else R!0): "e_0 must be the identity";
        for k in [0..n-1] do
            require FFCGet(T,n,i,j,k) eq FFCGet(T,n,j,i,k): "The algebra must be commutative";
            if ProjectiveBase then
                require FFCIsHomogeneousOfDegree(FFCGet(T,n,i,j,k),w[i+1]+w[j+1]-w[k+1]):
                    "The multiplication must respect the grading";
            end if;
        end for;
    end for;
    C := FFCNewCover();
    C`Degree := n;
    C`_Data`Presentation`Kind := "Algebra";
    C`Model := T;
    C`StructureConstants := T;
    C`CoefficientRing := R;
    C`ProjectiveBase := ProjectiveBase;
    C`Embedding := "Algebra";
    C`_Data`Bundle`Algebra := w;
    require Type(Twisted) eq BoolElt: "Twisted must be a boolean";
    C`Twisted := Twisted;
    C`_Data`Presentation`Flatness := CheckAlgebra select "Verified" else "Assumed";
    C`_Data`Bundle`Variables := n eq 1 select [0,0] else w;
    C`_Data`Bundle`Equations := n eq 1 select [0] else &cat[[w[i]+w[j] : j in [i..n]] : i in [2..n]];
    C`_Data`Bundle`Rows := [];
    C`_Data`Bundle`Twist := 0;
    if CheckAlgebra then
        require IsAssociative(C): "The multiplication is not associative";
    end if;
    return C;
end intrinsic;
