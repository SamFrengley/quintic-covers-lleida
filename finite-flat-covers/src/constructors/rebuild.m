// constructors / rebuild
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "algebras.m": FFCBinaryAlgebraCover;
import "resolutions.m": FFCResolutionConstruct;
import "tensors.m": FFCConstruct;

function FFCRebuildWithWeights(C,M,R,projective,w,q,r,t,W,aw)
    assume := C`_Data`Presentation`Flatness in {"Assumed","Verified"};
    if C`_Data`Presentation`Kind eq "Resolution" then
        D := FFCResolutionConstruct(M,Eltseq(M[1]),Degree(C),R,projective,w,q,W,
            C`Embedding,assume,false);
    elif C`_Data`Presentation`Kind eq "BinaryAlgebra" then
        D := FFCBinaryAlgebraCover(M,Degree(C),R);
    elif C`_Data`Presentation`Kind eq "Algebra" then
        D := FiniteFlatCoverFromStructureConstants(M,Degree(C) : ProjectiveBase := projective,
            AlgebraWeights := aw, CheckAlgebra := false);
    else
        D := FFCConstruct(M,C`Degree,R,projective,w,q,r,t,C`Embedding,assume,false);
    end if;
    D`Twisted := C`Twisted;
    return D;
end function;

function FFCRebuild(C,M,R,projective,preserve)
    if preserve then
        w := C`_Data`Bundle`Variables;
        q := C`_Data`Bundle`Equations;
        r := C`_Data`Bundle`Rows;
        t := C`_Data`Bundle`Twist;
        aw := assigned C`_Data`Bundle`Algebra select C`_Data`Bundle`Algebra else [];
        if C`_Data`Presentation`Kind eq "Resolution" and assigned C`_Data`Resolution`Weights then
            W := C`_Data`Resolution`Weights;
        else
            W := [];
        end if;
    else
        w := [];
        q := [];
        r := [];
        t := 0;
        W := [];
        aw := [];
    end if;
    return FFCRebuildWithWeights(C,M,R,projective,w,q,r,t,W,aw);
end function;
