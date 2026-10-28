// resolution / access
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/maps.m": FFCMapPolynomial;
import "../geometry/equations.m": FFCRawModelEquations;
import "format.m": FFCBetti, FFCResolutionBaseWeights;
import "kernels.m": FFCCompleteResolution, FFCPureKernel;

intrinsic ResolutionMaps(C::FinFlatCov) -> List
{Cached column-convention maps Phi_i:F_i->F_(i-1). No syzygies are computed just to return model
 equations.}
    if assigned C`_Data`Resolution`Maps then
        return C`_Data`Resolution`Maps;
    end if;
    if assigned C`_Data`Resolution`Pending then
        job := C`_Data`Resolution`Pending;
        if Type(job[1]) eq MonStgElt then
            source := job[2];
            F := ResolutionMaps(source);
            E,phi := BaseChange(source,job[3] : PreserveGrading := job[4]);
        else
            source := job[1];
            F := ResolutionMaps(source);
            E := ActBy(source,job[2],job[3] : Twisted := job[4]);
        end if;
        C`Model := E`Model;
        C`_Data`Resolution`Maps := E`_Data`Resolution`Maps;
        C`_Data`Resolution`Weights := E`_Data`Resolution`Weights;
        C`_Data`Resolution`FirstSyzygies := E`_Data`Resolution`FirstSyzygies;
        C`_Data`Bundle`Algebra := E`_Data`Bundle`Algebra;
        delete C`_Data`Resolution`Pending;
        return C`_Data`Resolution`Maps;
    end if;
    n := Degree(C);
    R := BaseRing(C);
    require C`_Data`Presentation`Kind notin {"Algebra",
        "BinaryAlgebra"}: "A general non-Gorenstein algebra has no canonical pure resolution";
    require n ge 4: "The quadratic resolution format starts in degree 4";
    Q := FFCRawModelEquations(C);
    P := Parent(Q[1]);
    if C`_Data`Presentation`Kind eq "Bhargava" and n eq 4 then
        F := [* Matrix(P,1,2,Q),Matrix(P,2,1,[Q[2],-Q[1]]) *];
    elif C`_Data`Presentation`Kind eq "Bhargava" and n eq 5 then
        M := &+[P.i*ChangeRing(C`Model[i],P) : i in [1..4]];
        F := [* Matrix(P,1,5,Q),M,Matrix(P,5,1,Q) *];
    else
        prefix := [* Matrix(P,1,#Q,Q) *];
        if assigned C`_Data`Resolution`FirstSyzygies then
            Append(~prefix,C`_Data`Resolution`FirstSyzygies);
        end if;
        F := FFCCompleteResolution(Q,n,prefix);
    end if;
    W := FFCResolutionBaseWeights(F,C`_Data`Bundle`Variables,C`ProjectiveBase,[]);
    C`_Data`Resolution`Maps := F;
    C`_Data`Resolution`FirstSyzygies := F[2];
    C`_Data`Resolution`Weights := W;
    if C`_Data`Presentation`Kind eq "Resolution" then
        C`Model := F;
        delta := W[#W][1]-(&+C`_Data`Bundle`Variables);
        C`_Data`Bundle`Algebra := [0] cat [delta-z : z in C`_Data`Bundle`Variables];
    end if;
    return F;
end intrinsic;

intrinsic BettiNumbers(C::FinFlatCov) -> SeqEnum
{The expected pure resolution ranks, including both end terms; cached.}
    if not assigned C`_Data`Resolution`Betti then
        C`_Data`Resolution`Betti := FFCBetti(Degree(C));
    end if;
    return C`_Data`Resolution`Betti;
end intrinsic;

intrinsic FirstSyzygies(C::FinFlatCov) -> Mtrx
{The matrix Phi_2 of relations among model equations; for degree 5 this is the alternating
 pencil.}
    if assigned C`_Data`Resolution`FirstSyzygies then
        return C`_Data`Resolution`FirstSyzygies;
    end if;
    n := Degree(C);
    require n ge 4: "FirstSyzygies requires degree at least 4";
    if assigned C`_Data`Resolution`Pending then
        job := C`_Data`Resolution`Pending;
        if Type(job[1]) eq MonStgElt then
            source := job[2];
            S := FirstSyzygies(source);
            P := BaseRing(C`Model[1]);
            S := Matrix(P,Nrows(S),Ncols(S),
                [FFCMapPolynomial(q,job[3],P) : q in Eltseq(S)]);
            C`_Data`Resolution`FirstSyzygies := S;
            return S;
        end if;
        // For a generic-field action, the first syzygy alone need not be
        // obtainable by an integral frame change.  Materialize the checked
        // transformed resolution and take its second map.
        F := ResolutionMaps(C);
        S := F[2];
    elif assigned C`_Data`Resolution`Maps or n le 5 then
        F := ResolutionMaps(C);
        S := F[2];
    else
        Q := FFCRawModelEquations(C);
        P := Parent(Q[1]);
        S := FFCPureKernel(Matrix(P,1,#Q,Q),1);
        require Ncols(S) eq (FFCBetti(n))[3]: "Unexpected linear syzygy rank";
    end if;
    C`_Data`Resolution`FirstSyzygies := S;
    return S;
end intrinsic;

intrinsic VerifyResolution(C::FinFlatCov) -> BoolElt
{Check exactness by polynomial module kernels and images, not only adjacent compositions.
 Potentially expensive.}
    if assigned C`_Data`Resolution`Exact then
        return C`_Data`Resolution`Exact;
    end if;
    F := ResolutionMaps(C);
    P := BaseRing(F[1]);
    b := FFCBetti(Degree(C));
    for i in [1..#F-1] do
        if not IsZero(F[i]*F[i+1]) then
            C`_Data`Resolution`Exact := false;
            return false;
        end if;
    end for;
    V := [* EModule(P,r) : r in b *];
    H := [* Homomorphism(V[i+1],V[i],Transpose(F[i])) : i in [1..#F] *];
    ok := true;
    for i in [1..#H-1] do
        if Kernel(H[i]) ne Image(H[i+1]) then
            ok := false;
            break;
        end if;
    end for;
    Z := sub<V[#V] | [V[#V] | ]>;
    ok := ok and Kernel(H[#H]) eq Z;
    C`_Data`Resolution`Exact := ok;
    return ok;
end intrinsic;
