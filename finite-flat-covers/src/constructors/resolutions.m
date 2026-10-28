// Canonical resolution input. Exactness is checked only by VerifyResolution.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCGet;
import "../core/arithmetic.m": FFCIsHomogeneousOfDegree;
import "../core/grading.m": FFCRelativeWeight;
import "../core/type.m": FFCNewCover;
import "../resolution/format.m": FFCCheckResolutionShape, FFCResolutionBaseWeights;

function FFCResolutionConstruct(F,Q,n,R,projective,w,qw,W,embedding,assume,check)
    if n lt 4 then
        error "Resolution models require degree at least 4";
    end if;
    if Type(projective) ne BoolElt then
        error "ProjectiveBase must be true or false";
    end if;
    if embedding notin {"Model","Algebra"} then
        error "Embedding must be Model or Algebra";
    end if;
    if #w eq 0 then
        w := [0 : i in [1..n-1]];
    end if;
    if #w ne n-1 then
        error "VariableWeights must have length n-1";
    end if;
    if projective and not (Type(R) eq RngMPol and Rank(R) eq 2) then
        error "Proj requires a standard graded two-variable base ring";
    end if;
    if not projective and exists{v : v in w cat qw | v ne 0} then
        error "Nonzero bundle degrees require Proj";
    end if;
    complete := #F eq n-2;
    if complete then
        FFCCheckResolutionShape(F,n);
        W := FFCResolutionBaseWeights(F,w,projective,W);
        expected := W[2];
    else
        if #F ne 1 then
            error "Supply all maps, or construct from quadrics";
        end if;
        if #W ne 0 then
            error "ResolutionWeights require the complete resolution";
        end if;
        expected := [];
        for q in Q do
            if projective then
                ok,e := FFCRelativeWeight(q,w);
                if not ok then
                    error "A quadric is not bigraded";
                end if;
            else
                e := 0;
            end if;
            Append(~expected,e);
        end for;
    end if;
    if #qw ne 0 and qw ne expected then
        error "EquationWeights do not match the first resolution map";
    end if;
    C := FFCNewCover();
    C`Degree := n;
    C`_Data`Presentation`Kind := "Resolution";
    C`Model := F;
    C`CoefficientRing := R;
    C`ProjectiveBase := projective;
    C`Embedding := embedding;
    C`Twisted := true;
    C`_Data`Bundle`Variables := w;
    C`_Data`Bundle`Equations := expected;
    C`_Data`Bundle`Rows := [];
    C`_Data`Bundle`Twist := 0;
    C`_Data`Presentation`Polynomials := Q;
    C`_Data`Presentation`Flatness := assume select "Assumed" else "Not certified";
    if not projective then
        C`_Data`Bundle`Algebra := [0 : i in [1..n]];
    end if;
    if complete then
        C`_Data`Resolution`Maps := F;
        C`_Data`Resolution`Weights := W;
        C`_Data`Resolution`FirstSyzygies := F[2];
        delta := W[#W][1]-(&+w);
        C`_Data`Bundle`Algebra := [0] cat [delta-z : z in w];
    end if;
    if check then
        if not IsAssociative(C) then
            error "The derived multiplication is not associative";
        end if;
        if projective then
            T := StructureConstants(C);
            aw := C`_Data`Bundle`Algebra;
            for i,j,k in [0..n-1] do
                if not FFCIsHomogeneousOfDegree(FFCGet(T,n,i,j,k),aw[i+1]+aw[j+1]-aw[k+1]) then
                    error "The derived multiplication is not compatible with the bigrading";
                end if;
            end for;
        end if;
    end if;
    return C;
end function;

intrinsic FiniteFlatCoverFromResolution(F::List : CoverDegree := 0, ProjectiveBase := false, Twisted := true,
    VariableWeights := [], ResolutionWeights := [], Embedding := "Model", AssumeFiniteFlat := false,
    CheckAlgebra := false) -> FinFlatCov
{Construct an oriented Fisher--Radicevic model. F is [* Phi_1,...,Phi_(n-2) *] in the COLUMN
 convention.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    n := CoverDegree eq 0 select #F+2 else CoverDegree;
    require n ge 4 and #F eq n-2: "Expected all n-2 resolution matrices";
    P := BaseRing(F[1]);
    R := BaseRing(P);
    Q := Eltseq(F[1]);
    require Type(Twisted) eq BoolElt: "Twisted must be a boolean";
    C := FFCResolutionConstruct(F,Q,n,R,ProjectiveBase,VariableWeights,[],ResolutionWeights,
        Embedding,AssumeFiniteFlat,CheckAlgebra);
    C`Twisted := Twisted;
    return C;
end intrinsic;

intrinsic FiniteFlatCoverFromResolution(F::SeqEnum : CoverDegree := 0, ProjectiveBase := false, Twisted := true,
    VariableWeights := [], ResolutionWeights := [], Embedding := "Model", AssumeFiniteFlat := false,
    CheckAlgebra := false) -> FinFlatCov
{Sequence variant; a Magma heterogeneous list is preferred for rectangular matrices.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    return FiniteFlatCoverFromResolution([* A : A in F *] : CoverDegree := CoverDegree, Twisted := Twisted,
        ProjectiveBase := ProjectiveBase, VariableWeights := VariableWeights, ResolutionWeights := ResolutionWeights,
        Embedding := Embedding, AssumeFiniteFlat := AssumeFiniteFlat, CheckAlgebra := CheckAlgebra);
end intrinsic;

intrinsic FiniteFlatCover(F::List : CoverDegree := 0, ProjectiveBase := false, Twisted := true,
    VariableWeights := [], ResolutionWeights := [], Embedding := "Model", AssumeFiniteFlat := false,
    CheckAlgebra := false) -> FinFlatCov
{Resolution-model constructor in arbitrary degree at least four.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    return FiniteFlatCoverFromResolution(F : CoverDegree := CoverDegree, ProjectiveBase := ProjectiveBase, Twisted := Twisted,
        VariableWeights := VariableWeights, ResolutionWeights := ResolutionWeights,
        Embedding := Embedding, AssumeFiniteFlat := AssumeFiniteFlat, CheckAlgebra := CheckAlgebra);
end intrinsic;

intrinsic FiniteFlatCoverFromQuadrics(Q::SeqEnum : CoverDegree := 0, ProjectiveBase := false, Twisted := true,
    VariableWeights := [], EquationWeights := [], Embedding := "Model", AssumeFiniteFlat := false,
    CheckAlgebra := false) -> FinFlatCov
{Construct from canonical quadrics. The full pure resolution is computed only when needed.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    require #Q gt 0: "Supply a nonempty list of quadrics";
    P := Parent(Q[1]);
    n := CoverDegree eq 0 select Rank(P)+1 else CoverDegree;
    require n ge 4 and Rank(P) eq n-1: "Use n-1 fibre variables for a degree-n resolution model";
    require forall{q : q in Q | Parent(q) eq P and FFCIsHomogeneousOfDegree(q,2)}:
        "The equations must be homogeneous quadrics over a common coefficient ring";
    R := BaseRing(P);
    /* Constant-coefficient row reduction removes redundant quadrics over a
       FIELD. Over arithmetic bases no nonunit pivot or saturation is used. */
    if #Q ne n*(n-3) div 2 then
        require IsField(R) and not ProjectiveBase:
            "Supply a minimal integral/bigraded set of n(n-3)/2 quadrics";
        mons := MonomialsOfDegree(P,2);
        A := Matrix(R,#Q,#mons,[MonomialCoefficient(q,m) : q in Q, m in mons]);
        A := EchelonForm(A);
        r := Rank(A);
        Q := [&+[(P!A[i,j])*mons[j] : j in [1..#mons]] : i in [1..r]];
    end if;
    require #Q eq n*(n-3) div 2: "The quadratic span has the wrong rank";
    F := [* Matrix(P,1,#Q,Q) *];
    require Type(Twisted) eq BoolElt: "Twisted must be a boolean";
    C := FFCResolutionConstruct(F,Q,n,R,ProjectiveBase,VariableWeights,EquationWeights,[],
        Embedding,AssumeFiniteFlat,CheckAlgebra);
    C`Twisted := Twisted;
    return C;
end intrinsic;
