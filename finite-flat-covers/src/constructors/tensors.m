// Bhargava tensor constructors. No geometry, resolvents, or discriminants.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCGet;
import "../core/arithmetic.m": FFCIsHomogeneousOfDegree;
import "../core/grading.m": FFCWeights;
import "../core/type.m": FFCNewCover;
import "../models/forms.m": FFCConvertSymmetric, FFCQuadricToTable;

function FFCConstruct(M,d,R,projective,w,qw,rw,tw,embedding,assume,check)
    if Type(projective) ne BoolElt then
        error "ProjectiveBase must be true or false";
    end if;
    if embedding notin {"Algebra","Model"} then
        error "Embedding must be Algebra or Model";
    end if;
    C := FFCNewCover();
    C`Degree := d;
    C`Model := M;
    C`CoefficientRing := R;
    C`ProjectiveBase := projective;
    C`_Data`Presentation`Kind := "Bhargava";
    C`Twisted := true;
    w,qw,rw,tw,aw := FFCWeights(M,d,R,projective,w,qw,rw,tw);
    C`_Data`Bundle`Variables := w;
    C`_Data`Bundle`Equations := qw;
    C`_Data`Bundle`Rows := rw;
    C`_Data`Bundle`Twist := tw;
    C`_Data`Bundle`Algebra := aw;
    C`Embedding := embedding;
    C`_Data`Presentation`Flatness := assume select "Assumed" else "Not certified";
    if check then
        if not IsAssociative(C) then
            error "The multiplication table failed its associativity check";
        end if;
    end if;
    /* Also check compatibility of algebra multiplication with the grading. */
    if check and projective then
        T := StructureConstants(C);
        for i,j,k in [0..d-1] do
            if not FFCIsHomogeneousOfDegree(FFCGet(T,d,i,j,k),aw[i+1]+aw[j+1]-aw[k+1]) then
                error "Multiplication table is not compatible with the algebra bundle weights";
            end if;
        end for;
    end if;
    return C;
end function;

intrinsic FiniteFlatCover(M::SeqEnum : ProjectiveBase := false, ModelConvention := "Coefficients",
    CoverDegree := 0, Twisted := true, VariableWeights := [], EquationWeights := [], RowWeights := [],
    MatrixTwist := 0, Embedding := "Model", AssumeFiniteFlat := false,
    CheckAlgebra := false) -> FinFlatCov
{Construct from two ternary quadrics/symmetric coefficient tables or four alternating 5 by 5
 matrices. The default is the small model; choose Embedding := "Algebra" explicitly for
 the multiplication-table presentation, including degenerate tensors.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    require #M gt 0: "The model cannot be empty";
    if Type(M[1]) eq RngMPolElt and Rank(Parent(M[1])) ge 4 then
        require #RowWeights eq 0 and MatrixTwist eq 0:
            "RowWeights and MatrixTwist are specific to quintic alternating models";
        return FiniteFlatCoverFromQuadrics(M : CoverDegree := CoverDegree, ProjectiveBase := ProjectiveBase, Twisted := Twisted,
            VariableWeights := VariableWeights, EquationWeights := EquationWeights,
            Embedding := Embedding, AssumeFiniteFlat := AssumeFiniteFlat, CheckAlgebra := CheckAlgebra);
    end if;
    require #M in {2,4}: "Use a list [* Phi_1,... *] for a resolution model";
    if Type(M[1]) eq RngMPolElt then
        require #M eq 2: "Polynomial sequence input is a pair of ternary quadrics";
        P := Parent(M[1]);
        require Rank(P) eq 3: "Quadrics must have three fibre variables";
        require forall{q : q in M | Parent(q) eq P and (q eq 0 or (IsHomogeneous(q) and Degree(q) eq 2))}:
            "Input forms must be homogeneous ternary quadrics in the same ring";
        R := BaseRing(P);
        M := [FFCQuadricToTable(q) : q in M];
        d := 4;
    else
        R := BaseRing(M[1]);
        require forall{A : A in M | BaseRing(A) eq R}: "All matrices must have the same coefficient ring";
        d := #M eq 2 select 4 else 5;
        if d eq 4 then
            M := [FFCConvertSymmetric(A,ModelConvention) : A in M];
        else
            require forall{A : A in M | Nrows(A) eq 5 and Ncols(A) eq 5}:
                "Quintic matrices must be 5 by 5";
            require forall{A : A in M | Transpose(A) eq -A and forall{i : i in [1..5] | A[i,i] eq 0}}:
                "Quintic matrices must be alternating, including zero diagonal in characteristic 2";
        end if;
    end if;
    require CoverDegree eq 0 or CoverDegree eq d: "CoverDegree disagrees with the tensor shape";
    C := FFCConstruct(M,d,R,ProjectiveBase,VariableWeights,EquationWeights,RowWeights,MatrixTwist,
        Embedding,AssumeFiniteFlat,CheckAlgebra);
    require Type(Twisted) eq BoolElt: "Twisted must be a boolean";
    C`Twisted := Twisted;
    return C;
end intrinsic;

intrinsic IdentityFiniteFlatCover(R::Rng : ProjectiveBase := false, Twisted := true) -> FinFlatCov
{The degree-one identity cover.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    require Type(Twisted) eq BoolElt: "Twisted must be a boolean";
    C := FFCConstruct([R!1],1,R,ProjectiveBase,[],[],[],0,"Algebra",false,false);
    C`Twisted := Twisted;
    return C;
end intrinsic;
