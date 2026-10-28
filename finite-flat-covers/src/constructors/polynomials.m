// Univariate and homogeneous-binary input; explicit canonical quadrics.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "algebras.m": FFCBinaryAlgebraCover;
import "tensors.m": FFCConstruct;
import "polynomial_weights.m": FFCBinaryModelWeights;
import "model_ordering.m": FFCOrderPolynomialModel;
import "../core/arithmetic.m": FFCIsUnit;
import "../models/forms.m": FFCModelFromBinaryCoefficients;
import "../core/names.m": FFCCoordinateRing, FFCNamedPolynomialRing;

function FFCCertifiablyPrimitive(a)
    // A cheap sufficient test, not a decision procedure over R[t].
    if exists{c : c in a | FFCIsUnit(c)} then
        return true;
    end if;
    R := Universe(a);
    if Type(R) eq RngInt then
        return GCD(a) eq 1;
    end if;
    return false;
end function;

intrinsic CanonicalQuadrics(f::RngUPolElt) -> SeqEnum
{Division-free canonical quadrics for a monic rank-n algebra R[t]/f in coordinates
 [1:t:...:t^(n-2)], n>=4.}
    n := Degree(f);
    U := Parent(f);
    R := BaseRing(U);
    require n ge 4 and LeadingCoefficient(f) eq R!1: "A monic polynomial of degree at least four is required";
    P := FFCCoordinateRing(R,n-1);
    pairs := &cat[[<i,j> : j in [i..n-2]] : i in [0..n-2]];
    pivots := [ [a : a in [1..#pairs] | pairs[a][1]+pairs[a][2] eq k][1] : k in [0..n-1] ];
    mons := [P.(a[1]+1)*P.(a[2]+1) : a in pairs];
    Q := [];
    for a in [1..#pairs] do
        if a in pivots then
            continue;
        end if;
        r := U.1^(pairs[a][1]+pairs[a][2]) mod f;
        Append(~Q,mons[a]-&+[(P!Coefficient(r,k))*mons[pivots[k+1]] : k in [0..n-1]]);
    end for;
    assert #Q eq n*(n-3) div 2;
    return Q;
end intrinsic;

intrinsic CanonicalQuadrics(f::RngMPolElt : CoverDegree := 0) -> SeqEnum
{Canonical binary n-ic equations: rational-normal-curve relations and all degree n-4 multiples of
 f, n>=4. No division.}
    B := Parent(f);
    R := BaseRing(B);
    require Rank(B) eq 2 and (f eq 0 or IsHomogeneous(f)): "Expected a homogeneous binary form";
    n := CoverDegree eq 0 select Degree(f) else CoverDegree;
    require n ge 4 and (f eq 0 or Degree(f) eq n): "Expected a degree n>=4 binary form";
    m := n-2;
    P := FFCCoordinateRing(R,n-1);
    pairs := &cat[[<i,j> : j in [i..m]] : i in [0..m]];
    pivots := [[a : a in [1..#pairs] | pairs[a][1]+pairs[a][2] eq k][1] : k in [0..2*m]];
    mons := [P.(a[1]+1)*P.(a[2]+1) : a in pairs];
    Q := [mons[a]-mons[pivots[pairs[a][1]+pairs[a][2]+1]] : a in [1..#pairs] | a notin pivots];
    coeffs := [MonomialCoefficient(f,B.1^i*B.2^(n-i)) : i in [0..n]];
    for k in [0..n-4] do
        Append(~Q,&+[(P!coeffs[i+1])*mons[pivots[i+k+1]] : i in [0..n]]);
    end for;
    assert #Q eq n*(n-3) div 2;
    return Q;
end intrinsic;

intrinsic FiniteFlatCover(f::RngMPolElt : CoverDegree := 0, ProjectiveBase := false, Twisted := true,
    VariableWeights := [], EquationWeights := [], RowWeights := [], MatrixTwist := 0,
    Embedding := "Model", AssumeFiniteFlat := false, CheckAlgebra := false) -> FinFlatCov
{Construct from a homogeneous binary form (including forms with a zero x^n coefficient), or a
 rank-one multivariate polynomial ring.}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    P := Parent(f);
    R := BaseRing(P);
    require Type(Twisted) eq BoolElt: "Twisted must be a boolean";
    if Rank(P) eq 1 then
        U := FFCNamedPolynomialRing(R,1,[Sprint(Name(P,1))]);
        return FiniteFlatCover(Evaluate(f,[U.1]) : CoverDegree := CoverDegree, ProjectiveBase := ProjectiveBase,
            Twisted := Twisted, VariableWeights := VariableWeights, EquationWeights := EquationWeights,
            RowWeights := RowWeights, MatrixTwist := MatrixTwist, Embedding := Embedding,
            AssumeFiniteFlat := AssumeFiniteFlat,
            CheckAlgebra := CheckAlgebra);
    end if;
    require Rank(P) eq 2 and (f eq 0 or IsHomogeneous(f)): "Input must be a homogeneous binary form";
    d := CoverDegree eq 0 select Degree(f) else CoverDegree;
    require d ge 1 and (f eq 0 or Degree(f) eq d): "Specify a positive CoverDegree for zero forms; otherwise degrees must agree";
    require Embedding in {"Algebra","Model"}: "Embedding must be Algebra or Model";
    a := [MonomialCoefficient(f,P.1^i*P.2^(d-i)) : i in [0..d]];
    if d eq 1 then
        C := IdentityFiniteFlatCover(R : ProjectiveBase := ProjectiveBase);
        C`Twisted := Twisted;
        return C;
    end if;
    // Infer from the INPUT form before converting it to a different model.
    // For polynomial input in degrees 3--5, automatic grading also fixes the
    // actual tensor frame in FV order: e_i and f_i increase left to right.
    // Explicit model weights are an expert override and preserve the supplied frame.
    orderFV := false;
    pe := [];
    pf := [];
    if ProjectiveBase and #VariableWeights eq 0 and #RowWeights eq 0 and MatrixTwist eq 0 then
        VariableWeights,RowWeights,MatrixTwist,eRaw,fRaw,pe,pf := FFCBinaryModelWeights(a,d);
        orderFV := d in {3,4,5};
    end if;
    if d le 5 then
        if d le 3 then
            PM := FFCCoordinateRing(R,2);
            M := Evaluate(f,[PM.1,PM.2]);
        else
            M := FFCModelFromBinaryCoefficients(a,d);
        end if;
        if orderFV then
            M := FFCOrderPolynomialModel(M,d,pe,pf);
        end if;
        C := FFCConstruct(M,d,R,ProjectiveBase,VariableWeights,EquationWeights,RowWeights,MatrixTwist,
            Embedding,AssumeFiniteFlat,CheckAlgebra);
        C`Twisted := Twisted;
        return C;
    end if;
    require #RowWeights eq 0 and MatrixTwist eq 0:
        "RowWeights and MatrixTwist are specific to quintic alternating models";
    primitive := FFCCertifiablyPrimitive(a);
    if primitive or AssumeFiniteFlat or Embedding eq "Model" then
        Q := CanonicalQuadrics(f : CoverDegree := d);
        C := FiniteFlatCoverFromQuadrics(Q : CoverDegree := d, ProjectiveBase := ProjectiveBase, Twisted := Twisted,
            VariableWeights := VariableWeights, EquationWeights := EquationWeights,
            Embedding := Embedding, AssumeFiniteFlat := primitive or AssumeFiniteFlat, CheckAlgebra := CheckAlgebra);
        if primitive then
            C`_Data`Presentation`Flatness := "Verified";
        end if;
        return C;
    end if;
    require not ProjectiveBase: "For a higher-degree Proj binary model supply compatible bundle weights and AssumeFiniteFlat; use an explicit graded multiplication table for a non-Gorenstein cover";
    require #VariableWeights eq 0 and #EquationWeights eq 0 and #RowWeights eq 0 and MatrixTwist eq 0:
        "Bundle weights are not used for this affine algebra fallback";
    C := FFCBinaryAlgebraCover(f,d,R);
    C`Twisted := Twisted;
    if CheckAlgebra then
        require IsAssociative(C): "The binary-form multiplication is not associative";
    end if;
    return C;
end intrinsic;

intrinsic FiniteFlatCover(f::RngUPolElt : CoverDegree := 0, ProjectiveBase := false, Twisted := true,
    VariableWeights := [], EquationWeights := [], RowWeights := [], MatrixTwist := 0,
    Embedding := "Model", AssumeFiniteFlat := false, CheckAlgebra := false) -> FinFlatCov
{Homogenize f to CoverDegree (default Degree(f)). For a nonmonic polynomial this is the
 binary-form ring, not generally R[z]/(f).}
    require Type(ProjectiveBase) eq BoolElt: "ProjectiveBase must be true or false";
    R := BaseRing(Parent(f));
    d := CoverDegree eq 0 select Degree(f) else CoverDegree;
    require d ge 1 and Degree(f) le d: "CoverDegree must be positive and at least Degree(f)";
    P := FFCCoordinateRing(R,2);
    F := &+[(P!Coefficient(f,i))*P.1^i*P.2^(d-i) : i in [0..d]];
    return FiniteFlatCover(F : CoverDegree := d, ProjectiveBase := ProjectiveBase, Twisted := Twisted,
        VariableWeights := VariableWeights, EquationWeights := EquationWeights,
        RowWeights := RowWeights, MatrixTwist := MatrixTwist, Embedding := Embedding,
        AssumeFiniteFlat := AssumeFiniteFlat,
        CheckAlgebra := CheckAlgebra);
end intrinsic;
