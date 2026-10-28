// Cheap inspection. No accessor in this file performs algebra or geometry.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

intrinsic Print(C::FinFlatCov, level::MonStgElt)
{Print a finite flat cover and its chosen presentation.}
    if not assigned C`Degree then
        printf "Uninitialized finite flat cover";
        return;
    end if;
    printf "Finite flat cover of degree %o", C`Degree;
    if assigned C`ProjectiveBase and assigned C`CoefficientRing then
        printf " over %o(%o)", C`ProjectiveBase select "Proj" else "Spec", C`CoefficientRing;
    end if;
    if assigned C`Embedding then
        printf "; embedding: %o", C`Embedding;
    end if;
end intrinsic;

intrinsic Degree(C::FinFlatCov) -> RngIntElt
{The finite locally free rank.}
    return C`Degree;
end intrinsic;

intrinsic BaseRing(C::FinFlatCov) -> Rng
{The affine coefficient ring, or the homogeneous base ring for a Proj base.}
    return C`CoefficientRing;
end intrinsic;

intrinsic Model(C::FinFlatCov) -> .
{Return the stored defining model without performing any computation.
 For Bhargava models of degree 2 or 3 this is the homogeneous binary form;
 in degree 4 it is the pair of 3 by 3 symmetric coefficient matrices;
 in degree 5 it is the quadruple of 5 by 5 alternating matrices.
 For a higher-degree resolution model, the supplied partial/full resolution is returned
 unchanged; use ResolutionMaps to complete it. Explicit algebra-table covers return
 their supplied table, since no canonical Bhargava tensor is determined by such input.}
    require assigned C`Model: "This cover has no stored defining model";
    return C`Model;
end intrinsic;

intrinsic ProjectiveBase(C::FinFlatCov) -> BoolElt
{Whether the base is Proj(R), rather than Spec(R).}
    return C`ProjectiveBase;
end intrinsic;

intrinsic CachedComputations(C::FinFlatCov) -> SeqEnum
{Names of already computed results. Does not compute them; deferred jobs are not results.}
    names := [];
    if assigned C`StructureConstants then
        Append(~names,"StructureConstants");
    end if;
    if assigned C`Discriminant then
        Append(~names,"Discriminant");
    end if;
    if assigned C`DefiningPolynomials then
        Append(~names,"DefiningPolynomials");
    end if;
    if assigned C`UnderlyingScheme then
        Append(~names,"UnderlyingScheme");
    end if;
    if assigned C`_Data`Presentation`Polynomials then
        Append(~names,"ModelPolynomials");
    end if;
    if assigned C`_Data`Algebra`Matrices then
        Append(~names,"MultiplicationMatrices");
    end if;
    if assigned C`_Data`Algebra`Traces then
        Append(~names,"TraceVector");
    end if;
    if assigned C`_Data`Algebra`Pairing then
        Append(~names,"TracePairing");
    end if;
    if assigned C`_Data`Algebra`TraceDiscriminant then
        Append(~names,"TraceDiscriminant");
    end if;
    if assigned C`_Data`Algebra`Associative then
        Append(~names,"IsAssociative");
    end if;
    if assigned C`_Data`Resolution`Maps then
        Append(~names,"ResolutionMaps");
    end if;
    if assigned C`_Data`Resolution`FirstSyzygies then
        Append(~names,"FirstSyzygies");
    end if;
    if assigned C`_Data`Resolution`Exact then
        Append(~names,"VerifyResolution");
    end if;
    if assigned C`_Data`Geometry`CoxModel then
        Append(~names,"CoxModelData");
    end if;
    if assigned C`_Data`Geometry`CoxAlgebra then
        Append(~names,"CoxAlgebraData");
    end if;
    if assigned C`_Data`Geometry`ModelScheme then
        Append(~names,"ModelScheme");
    end if;
    if assigned C`_Data`Resolvents`Standard then
        Append(~names,"Resolvent");
    end if;
    if assigned C`_Data`Resolvents`Conjectural then
        Append(~names,"ConjecturalSexticResolvent");
    end if;
    if assigned C`_Data`Bundle`Tschirnhausen then
        Append(~names,"TschirnhausenInvariants");
    end if;
    if assigned C`_Data`Bundle`FirstSyzygy then
        Append(~names,"FirstSyzygyInvariants");
    end if;
    Sort(~names);
    return names;
end intrinsic;

intrinsic FiniteFlatCoverVersion() -> MonStgElt
{Version of this attached implementation. Does not inspect or modify a cover.}
    return "16.0.1";
end intrinsic;
