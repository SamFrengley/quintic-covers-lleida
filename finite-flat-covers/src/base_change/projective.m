// Projective patches and generic fibres.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "primes.m": FFCGroundField;
import "../core/maps.m": FFCMapWithImages;
import "../core/names.m": FFCBaseCoordinateNames, FFCNamedFunctionField,
    FFCNamedPolynomialRing;

intrinsic CoverPatch(C::FinFlatCov, chart::RngIntElt) -> FinFlatCov, Map
{Trivialise over the first or second nonzero base coordinate. The remaining affine coordinate keeps
 the name supplied on the original base.}
    require C`ProjectiveBase and chart in {1,2}: "Choose chart 1 or 2 of a Proj base";
    R := BaseRing(C);
    names := FFCBaseCoordinateNames(R);
    free := chart eq 1 select 2 else 1;
    S := FFCNamedPolynomialRing(BaseRing(R),1,[names[free]]);
    u := S.1;
    values := chart eq 1 select [S!1,u] else [u,S!1];
    phi := FFCMapWithImages(R,S,values);
    D,phi := BaseChange(C,phi);
    return D,phi;
end intrinsic;

intrinsic GenericFibre(C::FinFlatCov : Homogeneous := true) -> FinFlatCov, Map
{The generic field fibre; retained base coordinates keep their original names. Homogeneous := false
 removes the extra scaling variable on a Proj base.}
    R := BaseRing(C);
    if IsField(R) then
        phi := map<R -> R | a :-> a>;
        return BaseChange(C,phi);
    end if;
    if Type(R) eq RngInt then
        K := Rationals();
        phi := FFCMapWithImages(R,K,[]);
        return BaseChange(C,phi);
    end if;
    require Type(R) in {RngUPol,RngMPol}: "GenericFibre supports Z and polynomial bases over Z or a field";
    k := FFCGroundField(R);
    n := Type(R) eq RngUPol select 1 else Rank(R);
    names := FFCBaseCoordinateNames(R);
    if C`ProjectiveBase and not Homogeneous then
        K := FFCNamedFunctionField(k,1,[names[1]]);
        values := [K.1,K!1];
    else
        K := FFCNamedFunctionField(k,n,names);
        values := [K.i : i in [1..n]];
    end if;
    phi := FFCMapWithImages(R,K,values);
    return BaseChange(C,phi);
end intrinsic;
