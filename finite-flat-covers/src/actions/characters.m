// Action normalization and discriminant characters.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/grading.m": FFCPrepareActionMatrix, FFCPrepareActionMatrixWithWeights, FFCRationalDegree;

function FFCResolveTwist(C,t)
    if Type(t) eq BoolElt then
        return t;
    end if;
    if Type(t) eq MonStgElt and t eq "Stored" then
        return C`Twisted;
    end if;
    error "Twisted must be true, false, or the default string Stored";
end function;

function FFCTensorActionData(C,g,h,tw)
    n := Degree(C);
    R := BaseRing(C);
    projective := C`ProjectiveBase;
    if n eq 4 then
        g,wnew := FFCPrepareActionMatrixWithWeights(g,R,C`_Data`Bundle`Variables,projective,true);
        h,qbar := FFCPrepareActionMatrixWithWeights(h,R,C`_Data`Bundle`Equations,projective,false);
        rnew := [];
    else
        g,rnew := FFCPrepareActionMatrixWithWeights(g,R,C`_Data`Bundle`Rows,projective,false);
        h,wnew := FFCPrepareActionMatrixWithWeights(h,R,C`_Data`Bundle`Variables,projective,true);
        qbar := [];
    end if;
    dg := Determinant(g);
    dh := Determinant(h);
    s := tw select dh^-1 else Parent(dh)!1;
    ds := 0;
    if projective then
        ok,ds := FFCRationalDegree(s,R);
        if not ok then
            error "The determinant twist is not a homogeneous rational function";
        end if;
    end if;
    if n eq 4 then
        if tw and dg ne dh then
            error "The twisted quartic action requires det(g3)=det(h2); use Twisted := false for the full untwisted product";
        end if;
        qnew := [z+ds : z in qbar];
        return g,h,s,s^2*dg*dh*g,s^12*dg^8*dh^6,wnew,qnew,[],0;
    end if;
    if tw and dg ne dh^2 then
        error "The twisted quintic action requires det(g5)=det(h4)^2; use Twisted := false for the full untwisted product";
    end if;
    tnew := C`_Data`Bundle`Twist+ds;
    return g,h,s,s^5*dg^2*dh*h,s^40*dg^16*dh^10,wnew,[],rnew,tnew;
end function;

intrinsic IsTwisted(C::FinFlatCov) -> BoolElt
{Whether the stored tensor/resolution action is determinant twisted.}
    return C`Twisted;
end intrinsic;

intrinsic DiscriminantMultiplier(C::FinFlatCov,g::Mtrx,h::Mtrx : Twisted := "Stored") -> RngElt
{The generic-fibre discriminant character. Fraction-field matrices are allowed; ActBy additionally
 checks that the transformed model descends to the coefficient ring.}
    tw := FFCResolveTwist(C,Twisted);
    n := Degree(C);
    R := BaseRing(C);
    if C`_Data`Presentation`Kind eq "Resolution" then
        g := FFCPrepareActionMatrix(g,R,C`_Data`Bundle`Variables,C`ProjectiveBase,true);
        h := FFCPrepareActionMatrix(h,R,C`_Data`Bundle`Equations,C`ProjectiveBase,false);
        return Determinant(g)^(tw select 2 else 2*n);
    end if;
    require C`_Data`Presentation`Kind eq "Bhargava" and n in {4,
        5}: "A two-matrix tensor action requires degree 4 or 5";
    gg,hh,s,L,chi,wnew,qnew,rnew,tnew := FFCTensorActionData(C,g,h,tw);
    return chi;
end intrinsic;

intrinsic DiscriminantMultiplier(C::FinFlatCov,g::Mtrx,H::List : Twisted := "Stored") -> RngElt
{Resolution character on the generic fibre.}
    require C`_Data`Presentation`Kind eq "Resolution": "List actions require a resolution model";
    n := Degree(C);
    R := BaseRing(C);
    F := ResolutionMaps(C);
    tw := FFCResolveTwist(C,Twisted);
    require #H eq #F: "Supply a basis matrix for every resolution module after F_0";
    g := FFCPrepareActionMatrix(g,R,C`_Data`Bundle`Variables,C`ProjectiveBase,true);
    HH := [* *];
    for i in [1..#H] do
        Append(~HH,FFCPrepareActionMatrix(H[i],R,C`_Data`Resolution`Weights[i+1],C`ProjectiveBase,true));
    end for;
    return HH[#HH][1,1]^(2*n-2)*Determinant(g)^(tw select 2 else 2*n);
end intrinsic;

intrinsic DiscriminantMultiplier(C::FinFlatCov,g::Mtrx,H::SeqEnum : Twisted := "Stored") -> RngElt
{Sequence variant of the resolution character.}
    return DiscriminantMultiplier(C,g,[* B : B in H *] : Twisted := Twisted);
end intrinsic;

intrinsic DiscriminantMultiplier(C::FinFlatCov,g::Mtrx : Twisted := "Stored") -> RngElt
{Discriminant character without evaluating Discriminant(C).}
    n := Degree(C);
    R := BaseRing(C);
    tw := FFCResolveTwist(C,Twisted);
    if C`_Data`Presentation`Kind eq "Algebra" then
        g := FFCPrepareActionMatrix(g,R,C`_Data`Bundle`Algebra[2..n],C`ProjectiveBase,false);
        return Determinant(g)^2;
    end if;
    if C`_Data`Presentation`Kind eq "Resolution" then
        g := FFCPrepareActionMatrix(g,R,C`_Data`Bundle`Variables,C`ProjectiveBase,true);
        return Determinant(g)^(tw select 2 else 2*n);
    end if;
    if n in {2,3} then
        g := FFCPrepareActionMatrix(g,R,C`_Data`Bundle`Variables,C`ProjectiveBase,true);
        return Determinant(g)^(tw select (n-1)*(n-2) else n*(n-1));
    end if;
    require n in {4,5}: "The identity cover has no tensor action";
    if n eq 4 then
        if Nrows(g) eq 3 then
            return DiscriminantMultiplier(C,g,IdentityMatrix(R,2) : Twisted := tw);
        end if;
        require Nrows(g) eq 2: "A quartic factor has size 3 or 2";
        return DiscriminantMultiplier(C,IdentityMatrix(R,3),g : Twisted := tw);
    end if;
    if Nrows(g) eq 5 then
        return DiscriminantMultiplier(C,g,IdentityMatrix(R,4) : Twisted := tw);
    end if;
    require Nrows(g) eq 4: "A quintic factor has size 5 or 4";
    return DiscriminantMultiplier(C,IdentityMatrix(R,5),g : Twisted := tw);
end intrinsic;
