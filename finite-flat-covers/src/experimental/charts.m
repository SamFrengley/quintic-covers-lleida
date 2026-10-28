// experimental / charts
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

intrinsic ConjecturalSexticResolventCharts(C::FinFlatCov) -> Tup
{For a quintic over Proj Z[s,t], return <s-chart sextic,t-chart sextic,transition>. The
 transition expresses the s-chart basis in the t-chart basis, with u=s/t. Cached; no
 discriminants.}
    require Degree(C) eq 5 and C`ProjectiveBase: "Expected a quintic over a Proj base";
    require Type(BaseRing(BaseRing(C))) eq RngInt: "This atlas backend currently uses integral mixed characteristic charts";
    if assigned C`_Data`Resolvents`Atlas then
        return C`_Data`Resolvents`Atlas;
    end if;
    A0,pa := CoverPatch(C,1);
    B0,pb := CoverPatch(C,2);
    A := FiniteFlatCover(Model(A0) : Twisted := C`Twisted, CheckAlgebra := false);
    B := FiniteFlatCover(Model(B0) : Twisted := C`Twisted, CheckAlgebra := false);
    SA := ConjecturalSexticResolvent(A);
    SB := ConjecturalSexticResolvent(B);
    Raw := BhargavaResolvent(C);
    w := Raw`_Data`Bundle`Algebra;
    K<u> := FunctionField(Rationals());
    evalfrac := function(x,y)
        a := Numerator(x);
        b := Denominator(x);
        if Type(Parent(a)) eq RngUPol then
            return Evaluate(a,y)/Evaluate(b,y);
        end if;
        if Type(Parent(a)) eq RngMPol then
            return Evaluate(a,[y])/Evaluate(b,[y]);
        end if;
        return K!x;
    end function;
    NA := Matrix(K,6,6,[evalfrac(a,1/u) : a in Eltseq(SA`_Data`Resolvents`BasisChange)]);
    NB := Matrix(K,6,6,[evalfrac(a,u) : a in Eltseq(SB`_Data`Resolvents`BasisChange)]);
    W := DiagonalMatrix(K,[u^(-a) : a in w]);
    J := NA*W*NB^-1;
    // Certify that transition and inverse lie in GL_6(Z[u,u^-1]).
    for M in [J,J^-1] do
        for x in Eltseq(M) do
            if x eq 0 then
                continue;
            end if;
            den := Denominator(x);
            if Type(Parent(den)) eq RngUPol then
                require den eq LeadingCoefficient(den)*Parent(den).1^Degree(den):
                    "Atlas transition has a non-Laurent denominator";
                c := LeadingCoefficient(den);
            else
                require #Monomials(den) eq 1: "Atlas transition has a non-Laurent denominator";
                c := Coefficients(den)[1];
            end if;
            require forall{a : a in Coefficients(Numerator(x)) | IsIntegral(a/c)}:
                "Atlas transition is not integral on the overlap";
        end for;
    end for;
    C`_Data`Resolvents`Atlas := <SA,SB,J>;
    return C`_Data`Resolvents`Atlas;
end intrinsic;
