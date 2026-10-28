// core / arithmetic
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

function FFCExactHalf(a)
    R := Parent(a);
    if Characteristic(R) eq 2 then
        error "A Hessian has lost its diagonal in characteristic 2; supply coefficients instead";
    end if;
    if IsField(R) then
        return a/(R!2);
    end if;
    ok,q := IsDivisibleBy(a,R!2);
    if not ok then
        error "The Hessian diagonal is not divisible by 2 over the input ring";
    end if;
    return q;
end function;

function FFCIntegralInverse(M)
    /* Inverse only of a previously checked unimodular matrix. Coerce back:
       Magma may otherwise return a matrix over a fraction field. */
    R := BaseRing(M);
    return Matrix(R,Nrows(M),Ncols(M),[R!a : a in Eltseq(M^-1)]);
end function;

function FFCIsHomogeneousOfDegree(f,e)
    if f eq 0 then
        return true;
    end if;
    if e lt 0 then
        return false;
    end if;
    return forall{m : m in Monomials(f) | &+Exponents(m) eq e};
end function;

forward FFCIsUnit;

function FFCIsUnit(a)
    R := Parent(a);
    if IsField(R) then
        return a ne 0;
    end if;
    if Type(R) eq RngInt then
        return a eq 1 or a eq -1;
    end if;
    if Type(R) eq RngUPol then
        return Degree(a) eq 0 and FFCIsUnit(Coefficient(a,0));
    end if;
    if Type(R) eq RngMPol then
        if a eq 0 or Degree(a) ne 0 then
            return false;
        end if;
        return FFCIsUnit(Coefficients(a)[1]);
    end if;
    return IsUnit(a);
end function;

function FFCSign(p)
    z := 1;
    for i in [1..#p] do
        for j in [i+1..#p] do
            if p[i] gt p[j] then
                z := -z;
            end if;
        end for;
    end for;
    return z;
end function;

function FFCActionField(R)
    // All actions are formed over the generic coefficient field and are
    // descended afterwards.  This is deliberately separate from BaseChange.
    if IsField(R) then
        return R;
    end if;
    return FieldOfFractions(R);
end function;

function FFCDescendElement(x,R,label)
    // Exact membership test in R.  The second branch handles fraction-field
    // representations whose numerator/denominator have not been cancelled by
    // the parent automatically.
    ok,y := IsCoercible(R,x);
    if ok then
        return y;
    end if;
    if IsField(R) then
        error Sprintf("%o does not lie in the coefficient field",label);
    end if;
    K := Parent(x);
    if IsField(K) then
        a := Numerator(x);
        b := Denominator(x);
        oka,aa := IsCoercible(R,a);
        okb,bb := IsCoercible(R,b);
        if oka and okb and bb ne 0 then
            if Type(R) eq RngInt then
                if aa mod bb eq 0 then
                    return aa div bb;
                end if;
            elif Type(R) in {RngUPol,RngMPol} then
                divok,q := IsDivisibleBy(aa,bb);
                if divok then
                    return q;
                end if;
            end if;
        end if;
    end if;
    error Sprintf("%o is not integral over the coefficient ring",label);
end function;
