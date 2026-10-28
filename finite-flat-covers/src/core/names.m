// Naming helpers for base rings and fibre coordinate rings.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

function FFCBaseCoordinateNames(R)
    if Type(R) eq RngUPol then
        return [Sprint(Name(R,1))];
    end if;
    if Type(R) eq RngMPol or Type(R) eq FldFunRat then
        return [Sprint(Name(R,i)) : i in [1..Rank(R)]];
    end if;
    return [];
end function;

function FFCCoordinateRing(R,n)
    P<[X]> := PolynomialRing(R,n);
    return P;
end function;

function FFCNamedPolynomialRing(k,n,names)
    P := n eq 1 select PolynomialRing(k) else PolynomialRing(k,n);
    if #names eq n then
        AssignNames(~P,names);
    end if;
    return P;
end function;

function FFCNamedFunctionField(k,n,names)
    K := n eq 1 select FunctionField(k) else FunctionField(k,n);
    if #names eq n then
        AssignNames(~K,names);
    end if;
    return K;
end function;

function FFCNamedExtension(k,g,name)
    if Degree(g) eq 1 then
        return k,-Coefficient(g,0)/Coefficient(g,1);
    end if;
    K<a> := ext<k | g>;
    if name ne "" then
        AssignNames(~K,[name]);
        a := K.1;
    end if;
    return K,a;
end function;
