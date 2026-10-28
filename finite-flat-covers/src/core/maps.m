// core / maps
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "names.m": FFCBaseCoordinateNames;

function FFCCoefficientImage(f,images,K)
    R := Parent(f);
    if Type(R) eq RngUPol then
        z := K!0;
        for i in [0..Degree(f)] do
            z +:= (K!Coefficient(f,i))*images[1]^i;
        end for;
        return z;
    end if;
    if Type(R) eq RngMPol then
        z := K!0;
        cc,mm := CoefficientsAndMonomials(f);
        for i in [1..#cc] do
            a := Exponents(mm[i]);
            term := K!cc[i];
            for j in [1..#a] do
                term *:= images[j]^a[j];
            end for;
            z +:= term;
        end for;
        return z;
    end if;
    return K!f;
end function;

function FFCFlatten(Q)
    R := BaseRing(Parent(Q[1]));
    k := BaseRing(R);
    n := Rank(Parent(Q[1]));
    P := PolynomialRing(k,n+2);
    base_names := FFCBaseCoordinateNames(R);
    AssignNames(~P,base_names cat [Sprintf("X[%o]",i) : i in [1..n]]);
    out := [];
    for q in Q do
        z := P!0;
        cc,mm := CoefficientsAndMonomials(q);
        for j in [1..#cc] do
            a := Exponents(mm[j]);
            c := FFCCoefficientImage(cc[j],[P.1,P.2],P);
            term := c;
            for i in [1..n] do
                term *:= P.(i+2)^a[i];
            end for;
            z +:= term;
        end for;
        Append(~out,z);
    end for;
    return out;
end function;

function FFCMapPolynomial(f,phi,P)
    z := P!0;
    cc,mm := CoefficientsAndMonomials(f);
    for i in [1..#cc] do
        z +:= (P!phi(cc[i]))*Monomial(P,Exponents(mm[i]));
    end for;
    return z;
end function;

function FFCMapWithImages(R,K,images)
    /* Natural map on constants; use BaseChange(C,phi) for other embeddings. */
    return map<R -> K | f :-> FFCCoefficientImage(f,images,K)>;
end function;
