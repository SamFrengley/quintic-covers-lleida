// Generic-field action helpers and exact descent to the stored coefficient ring.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/arithmetic.m": FFCDescendElement, FFCIsUnit;
import "../core/names.m": FFCCoordinateRing;

function FFCDescendMatrix(M,R,label)
    return Matrix(R,Nrows(M),Ncols(M),[
        FFCDescendElement(M[i,j],R,Sprintf("%o entry (%o,%o)",label,i,j))
        : i in [1..Nrows(M)], j in [1..Ncols(M)]
    ]);
end function;

function FFCDescendPolynomial(f,P,label)
    R := BaseRing(P);
    z := P!0;
    if f eq 0 then
        return z;
    end if;
    cc,mm := CoefficientsAndMonomials(f);
    for i in [1..#cc] do
        a := FFCDescendElement(cc[i],R,Sprintf("%o coefficient",label));
        z +:= a*Monomial(P,Exponents(mm[i]));
    end for;
    return z;
end function;

function FFCDescendPolynomialMatrix(M,P,label)
    return Matrix(P,Nrows(M),Ncols(M),[
        FFCDescendPolynomial(M[i,j],P,Sprintf("%o entry (%o,%o)",label,i,j))
        : i in [1..Nrows(M)], j in [1..Ncols(M)]
    ]);
end function;

function FFCActionPolynomialRing(P,K)
    Q := FFCCoordinateRing(K,Rank(P));
    return Q;
end function;

function FFCLiftPolynomialToActionField(f,Q)
    z := Q!0;
    if f eq 0 then
        return z;
    end if;
    cc,mm := CoefficientsAndMonomials(f);
    for i in [1..#cc] do
        z +:= (BaseRing(Q)!cc[i])*Monomial(Q,Exponents(mm[i]));
    end for;
    return z;
end function;

function FFCIntegralAutomorphismOverR(G,R)
    entries := [];
    for a in Eltseq(G) do
        ok,b := IsCoercible(R,a);
        if not ok then
            return false,ZeroMatrix(R,Nrows(G),Ncols(G));
        end if;
        Append(~entries,b);
    end for;
    H := Matrix(R,Nrows(G),Ncols(G),entries);
    return FFCIsUnit(Determinant(H)),H;
end function;
