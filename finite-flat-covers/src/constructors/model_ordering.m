// Reorder polynomial-derived low-degree models into FV splitting order.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

function FFCInversePermutation(p)
    q := [0 : i in [1..#p]];
    for i in [1..#p] do
        q[p[i]] := i;
    end for;
    return q;
end function;

function FFCPermuteFormVariables(f,p)
    P := Parent(f);
    q := FFCInversePermutation(p);
    return Evaluate(f,[P.(q[i]) : i in [1..#q]]);
end function;

function FFCPermuteSymmetricTable(A,p)
    R := BaseRing(A);
    n := #p;
    return Matrix(R,n,n,[A[p[i],p[j]] : i,j in [1..n]]);
end function;

function FFCPermuteAlternatingTable(A,p)
    R := BaseRing(A);
    n := #p;
    return Matrix(R,n,n,[A[p[i],p[j]] : i,j in [1..n]]);
end function;

function FFCOrderPolynomialModel(M,d,pe,pf)
    if d eq 2 then
        return M;
    end if;
    if d eq 3 then
        return pe eq [1,2] select M else FFCPermuteFormVariables(M,pe);
    end if;
    if d eq 4 then
        Q := [FFCPermuteSymmetricTable(A,pe) : A in M];
        return [Q[i] : i in pf];
    end if;
    if d eq 5 then
        Q := [FFCPermuteAlternatingTable(M[k],pf) : k in pe];
        return Q;
    end if;
    return M;
end function;
