// resolution / constants
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/basis.m": FFCAnchors;
import "../algebra/tables.m": FFCBlank, FFCConstantTerms, FFCGet, FFCPut;
import "../core/arithmetic.m": FFCSign;

function FFCSlice(A,mon)
    R := BaseRing(BaseRing(A));
    return Matrix(R,Nrows(A),Ncols(A),[MonomialCoefficient(f,mon) : f in Eltseq(A)]);
end function;

function FFCFRCoefficients(C)
    if assigned C`_Data`Resolution`Slices then
        return C`_Data`Resolution`Slices;
    end if;
    F := ResolutionMaps(C);
    P := BaseRing(F[1]);
    r := Rank(P);
    ends := [* [* FFCSlice(F[1],P.i*P.j) : j in [1..r] *] : i in [1..r] *];
    tails := [* [* FFCSlice(F[#F],P.i*P.j) : j in [1..r] *] : i in [1..r] *];
    middles := [* [* FFCSlice(F[a],P.i) : i in [1..r] *] : a in [2..#F-1] *];
    data := <ends,middles,tails>;
    C`_Data`Resolution`Slices := data;
    return data;
end function;

function FFCFRBracket(C,a)
    if not assigned C`_Data`Resolution`Brackets then
        C`_Data`Resolution`Brackets := AssociativeArray();
    end if;
    key := Sprint(a);
    if IsDefined(C`_Data`Resolution`Brackets,key) then
        return C`_Data`Resolution`Brackets[key];
    end if;
    data := FFCFRCoefficients(C);
    n := Degree(C);
    u := data[1][a[1]][a[2]];
    for i in [1..n-4] do
        u := u*data[2][i][a[i+2]];
    end for;
    z := (u*data[3][a[n-1]][a[n]])[1,1];
    C`_Data`Resolution`Brackets[key] := z;
    return z;
end function;

function FFCFRConstants(C)
    /* Fisher--Radicevic, Theorem 10.1, equations (17)--(20), divided
       SYMBOLICALLY by 2n using the bracket identities: NO division in R. */
    n := Degree(C);
    R := BaseRing(C);
    T := FFCBlank(R,n);
    a := FFCAnchors(n);
    for i in [1..n-1] do
        for j in [i+1..n-1] do
            for k in [1..n-1] do
                if k in {i,j} then
                    continue;
                end if;
                rest := [l : l in [1..n-1] | l notin {i,j,k}];
                z := (-1)^(n+1)*FFCSign([i,j,k] cat rest)*FFCFRBracket(C,[i,i] cat rest cat [j,j]);
                FFCPut(~T,n,i,j,k,z);
            end for;
        end for;
        for j in [1..n-1] do
            if j eq i then
                continue;
            end if;
            rest := [l : l in [1..n-1] | l notin {i,j}];
            z := FFCSign([i,j] cat rest)*FFCFRBracket(C,[i,i] cat rest cat [i]);
            FFCPut(~T,n,i,i,j,z);
        end for;
        k := a[i];
        FFCPut(~T,n,i,k,k,R!0);
        for j in [1..n-1] do
            if j in {i,k} then
                continue;
            end if;
            rest := [l : l in [1..n-1] | l notin {i,j,k}];
            z := (-1)^n*FFCSign([i,j,k] cat rest)*FFCFRBracket(C,[i,i] cat rest cat [j,k]);
            FFCPut(~T,n,i,j,j,z);
        end for;
    end for;
    for i in [1..n-1] do
        rem := [l : l in [1..n-1] | l ne i];
        j := rem[1];
        k := rem[2];
        rest := [l : l in [1..n-1] | l notin {i,j,k}];
        z := (-1)^(n+1)*FFCSign([i,j,k] cat rest)*FFCFRBracket(C,[i,j] cat rest cat [k,i]);
        FFCPut(~T,n,i,i,i,FFCGet(T,n,i,j,j)+FFCGet(T,n,i,k,k)+z);
    end for;
    FFCConstantTerms(~T,n);
    return T;
end function;
