// Experimental integral envelope and checked lattice operations.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/basis.m": FFCBasisTransform;
import "../algebra/tables.m": FFCGet;
import "../core/arithmetic.m": FFCIntegralInverse;

function FFCCorrectionPolynomial(f,coefficient,values)
    R := Parent(values[1]);
    z := R!0;
    if f eq 0 then
        return z;
    end if;
    if Type(Parent(f)) eq RngUPol then
        for i in [0..Degree(f)] do
            z +:= coefficient(Coefficient(f,i))*values[1]^i;
        end for;
    else
        cc,mm := CoefficientsAndMonomials(f);
        for i in [1..#cc] do
            ex := Exponents(mm[i]);
            z +:= coefficient(cc[i])*(&*[values[j]^ex[j] : j in [1..#values]]);
        end for;
    end if;
    return z;
end function;

function FFCCorrectionCoerce(x,R)
    ok,y := IsCoercible(R,x);
    if ok then
        return y;
    end if;
    if Type(R) in {RngUPol,RngMPol} and Type(Parent(x)) eq FldFunRat then
        a := Numerator(x);
        b := Denominator(x);
        if b ne 0 and Degree(b) eq 0 then
            c := Coefficients(b)[1];
            n := Type(R) eq RngUPol select 1 else Rank(R);
            coef := func<v | R!(BaseRing(R)!(v/c))>;
            return FFCCorrectionPolynomial(a,coef,[R.i : i in [1..n]]);
        end if;
    end if;
    error "Trace-halving correction is not integral in the requested coefficient ring; no fractional table has been returned";
end function;

function FFCCorrectionDefects(T,E,residue)
    U := FFCBasisTransform(T,E,6);
    K := Parent(residue(0*U[1]));
    rows := [[residue(2*FFCGet(U,6,i,j,k)) : k in [0..5]] : i,j in [1..5] | i le j];
    nonzero := [r : r in rows | exists{a : a in r | a ne 0}];
    if #nonzero eq 0 then
        return U,rows,[];
    end if;
    r := nonzero[1];
    pivs := [j : j in [2..6] | r[j] ne 0];
    if #pivs eq 0 then
        error "Invalid scalar-only correction defect";
    end if;
    p := pivs[1];
    if not forall{a : a in rows | forall{k : k in [1..6] | a[k]*r[p] eq a[p]*r[k]}} then
        error "The trace-halving defect does not have rank at most one";
    end if;
    return U,rows,r;
end function;

function FFCCorrectionLift(x,R)
    if Type(Parent(x)) eq FldFin then
        return R!(Integers()!x);
    end if;
    n := Type(Parent(x)) eq RngUPol select 1 else Rank(Parent(x));
    coef := func<c | R!(Integers()!c)>;
    return FFCCorrectionPolynomial(x,coef,[R.i : i in [1..n]]);
end function;

function FFCCorrectionResidue(x,R,K)
    y := FFCCorrectionCoerce(x,R);
    if Type(R) eq RngInt then
        return K!y;
    end if;
    n := Type(R) eq RngUPol select 1 else Rank(R);
    coef := func<c | K!(Integers()!c)>;
    return FFCCorrectionPolynomial(y,coef,[K.i : i in [1..n]]);
end function;

function FFCHalfTraceBasis(traces,K)
    B := IdentityMatrix(K,6);
    for i in [1..5] do
        tr := K!traces[i+1];
        B[i+1,i+1] := K!1/2;
        B[i+1,1] := -tr/4;
    end for;
    return B;
end function;

function FFCIntegralTraceEnvelope(B)
    R := BaseRing(B);
    T := StructureConstants(B);
    if not (Type(R) eq RngInt or
        (Type(R) in {RngUPol,RngMPol} and Type(BaseRing(R)) eq RngInt)) then
        error "Integral trace-halving currently supports Z and polynomial rings over Z";
    end if;
    F := FieldOfFractions(R);
    TT := [F!a : a in T];
    traces := TraceVector(B);
    E := FFCHalfTraceBasis(traces,F);
    // Tau must be integral before ANY reduction modulo two.
    for i in [0..5] do
        a := FFCCorrectionCoerce((F!traces[i+1])/2,R);
    end for;
    if Type(R) eq RngInt then
        K := GF(2);
    elif Type(R) eq RngUPol or (Type(R) eq RngMPol and Rank(R) eq 1) then
        // Canonicalize a rank-one multivariate parent for Euclidean completion.
        K := PolynomialRing(GF(2));
    else
        K := PolynomialRing(GF(2),Rank(R));
    end if;
    red := func<x | FFCCorrectionResidue(x,R,K)>;
    U,rows,r := FFCCorrectionDefects(TT,E,red);
    if #r eq 0 then
        V := [FFCCorrectionCoerce(a,R) : a in U];
        inc := Matrix(R,6,6,[FFCCorrectionCoerce(a,R) : a in Eltseq(E^-1)]);
        return V,E,inc,R!4,"Trace-halving envelope, index 32; the source has bad reduction at 2";
    end if;
    if Type(K) ne FldFin then
        d := K!0;
        for j in [2..6] do
            d := GCD(d,r[j]);
        end for;
        rr := [];
        for a in r do
            ok,q := IsDivisibleBy(a,d);
            if not ok then
                error "The saturated defect has no integral scalar coordinate";
            end if;
            Append(~rr,q);
        end for;
        r := rr;
    end if;
    lift := func<x | FFCCorrectionLift(x,R)>;
    units := [j : j in [2..6] | r[j] eq K!1];
    if #units gt 0 then
        // This branch preserves the grading of a homogeneous defect row.
        p := units[1];
        H := IdentityMatrix(F,6);
        for j in [1..6] do
            H[p,j] := F!lift(r[j])/2;
        end for;
        N := H*E;
    else
        if Type(K) ne RngUPol then
            error "The corrected module has no unit-pivot split frame here. On Proj use ConjecturalSexticResolventCharts(C); on Spec use a polynomial chart or supply a free frame";
        end if;
        if B`ProjectiveBase then
            error "A global graded frame was not found; use ConjecturalSexticResolventCharts(C) rather than an ungraded completion";
        end if;
        // Euclidean completion lifted as elementary operations, NOT entrywise
        // lifting an arbitrary GL_5(F_2[t]) matrix (its determinant need not lift to a unit).
        u := r[2..6];
        col := IdentityMatrix(R,5);
        p := [j : j in [1..5] | u[j] ne 0][1];
        if p ne 1 then
            SwapColumns(~col,1,p);
            a := u[1];
            u[1] := u[p];
            u[p] := a;
        end if;
        for j in [2..5] do
            while u[j] ne 0 do
                q,rem := Quotrem(u[1],u[j]);
                AddColumn(~col,-lift(q),j,1);
                u[1] := rem;
                SwapColumns(~col,1,j);
                a := u[1];
                u[1] := u[j];
                u[j] := a;
            end while;
        end for;
        if u ne [K!1,K!0,K!0,K!0,K!0] then
            error "Primitive row completion failed";
        end if;
        G := IdentityMatrix(F,6);
        P := FFCIntegralInverse(col);
        for i,j in [1..5] do
            G[i+1,j+1] := F!P[i,j];
        end for;
        H := IdentityMatrix(F,6);
        H[2,2] := F!1/2;
        H[2,1] := F!lift(r[1])/2;
        N := H*G*E;
    end if;
    V := [FFCCorrectionCoerce(a,R) : a in FFCBasisTransform(TT,N,6)];
    inc := Matrix(R,6,6,[FFCCorrectionCoerce(a,R) : a in Eltseq(N^-1)]);
    // The index character is certified without evaluating a trace determinant.
    if Determinant(N)^2 ne F!1/4096 then
        error "Incorrect correction index";
    end if;
    text := Type(R) eq RngInt select "Trace-halving envelope, index 64"
else
    "Primitive-defect/reflexive trace-halving envelope, index 64";
    return V,N,inc,R!1,text;
end function;
