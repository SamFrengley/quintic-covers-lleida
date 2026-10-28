// Experimental lifting backend; fresh characteristic-two input must be etale.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/basis.m": FFCBasisTransform;
import "envelope.m": FFCCorrectionDefects, FFCCorrectionPolynomial, FFCHalfTraceBasis;

forward FFCTwoLiftData;

function FFCTwoLiftData(K)
    if Type(K) eq FldFin then
        if Characteristic(K) ne 2 then
            error "Expected a characteristic-two field";
        end if;
        E := PrimeField(K);
        d := Degree(K);
        if d eq 1 then
            L := Rationals();
            lift := func<x | L!(Integers()!x)>;
            red := function(x)
                x := L!x;
                if IsEven(Denominator(x)) then
                    error "Nonintegral 2-adic coefficient in corrected table";
                end if;
                return K!Numerator(x)/K!Denominator(x);
            end function;
            val := func<x | Valuation(Numerator(L!x),2)-Valuation(Denominator(L!x),2)>;
            return L,lift,red,val;
        end if;
        P := PolynomialRing(Rationals());
        f := DefiningPolynomial(K,E);
        L := NumberField(P![Integers()!c : c in Coefficients(f)]);
        b := Generator(K,E);
        lift := function(x)
            c := Eltseq(K!x,E);
            return &+[(L!(Integers()!c[i]))*L.1^(i-1) : i in [1..#c]];
        end function;
        red := function(x)
            c := Eltseq(L!x);
            if exists{a : a in c | IsEven(Denominator(a))} then
                error "Nonintegral coefficient in the unramified characteristic-two lift";
            end if;
            return &+[(K!Numerator(c[i])/K!Denominator(c[i]))*b^(i-1) : i in [1..#c]];
        end function;
        val := function(x)
            c := [a : a in Eltseq(L!x) | a ne 0];
            if #c eq 0 then
                error "Valuation helper requires a nonzero argument";
            end if;
            return Minimum([Valuation(Numerator(a),2)-Valuation(Denominator(a),2) : a in c]);
        end function;
        return L,lift,red,val;
    end if;
    if Type(K) eq FldFunRat then
        k := BaseRing(K);
        L0,up0,down0,v0 := FFCTwoLiftData(k);
        n := Rank(K);
        L := FunctionField(L0,n);
        up_poly := func<f | FFCCorrectionPolynomial(f,up0,[L.i : i in [1..n]])>;
        down_poly := func<f | FFCCorrectionPolynomial(f,down0,[K.i : i in [1..n]])>;
        lift := func<x | up_poly(Numerator(x))/up_poly(Denominator(x))>;
        val_poly := function(f)
            return Minimum([v0(a) : a in Coefficients(f) | a ne 0]);
        end function;
        red := function(x)
            x := L!x;
            if x eq 0 then
                return K!0;
            end if;
            a := Numerator(x);
            b := Denominator(x);
            v := val_poly(b);
            scale := L0!2^(-v);
            a := scale*a;
            b := scale*b;
            aa := down_poly(a);
            bb := down_poly(b);
            if bb eq 0 then
                error "Characteristic-two reduction has a zero denominator";
            end if;
            return aa/bb;
        end function;
        val := func<x | val_poly(Numerator(L!x))-val_poly(Denominator(L!x))>;
        return L,lift,red,val;
    end if;
    error "Fresh characteristic-two correction supports finite fields and rational function fields over them; specialize a corrected mixed-characteristic cover for other bases";
end function;

function FFCCharacteristicTwoCorrection(C)
    K := BaseRing(C);
    if not IsField(K) then
        error "For a characteristic-two polynomial base first correct a mixed-characteristic lift and BaseChange it, or pass to a field fibre";
    end if;
    // Rank, not determinant: neither discriminant cache is populated here.
    if Rank(TracePairing(C)) ne 5 then
        error "Fresh characteristic-two reconstruction requires an etale quintic; specialize a previously corrected cover to obtain degenerate fibres";
    end if;
    L,up,down,v := FFCTwoLiftData(K);
    AA := [Matrix(L,5,5,[up(a) : a in Eltseq(A)]) : A in Model(C)];
    Lift := FiniteFlatCover(AA : Twisted := C`Twisted, CheckAlgebra := false);
    Raw := BhargavaResolvent(Lift);
    T := StructureConstants(Raw);
    E := FFCHalfTraceBasis(TraceVector(Raw),L);
    U,rows,r := FFCCorrectionDefects(T,E,down);
    if #r eq 0 then
        error "An etale quintic has a nonzero sextic correction defect";
    end if;
    p := [j : j in [2..6] | r[j] ne 0][1];
    r := [a/r[p] : a in r];
    H := IdentityMatrix(L,6);
    for j in [1..6] do
        H[p,j] := up(r[j])/2;
    end for;
    N := H*E;
    V := [down(a) : a in FFCBasisTransform(T,N,6)];
    inclusion := Matrix(K,6,6,[down(a) : a in Eltseq(N^-1)]);
    return V,inclusion;
end function;
