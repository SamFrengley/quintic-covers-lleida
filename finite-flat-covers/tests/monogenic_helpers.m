/* Independent test code, intentionally not using the package's private table
   transform or monogenic construction functions. Rows of B give an explicit
   model-basis -> power-basis isomorphism. No trace-pairing inversion. */
forward TestUnit;
function TestUnit(c)
    R := Parent(c);
    if IsField(R) then
        return c ne 0;
    end if;
    if Type(R) eq RngInt then
        return Abs(c) eq 1;
    end if;
    if Type(R) eq RngUPol then
        return Degree(c) eq 0 and TestUnit(Coefficient(c,0));
    end if;
    if Type(R) eq RngMPol then
        return c ne 0 and Degree(c) eq 0 and TestUnit(Coefficients(c)[1]);
    end if;
    return IsUnit(c);
end function;
function TestInverse(B)
    R := BaseRing(B);
    assert TestUnit(Determinant(B));
    return Matrix(R,Nrows(B),Ncols(B),[R!c : c in Eltseq(B^-1)]);
end function;
function TestAnchors(n)
    if n eq 3 then
        return [2,1];
    end if;
    if n eq 4 then
        return [2,1,1];
    end if;
    if n eq 5 then
        return [2,1,4,3];
    end if;
    return [2..n-1] cat [1];
end function;
function TestSC(T,n,i,j,k)
    return T[((i*n+j)*n+k)+1];
end function;
function TestCoordinates(f)
    U := Parent(f);
    z := U.1;
    n := Degree(f);
    if n le 3 then
        return [z,U!1];
    end if;
    if n eq 4 then
        return [z,z^2,U!1];
    end if;
    return [z^i : i in [0..n-2]];
end function;
function TestImages(B,U)
    n := Nrows(B);
    return [&+[(U!B[i,j])*U.1^(j-1) : j in [1..n]] : i in [1..n]];
end function;
function TestProductRow(a,b,f,Bi)
    U := Parent(f);
    R := BaseRing(U);
    n := Degree(f);
    q := (a*b) mod f;
    return Vector(R,[Coefficient(q,k) : k in [0..n-1]])*Bi;
end function;
function CheckMonogenicIsomorphism(C,f,v)
    n := Degree(f);
    U := Parent(f);
    R := BaseRing(U);
    z := U.1;
    assert n eq Degree(C) and BaseRing(C) eq R and LeadingCoefficient(f) eq R!1;
    T := StructureConstants(C);
    if n eq 2 then
        B := IdentityMatrix(R,n);
    else
        assert #v eq n-1;
        H := Matrix(R,n-1,n-1,[Coefficient((z^a*v[j]) mod f,n-1) : a in [1..n-1], j in [1..n-1]]);
        Hi := TestInverse(H);
        B := IdentityMatrix(R,n);
        for i,j in [1..n-1] do
            B[i+1,j+1] := Hi[i,j];
        end for;
        images := TestImages(B,U);
        Bi := TestInverse(B);
        anchors := TestAnchors(n);
        shift := [R!0];
        for i in [1..n-1] do
            j := anchors[i];
            row := TestProductRow(images[i+1],images[j+1],f,Bi);
            Append(~shift,row[j+1]);
        end for;
        for i in [1..n-1] do
            B[i+1,1] -:= shift[i+1];
        end for;
        images := TestImages(B,U);
        Bi := TestInverse(B);
        found := false;
        u := R!0;
        for i in [1..n-1] do
            for j in [i..n-1] do
                row := TestProductRow(images[i+1],images[j+1],f,Bi);
                for k in [1..n-1] do
                    if TestUnit(row[k+1]) then
                        u := TestSC(T,n,i,j,k)*(R!(row[k+1]^-1));
                        found := true;
                        break;
                    end if;
                end for;
                if found then
                    break;
                end if;
            end for;
            if found then
                break;
            end if;
        end for;
        assert found and TestUnit(u);
        for i in [2..n] do
            for j in [1..n] do
                B[i,j] *:= u;
            end for;
        end for;
    end if;
    assert TestUnit(Determinant(B));
    images := TestImages(B,U);
    assert images[1] eq U!1;
    for i,j in [0..n-1] do
        difference := images[i+1]*images[j+1]-&+[(U!TestSC(T,n,i,j,k))*images[k+1] : k in [0..n-1]];
        assert difference mod f eq 0;
    end for;
    /* In addition to every product, check the simultaneous intertwiner of
       ALL multiplication matrices, using the independently computed companion. */
    Z := Matrix(R,n,n,[Coefficient(z^(j+1) mod f,i) : i in [0..n-1], j in [0..n-1]]);
    L := MultiplicationMatrices(C);
    for i in [1..n] do
        A := &+[B[i,k+1]*Z^k : k in [0..n-1]];
        assert A*Transpose(B) eq Transpose(B)*L[i];
    end for;
    /* The geometric coordinates, not the recovered basis elements, satisfy
       every equation of the small projective model. */
    for q in ModelPolynomials(C) do
        assert Evaluate(q,v) mod f eq 0;
    end for;
    return B;
end function;
procedure CheckMonogenicChart(C,f,v)
    /* This optional GB check is independent of all structure constants. */
    U := Parent(f);
    R := BaseRing(U);
    if not (IsField(R) or Type(R) eq RngInt) then
        return;
    end if;
    chart := [i : i in [1..#v] | v[i] eq U!1][1];
    keep := [i : i in [1..#v] | i ne chart];
    A := PolynomialRing(R,#keep);
    j := [j : j in [1..#keep] | v[keep[j]] eq U.1][1];
    vals := [A!0 : i in [1..#v]];
    vals[chart] := 1;
    for k in [1..#keep] do
        vals[keep[k]] := A.k;
    end for;
    q := [Evaluate(a,vals) : a in ModelPolynomials(C)];
    expected := [Evaluate(f,A.j)] cat [A.k-Evaluate(v[keep[k]],A.j) : k in [1..#keep] | k ne j];
    assert ideal<A | q> eq ideal<A | expected>;
end procedure;
