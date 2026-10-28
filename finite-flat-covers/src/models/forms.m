// models / forms
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/arithmetic.m": FFCExactHalf;
import "multiplication.m": FFCSignedPfaffians;
import "../core/names.m": FFCCoordinateRing;

function FFCAlternating(u)
    R := Universe(u);
    A := ZeroMatrix(R,5,5);
    z := 0;
    for i in [1..5] do
        for j in [i+1..5] do
            z +:= 1;
            A[i,j] := u[z];
            A[j,i] := -u[z];
        end for;
    end for;
    return A;
end function;

function FFCConvertSymmetric(A,convention)
    if Nrows(A) ne 3 or Ncols(A) ne 3 or Transpose(A) ne A then
        error "Quartic matrices must be symmetric 3 by 3 matrices";
    end if;
    B := A;
    if convention eq "Coefficients" then
        return B;
    end if;
    if convention eq "Hessian" then
        for i in [1..3] do
            B[i,i] := FFCExactHalf(A[i,i]);
        end for;
        return B;
    end if;
    if convention eq "Gram" then
        for i in [1..3] do
            for j in [i+1..3] do
                B[i,j] := 2*A[i,j];
                B[j,i] := B[i,j];
            end for;
        end for;
        return B;
    end if;
    error "ModelConvention must be Coefficients, Hessian or Gram";
end function;

function FFCTableToQuadric(A,P)
    n := Nrows(A);
    q := P!0;
    for i in [1..n] do
        for j in [i..n] do
            q +:= (P!A[i,j])*P.i*P.j;
        end for;
    end for;
    return q;
end function;

function FFCModelEquations(M,d,R)
    if d eq 1 then
        P := FFCCoordinateRing(R,2);
        return [P.2];
    end if;
    if d in {2,3} then
        return [M];
    end if;
    n := d-1;
    P := FFCCoordinateRing(R,n);
    if d eq 4 then
        return [FFCTableToQuadric(A,P) : A in M];
    end if;
    N := ZeroMatrix(P,5,5);
    for i in [1..4] do
        N +:= P.i*ChangeRing(M[i],P);
    end for;
    return Eltseq(FFCSignedPfaffians(N));
end function;

function FFCQuadricToTable(q)
    P := Parent(q);
    R := BaseRing(P);
    n := Rank(P);
    A := ZeroMatrix(R,n,n);
    for i in [1..n] do
        for j in [i..n] do
            A[i,j] := MonomialCoefficient(q,P.i*P.j);
            A[j,i] := A[i,j];
        end for;
    end for;
    return A;
end function;

function FFCModelFromBinaryCoefficients(a,d)
    R := Universe(a);
    if d in {2,3} then
        P := FFCCoordinateRing(R,2);
        return &+[a[i+1]*P.1^i*P.2^(d-i) : i in [0..d]];
    end if;
    if d eq 4 then
        P := FFCCoordinateRing(R,3);
        x,y,z := Explode([P.i : i in [1..3]]);
        Q := [x^2-y*z, a[1]*z^2+a[2]*x*z+a[3]*y*z+a[4]*x*y+a[5]*y^2];
        return [FFCQuadricToTable(q) : q in Q];
    end if;
    a0,a1,a2,a3,a4,a5 := Explode(a);
    return [
        FFCAlternating([R|-a0,-a1,0,0,-a2,0,0,0,-1,0]),
        FFCAlternating([R|0,0,0,0,a3,0,1,1,0,0]),
        FFCAlternating([R|0,-a3,0,-1,-a4,-1,0,0,0,0]),
        FFCAlternating([R|-a3,0,1,0,-a5,0,0,0,0,0])
    ];
end function;

function FFCTransformQuadratic(A,g)
    // q_A(g^t x), in coefficient-table convention. No division or fibre ring.
    R := BaseRing(A);
    n := Nrows(A);
    B := ZeroMatrix(R,n,n);
    for a in [1..n] do
        B[a,a] := &+[A[i,i]*g[a,i]^2 : i in [1..n]];
        for i in [1..n] do
            for j in [i+1..n] do
                B[a,a] +:= A[i,j]*g[a,i]*g[a,j];
            end for;
        end for;
        for b in [a+1..n] do
            value := &+[2*A[i,i]*g[a,i]*g[b,i] : i in [1..n]];
            for i in [1..n] do
                for j in [i+1..n] do
                    value +:= A[i,j]*(g[a,i]*g[b,j]+g[a,j]*g[b,i]);
                end for;
            end for;
            B[a,b] := value;
            B[b,a] := value;
        end for;
    end for;
    return B;
end function;
