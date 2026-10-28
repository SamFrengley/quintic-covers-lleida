// models / multiplication
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCBlank, FFCConstantTerms, FFCGet, FFCPut;
import "../core/arithmetic.m": FFCSign;

function FFCSignedPfaffians(A)
    R := BaseRing(A);
    v := [R!0 : i in [1..5]];
    for i in [1..5] do
        J := [j : j in [1..5] | j ne i];
        a,b,c,d := Explode(J);
        v[i] := (-1)^(i+1)*(A[a,b]*A[c,d]-A[a,c]*A[b,d]+A[a,d]*A[b,c]);
    end for;
    return Vector(R,v);
end function;

function FFCBilinearPfaffians(A,B)
    return FFCSignedPfaffians(A+B)-FFCSignedPfaffians(A)-FFCSignedPfaffians(B);
end function;

function FFCBinaryRingConstants(a,n)
    R := Universe(a);
    T := FFCBlank(R,n);
    b := [a[n+1-j] : j in [0..n]];
    for i in [1..n-1] do
        for j in [i..n-1] do
            v := [R!0 : k in [0..n-1]];
            for k in [Max(1,i+j-n)..i] do
                v[k+1] -:= b[i+j-k+1];
            end for;
            for k in [j+1..Min(i+j,n)] do
                if k eq n then
                    v[1] -:= b[i+j-k+1]*b[n+1];
                else
                    v[k+1] +:= b[i+j-k+1];
                end if;
            end for;
            for k in [0..n-1] do
                FFCPut(~T,n,i,j,k,v[k+1]);
            end for;
        end for;
    end for;
    return T;
end function;

function FFCQuarticConstants(A,B)
    R := BaseRing(A);
    C := FFCBlank(R,4);
    L := function(i,j,k,l)
        return A[i,j]*B[k,l]-B[i,j]*A[k,l];
    end function;
    eps := [1,-1,1];
    cc := [L(2,3,1,1),-L(1,3,2,2),L(1,2,3,3)];
    for i in [1..3] do
        for j in [1..3] do
            if i eq j then
                continue;
            end if;
            k := [r : r in [1..3] | r ne i and r ne j][1];
            z := FFCSign([i,j,k]);
            FFCPut(~C,4,i,i,i,z*L(i,k,i,j)+cc[i]);
            FFCPut(~C,4,i,i,j,z*L(i,i,i,k));
            /* Divide the INTEGER sign, not a coefficient in R. */
            FFCPut(~C,4,i,j,i,((z+eps[j]) div 2)*L(i,k,j,j));
            FFCPut(~C,4,i,j,k,z*L(j,j,i,i));
        end for;
    end for;
    FFCConstantTerms(~C,4);
    return C;
end function;

function FFCQuinticConstants(A)
    R := BaseRing(A[1]);
    C := FFCBlank(R,5);
    P := [FFCSignedPfaffians(M) : M in A];
    B := [[FFCBilinearPfaffians(M,N) : N in A] : M in A];
    bracket := function(i,j,k,l,m)
        return InnerProduct(B[i][j]*A[k],B[l][m]);
    end function;
    for i in [1..4] do
        for j in [i+1..4] do
            for k in [1..4] do
                if k eq i or k eq j then
                    continue;
                end if;
                l := [r : r in [1..4] | r ne i and r ne j and r ne k][1];
                /* [ii,l,jj]/4 = Pf(A_i) A_l Pf(A_j)^t over Z. */
                z := FFCSign([i,j,k,l])*InnerProduct(P[i]*A[l],P[j]);
                FFCPut(~C,5,i,j,k,z);
            end for;
        end for;
    end for;
    for i in [1..4] do
        for j in [1..4] do
            if i eq j then
                continue;
            end if;
            rem := [r : r in [1..4] | r ne i and r ne j];
            k,l := Explode(rem);
            FFCPut(~C,5,i,i,j,FFCSign([i,j,k,l])*bracket(l,i,i,i,k));
        end for;
    end for;
    anchors := [2,1,4,3];
    for i in [1..4] do
        k := anchors[i];
        FFCPut(~C,5,i,k,k,R!0);
        for j in [1..4] do
            if j eq i or j eq k then
                continue;
            end if;
            l := [r : r in [1..4] | r ne i and r ne j and r ne k][1];
            /* [jk,l,ii]/2 = Bpf(A_j,A_k) A_l Pf(A_i)^t. */
            z := FFCSign([i,j,k,l])*InnerProduct(B[j][k]*A[l],P[i]);
            FFCPut(~C,5,i,j,j,z);
        end for;
    end for;
    for i in [1..4] do
        rem := [r : r in [1..4] | r ne i];
        j,k,l := Explode(rem);
        z := FFCGet(C,5,i,j,j)+FFCGet(C,5,i,k,k)
        + FFCSign([i,j,k,l])*bracket(i,j,l,k,i);
        FFCPut(~C,5,i,i,i,z);
    end for;
    FFCConstantTerms(~C,5);
    return C;
end function;
