// algebra / tables
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

function FFCIndex(d,i,j,k)
    return (i*d+j)*d+k+1;
end function;

procedure FFCPut(~C,d,i,j,k,v)
    C[FFCIndex(d,i,j,k)] := v;
    C[FFCIndex(d,j,i,k)] := v;
end procedure;

function FFCBlank(R,d)
    C := [R!0 : i in [1..d^3]];
    for i in [0..d-1] do
        FFCPut(~C,d,0,i,i,R!1);
    end for;
    return C;
end function;

function FFCGet(C,d,i,j,k)
    return C[FFCIndex(d,i,j,k)];
end function;

procedure FFCConstantTerms(~C,d)
    /* In (a_i a_j)a_k = a_i(a_j a_k), take k != i. */
    R := Universe(C);
    for i in [1..d-1] do
        for j in [i..d-1] do
            k := i eq 1 select 2 else 1;
            z := R!0;
            for r in [1..d-1] do
                z +:= FFCGet(C,d,j,k,r)*FFCGet(C,d,r,i,k)
                - FFCGet(C,d,i,j,r)*FFCGet(C,d,r,k,k);
            end for;
            FFCPut(~C,d,i,j,0,z);
        end for;
    end for;
end procedure;
