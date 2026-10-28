// Cheap presentation checks: count equations and fibre coordinates, not dimensions.
// These checks never compute multiplication tables, discriminants, or schemes.

function FFCEquationShape(C,which)
    if which notin {"Model","Algebra"} then
        error "Embedding must be Model or Algebra";
    end if;
    d := C`Degree;
    kind := C`_Data`Presentation`Kind;
    if which eq "Algebra" or kind in {"Algebra","BinaryAlgebra"} then
        if d eq 1 then
            return 2,1;
        end if;
        return d,d*(d-1) div 2;
    end if;
    if d le 3 then
        return 2,1;
    end if;
    return d-1,d*(d-3) div 2;
end function;

procedure FFCCheckEquationShape(C,Q,which,cox)
    n,m := FFCEquationShape(C,which);
    base := cox select 2 else 0;
    if #Q ne m then
        error Sprintf("%o embedding in degree %o requires %o equations, not %o. " cat
            "Reconstruct the cover with the desired Embedding; do not edit cached attributes.",
            which,C`Degree,m,#Q);
    end if;
    P := Parent(Q[1]);
    if Rank(P) ne n+base then
        error Sprintf("%o embedding in degree %o requires %o fibre coordinates " cat
            "and %o base coordinates; the equation ring has %o generators.",
            which,C`Degree,n,base,Rank(P));
    end if;
end procedure;
