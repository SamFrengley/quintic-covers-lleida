// Infer split gradings for weighted-homogeneous binary forms.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
// This inspects coefficient degrees only: no tables, Pfaffians, or syzygies.

function FFCBinaryCoefficientWeights(a)
    R := Universe(a);
    if Type(R) ne RngMPol or Rank(R) ne 2 then
        error "ProjectiveBase requires a standard graded two-variable base ring";
    end if;
    support := [];
    degrees := [];
    for i in [0..#a-1] do
        if a[i+1] eq 0 then
            continue;
        end if;
        if not IsHomogeneous(a[i+1]) then
            error Sprintf("The coefficient of X^%o Y^%o is not homogeneous in the base variables",
                i,#a-1-i);
        end if;
        Append(~support,i);
        Append(~degrees,Degree(a[i+1]));
    end for;
    // With at most one term the relative fibre weight is undetermined.
    // Use zero; explicit model weights can specify a different grading.
    if #support le 1 then
        c := #support eq 0 select 0 else degrees[1];
        return c,0;
    end if;
    gap := support[#support]-support[1];
    difference := degrees[1]-degrees[#degrees];
    if difference mod gap ne 0 then
        error "Coefficient degrees do not give an integral fibre weight; supply explicit model bundle weights";
    end if;
    r := difference div gap;
    c := degrees[1]+support[1]*r;
    for j in [1..#support] do
        if degrees[j] ne c-support[j]*r then
            error "Coefficient degrees are not affine-linear in the exponent; the polynomial is not weighted homogeneous";
        end if;
    end for;
    return c,r;
end function;

function FFCSortingPermutation(v)
    remaining := [1..#v];
    p := [];
    while #remaining gt 0 do
        m := Min([v[i] : i in remaining]);
        i := [j : j in remaining | v[j] eq m][1];
        Append(~p,i);
        remaining := [j : j in remaining | j ne i];
    end while;
    return p;
end function;

function FFCBinaryFVFrameData(a,d)
    c,r := FFCBinaryCoefficientWeights(a);

    // eRaw and fRaw follow the historical polynomial-to-tensor formulas.
    // The returned permutations put the actual model frames into the
    // Frengley--Vemulapalli convention: increasing e_i and f_i left to right.
    if d eq 2 then
        eRaw := [c-r];
        fRaw := [];
    elif d eq 3 then
        eRaw := [c-2*r,c-r];
        fRaw := [];
    elif d eq 4 then
        // Historical ternary coordinates: [XY,X^2,Y^2].
        eRaw := [c-2*r,c-3*r,c-r];
        // Historical quadric order: [rational-normal-curve relation, form relation].
        fRaw := [2*c-4*r,c-2*r];
    elif d eq 5 then
        // Historical matrix order from the binary-quintic tensor formula.
        eRaw := [c-i*r : i in [1..4]];
        fRaw := [2*c-4*r,2*c-5*r,2*c-6*r,c-2*r,c-3*r];
    else
        eRaw := [c-i*r : i in [1..d-1]];
        fRaw := [];
    end if;

    pe := FFCSortingPermutation(eRaw);
    pf := FFCSortingPermutation(fRaw);
    return c,r,eRaw,fRaw,pe,pf;
end function;

function FFCBinaryModelWeights(a,d)
    c,r,eRaw,fRaw,pe,pf := FFCBinaryFVFrameData(a,d);
    if d eq 2 then
        // A double cover is represented by a binary quadratic rather than P(E)=P^0.
        return [r,0],[],0,eRaw,fRaw,pe,pf;
    end if;
    if d le 5 then
        e := [eRaw[i] : i in pe];
        w := [-z : z in e];
        if d eq 5 then
            f := [fRaw[i] : i in pf];
            return w,f,-(&+e),eRaw,fRaw,pe,pf;
        end if;
        return w,[],0,eRaw,fRaw,pe,pf;
    end if;
    // Higher-degree canonical coordinates keep their existing monomial order.
    return [-z : z in eRaw],[],0,eRaw,fRaw,[1..#eRaw],[];
end function;
