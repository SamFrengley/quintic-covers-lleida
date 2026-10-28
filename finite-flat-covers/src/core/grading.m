// Validate split-bundle degrees directly on coefficients.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "arithmetic.m": FFCActionField, FFCIsHomogeneousOfDegree;

function FFCRationalDegree(x,R)
    if x eq 0 then
        return false,0;
    end if;
    ok,y := IsCoercible(R,x);
    if ok then
        if not IsHomogeneous(y) then
            return false,0;
        end if;
        return true,Degree(y);
    end if;
    // Projective bases are standard graded polynomial rings k[s,t].
    a := Numerator(x);
    b := Denominator(x);
    oka,aa := IsCoercible(R,a);
    okb,bb := IsCoercible(R,b);
    if not (oka and okb) or aa eq 0 or bb eq 0 then
        return false,0;
    end if;
    if not IsHomogeneous(aa) or not IsHomogeneous(bb) then
        return false,0;
    end if;
    return true,Degree(aa)-Degree(bb);
end function;

function FFCRationalHomogeneousDegree(x,R,e)
    if x eq 0 then
        return true;
    end if;
    ok,d := FFCRationalDegree(x,R);
    return ok and d eq e;
end function;

function FFCPrepareActionMatrixWithWeights(G,R,w,projective,dual)
    n := #w;
    if Nrows(G) ne n or Ncols(G) ne n then
        error "Action matrix has the wrong size";
    end if;
    K := FFCActionField(R);
    entries := [];
    for a in Eltseq(G) do
        ok,b := IsCoercible(K,a);
        if not ok then
            error "Action-matrix entries must lie in the coefficient ring or its fraction field";
        end if;
        Append(~entries,b);
    end for;
    H := Matrix(K,n,n,entries);
    if Determinant(H) eq 0 then
        error "Action matrix is singular over the fraction field";
    end if;
    if not projective then
        return H,w;
    end if;

    // H is allowed to change the splitting type.  If `dual' is true, row i
    // expresses the old coordinate/frame entries in the new i-th coordinate:
    //     deg(H[i,j]) + w_new[i] = w_old[j].
    // Otherwise row i is a direct frame combination:
    //     deg(H[i,j]) + w_old[j] = w_new[i].
    // Every nonzero entry in a row must therefore give the same target weight.
    target := [];
    for i in [1..n] do
        candidates := [];
        for j in [1..n] do
            if H[i,j] eq 0 then
                continue;
            end if;
            ok,d := FFCRationalDegree(H[i,j],R);
            if not ok then
                error Sprintf("Entry (%o,%o) is not a homogeneous rational function",i,j);
            end if;
            Append(~candidates,dual select w[j]-d else w[j]+d);
        end for;
        if #candidates eq 0 then
            error Sprintf("Row %o of the action matrix is zero",i);
        end if;
        if #Seqset(candidates) ne 1 then
            error Sprintf("Row %o does not define a homogeneous target bundle summand",i);
        end if;
        Append(~target,candidates[1]);
    end for;
    return H,target;
end function;

function FFCPrepareActionMatrix(G,R,w,projective,dual)
    H,target := FFCPrepareActionMatrixWithWeights(G,R,w,projective,dual);
    return H;
end function;

function FFCRelativeWeight(q,w)
    if q eq 0 then
        return true,0;
    end if;
    cc,mm := CoefficientsAndMonomials(q);
    degrees := [];
    for i in [1..#cc] do
        if not IsHomogeneous(cc[i]) then
            return false,0;
        end if;
        a := Exponents(mm[i]);
        Append(~degrees,Degree(cc[i])+&+[a[j]*w[j] : j in [1..#w]]);
    end for;
    return #Seqset(degrees) eq 1,degrees[1];
end function;

function FFCWeights(M,d,R,projective,w,qw,rw,tw)
    n := d le 3 select 2 else d-1;
    count := d le 3 select 1 else (d eq 4 select 2 else 5);
    if #w eq 0 then
        w := [0 : i in [1..n]];
    end if;
    if #w ne n then
        error "Incorrect number of VariableWeights";
    end if;
    if d eq 5 and #rw eq 0 then
        rw := [0,0,0,0,0];
    end if;
    if d eq 5 and #rw ne 5 then
        error "RowWeights must have length 5";
    end if;
    if #qw ne 0 and #qw ne count then
        error "Incorrect number of EquationWeights";
    end if;
    if exists{a : a in w cat qw cat rw | Type(a) ne RngIntElt}
        or Type(tw) ne RngIntElt then
        error "Bundle weights and MatrixTwist must be integers";
    end if;
    if not projective then
        if exists{v : v in w cat rw cat qw | v ne 0} or tw ne 0 then
            error "Nonzero bundle degrees require a projective base";
        end if;
        return w,[0 : i in [1..count]],rw,tw,[0 : i in [1..d]];
    end if;
    if Type(R) ne RngMPol or Rank(R) ne 2 then
        error "A projective base requires a standard graded ring k[s,t]";
    end if;
    if d eq 1 then
        return [0,0],[0],[],0,[0];
    end if;
    if d eq 5 then
        for k in [1..4] do
            for i in [1..5] do
                for j in [i+1..5] do
                    degree := tw+rw[i]+rw[j]-w[k];
                    if not FFCIsHomogeneousOfDegree(M[k][i,j],degree) then
                        error Sprintf("A[%o][%o,%o] must be homogeneous of base degree %o",k,i,j,degree);
                    end if;
                end for;
            end for;
        end for;
        expected := [2*tw+&+rw-rw[i] : i in [1..5]];
        if #qw ne 0 and qw ne expected then
            error "EquationWeights disagree with the Pfaffian row weights";
        end if;
        delta := 5*tw+2*(&+rw)-(&+w);
        return w,expected,rw,tw,[0] cat [delta-v : v in w];
    end if;
    // Each term is <coefficient, coordinate weight>; no polynomial expansion.
    if d le 3 then
        P := Parent(M);
        terms := [[<MonomialCoefficient(M,P.1^i*P.2^(d-i)),
            i*w[1]+(d-i)*w[2]> : i in [0..d]]];
    else
        terms := [&cat[[<A[i,j],w[i]+w[j]> : j in [i..3]]
            : i in [1..3]] : A in M];
    end if;
    inferred := [];
    for a in [1..#terms] do
        degrees := [];
        for term in terms[a] do
            c,v := Explode(term);
            if c eq 0 then
                continue;
            end if;
            if not IsHomogeneous(c) then
                error "A model coefficient is not homogeneous";
            end if;
            Append(~degrees,Degree(c)+v);
        end for;
        e := #qw gt 0 select qw[a] else (#degrees gt 0 select degrees[1] else 0);
        if exists{v : v in degrees | v ne e} then
            error "The model is not bihomogeneous for these bundle weights";
        end if;
        Append(~inferred,e);
    end for;
    delta := (&+inferred)-(&+w);
    aw := d eq 2 select [0,delta] else [0] cat [delta-v : v in w];
    return w,inferred,rw,tw,aw;
end function;
