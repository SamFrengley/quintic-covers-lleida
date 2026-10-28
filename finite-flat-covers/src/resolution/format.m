// resolution / format
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/arithmetic.m": FFCIsHomogeneousOfDegree;
import "../core/grading.m": FFCRelativeWeight;

function FFCBetti(n)
    if n lt 4 then
        error "The quadratic resolution format requires degree at least 4";
    end if;
    return [1] cat [n*Binomial(n-2,i)-Binomial(n,i+1) : i in [1..n-3]] cat [1];
end function;

procedure FFCCheckResolutionShape(F,n)
    b := FFCBetti(n);
    if #F ne n-2 then
        error "A full resolution needs n-2 matrices";
    end if;
    P := BaseRing(F[1]);
    if Type(P) ne RngMPol or Rank(P) ne n-1 then
        error "Resolution matrices must be over R[x_1,...,x_(n-1)]";
    end if;
    for a in [1..#F] do
        if BaseRing(F[a]) ne P or Nrows(F[a]) ne b[a] or Ncols(F[a]) ne b[a+1] then
            error Sprintf("Resolution map %o has the wrong parent or Betti dimensions",a);
        end if;
        e := a in {1,#F} select 2 else 1;
        if not forall{f : f in Eltseq(F[a]) | FFCIsHomogeneousOfDegree(f,e)} then
            error Sprintf("Resolution map %o must have fibre degree %o",a,e);
        end if;
    end for;
end procedure;

function FFCResolutionBaseWeights(F,w,projective,supplied)
    n := #F+2;
    b := FFCBetti(n);
    if not projective and #supplied eq 0 then
        return [[0 : i in [1..rank]] : rank in b];
    end if;
    if #supplied ne 0 then
        if #supplied ne #F+1 then
            error "ResolutionWeights lists F_0,...,F_(n-2)";
        end if;
        W := supplied;
    else
        W := [[0]];
        for a in [1..#F] do
            ww := [];
            for j in [1..Ncols(F[a])] do
                vals := [];
                for i in [1..Nrows(F[a])] do
                    if F[a][i,j] eq 0 then
                        continue;
                    end if;
                    if projective then
                        ok,e := FFCRelativeWeight(F[a][i,j],w);
                        if not ok then
                            error "Resolution is not bigraded; supply a homogeneous split resolution";
                        end if;
                    else
                        e := 0;
                    end if;
                    Append(~vals,e+W[a][i]);
                end for;
                if #vals eq 0 then
                    error "Cannot infer the degree of a zero resolution column; supply ResolutionWeights";
                end if;
                if #Seqset(vals) ne 1 then
                    error "Resolution column has incompatible bidegrees";
                end if;
                Append(~ww,vals[1]);
            end for;
            Append(~W,ww);
        end for;
    end if;
    if W[1] ne [0] then
        error "F_0 must have base weight zero";
    end if;
    for a in [1..#W] do
        if #W[a] ne b[a] then
            error "ResolutionWeights has an incorrect rank";
        end if;
        if not forall{z : z in W[a] | Type(z) eq RngIntElt} then
            error "Resolution weights must be integers";
        end if;
    end for;
    if not projective then
        if exists{z : z in &cat W | z ne 0} then
            error "Nonzero bundle weights require Proj";
        end if;
    else
        for a in [1..#F] do
            for i in [1..Nrows(F[a])] do
                for j in [1..Ncols(F[a])] do
                    f := F[a][i,j];
                    if f eq 0 then
                        continue;
                    end if;
                    ok,e := FFCRelativeWeight(f,w);
                    if not ok or e ne W[a+1][j]-W[a][i] then
                        error Sprintf("Wrong bidegree in resolution map %o at (%o,%o)",a,i,j);
                    end if;
                end for;
            end for;
        end for;
    end if;
    return W;
end function;
