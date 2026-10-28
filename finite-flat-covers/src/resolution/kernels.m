// resolution / kernels
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/names.m": FFCNamedPolynomialRing;
import "format.m": FFCBetti, FFCCheckResolutionShape;

function FFCLeftKernel(E)
    R := BaseRing(E);
    if IsField(R) then
        return NullspaceMatrix(E);
    end if;
    if Type(R) eq RngInt then
        /* SmithForm(A) returns S,U,V with U*A*V=S. */
        A := Transpose(E);
        S,U,V := SmithForm(A);
        r := Rank(S);
        assert U*A*V eq S;
        return Matrix(R,Nrows(E)-r,Nrows(E),
            [V[i,j] : j in [r+1..Nrows(E)], i in [1..Nrows(E)]]);
    end if;
    if Type(R) eq RngUPol then
        S := FFCNamedPolynomialRing(BaseRing(R),1,[Sprint(Name(R,1))]);
        cv := func<a | &+[S!Coefficient(a,i)*S.1^i : i in [0..Max(0,Degree(a))]]>;
        ES := Matrix(S,Nrows(E),Ncols(E),[cv(a) : a in Eltseq(E)]);
        F := EModule(S,Nrows(E));
        G := EModule(S,Ncols(E));
        K := Kernel(Homomorphism(F,G,ES));
        if not IsFree(K) then
            error "The coefficient kernel is not free; supply a split resolution";
        end if;
        B := MinimalBasis(K);
        back := func<a | Evaluate(a,[R.1])>;
        N := Matrix(R,#B,Nrows(E),[back(a) : a in &cat[Eltseq(b) : b in B]]);
    elif Type(R) eq RngMPol then
        F := EModule(R,Nrows(E));
        G := EModule(R,Ncols(E));
        K := Kernel(Homomorphism(F,G,E));
        if not IsFree(K) then
            error "The coefficient kernel is not free; supply a split resolution";
        end if;
        B := MinimalBasis(K);
        N := Matrix(R,#B,Nrows(E),&cat[Eltseq(b) : b in B]);
    else
        error "Automatic resolution: unsupported coefficient ring; supply all resolution maps";
    end if;
    assert IsZero(N*E);
    return N;
end function;

function FFCPureKernel(A,e)
    /* The degree-e part of the right kernel. No fraction-field substitution. */
    P := BaseRing(A);
    R := BaseRing(P);
    mons := MonomialsOfDegree(P,e);
    deg := Max([Degree(f) : f in Eltseq(A)]);
    outmons := MonomialsOfDegree(P,deg+e);
    E := ZeroMatrix(R,Ncols(A)*#mons,Nrows(A)*#outmons);
    for j in [1..Ncols(A)] do
        for b in [1..#mons] do
            for i in [1..Nrows(A)] do
                f := A[i,j]*mons[b];
                for c in [1..#outmons] do
                    E[(j-1)*#mons+b,(i-1)*#outmons+c] := MonomialCoefficient(f,outmons[c]);
                end for;
            end for;
        end for;
    end for;
    K := FFCLeftKernel(E);
    B := ZeroMatrix(P,Ncols(A),Nrows(K));
    for j in [1..Ncols(A)] do
        for a in [1..Nrows(K)] do
            B[j,a] := &+[(P!K[a,(j-1)*#mons+b])*mons[b] : b in [1..#mons]];
        end for;
    end for;
    assert IsZero(A*B);
    return B;
end function;

function FFCCompleteResolution(Q,n,prefix)
    P := Parent(Q[1]);
    b := FFCBetti(n);
    if #Q ne b[2] then
        error "Expected n(n-3)/2 minimal quadrics";
    end if;
    /* A list (not a homogeneous sequence): rectangular matrix spaces differ. */
    F := prefix;
    for a in [#F+1..n-2] do
        e := a eq n-2 select 2 else 1;
        B := FFCPureKernel(F[#F],e);
        if Ncols(B) ne b[a+1] then
            error Sprintf("Pure resolution step %o has %o generators, expected %o; supply an exact resolution or check the model",a,Ncols(B),b[a+1]);
        end if;
        Append(~F,B);
    end for;
    FFCCheckResolutionShape(F,n);
    return F;
end function;
