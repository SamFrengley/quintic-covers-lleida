// Trace data and explicitly requested discriminants.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "tables.m": FFCGet;
import "../core/arithmetic.m": FFCDescendElement;

procedure FFCAssignResolventRecipe(C,D,factor)
    // Store an unevaluated recipe. Only Discriminant(D) may evaluate it.
    D`_Data`Resolvents`DiscriminantFactor := factor;
    D`_Data`Algebra`DiscriminantRecipe := <C,3,factor>;
    if assigned C`Discriminant then
        D`Discriminant := factor*C`Discriminant^3;
    end if;
end procedure;

procedure FFCTransportDiscriminantRecipe(C,D,chi)
    if assigned C`_Data`Algebra`DiscriminantRecipe then
        Q,e,a := Explode(C`_Data`Algebra`DiscriminantRecipe);
        D`_Data`Algebra`DiscriminantRecipe := <Q,e,chi*a>;
    end if;
    if assigned C`_Data`Resolvents`DiscriminantFactor then
        D`_Data`Resolvents`DiscriminantFactor := chi*C`_Data`Resolvents`DiscriminantFactor;
    end if;
end procedure;

intrinsic TraceVector(C::FinFlatCov) -> SeqEnum
{Cached traces of 1,e_1,...,e_(n-1), computed directly from the multiplication table.}
    if assigned C`_Data`Algebra`Traces then
        return C`_Data`Algebra`Traces;
    end if;
    T := StructureConstants(C);
    n := Degree(C);
    v := [&+[FFCGet(T,n,i,j,j) : j in [0..n-1]] : i in [0..n-1]];
    C`_Data`Algebra`Traces := v;
    return v;
end intrinsic;

intrinsic TracePairing(C::FinFlatCov) -> Mtrx
{The trace pairing in the integral basis 1,e_1,...,e_(d-1).}
    if assigned C`_Data`Algebra`Pairing then
        return C`_Data`Algebra`Pairing;
    end if;
    A := StructureConstants(C);
    v := TraceVector(C);
    d := Degree(C);
    /* Tr(e_i e_j)=sum_k c_ij^k Tr(e_k): O(d^3), not d^2 matrix products. */
    T := Matrix(BaseRing(C),d,d,[&+[FFCGet(A,d,i,j,k)*v[k+1] : k in [0..d-1]] : i,j in [0..d-1]]);
    C`_Data`Algebra`Pairing := T;
    return T;
end intrinsic;

intrinsic TraceDiscriminant(C::FinFlatCov) -> RngElt
{Cached determinant of the trace pairing, independently of the resolvent discriminant route.}
    if not assigned C`_Data`Algebra`TraceDiscriminant then
        C`_Data`Algebra`TraceDiscriminant := Determinant(TracePairing(C));
    end if;
    return C`_Data`Algebra`TraceDiscriminant;
end intrinsic;

intrinsic Discriminant(C::FinFlatCov) -> RngElt
{The discriminant section; cubic/quartic models use their cached resolvent. Quintics do not force
 a sextic computation.}
    if not assigned C`Discriminant then
        n := Degree(C);
        if assigned C`_Data`Algebra`TraceDiscriminant then
            C`Discriminant := C`_Data`Algebra`TraceDiscriminant;
        elif assigned C`_Data`Algebra`DiscriminantRecipe then
            Q,e,a := Explode(C`_Data`Algebra`DiscriminantRecipe);
            C`Discriminant := FFCDescendElement(a*Discriminant(Q)^e,BaseRing(C),
                "discriminant obtained from the transported recipe");
        elif n eq 3 or (n eq 4 and C`_Data`Presentation`Kind eq "Bhargava") then
            C`Discriminant := Discriminant(Resolvent(C));
        else
            C`Discriminant := TraceDiscriminant(C);
        end if;
    end if;
    return C`Discriminant;
end intrinsic;
