// Unit-preserving basis changes and deferred table transport.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "tables.m": FFCBlank, FFCGet, FFCPut;
import "../core/arithmetic.m": FFCIntegralInverse;

function FFCAnchors(n)
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

function FFCBasisTransform(T,B,n)
    /* Rows of B express the new basis in the old one. B fixes the unit. */
    R := BaseRing(B);
    Bi := FFCIntegralInverse(B);
    U := FFCBlank(R,n);
    for i in [1..n-1] do
        for j in [i..n-1] do
            v := [R!0 : k in [0..n-1]];
            for a,b in [0..n-1] do
                z := B[i+1,a+1]*B[j+1,b+1];
                if z eq 0 then
                    continue;
                end if;
                for k in [0..n-1] do
                    v[k+1] +:= z*FFCGet(T,n,a,b,k);
                end for;
            end for;
            v := Vector(R,v)*Bi;
            for k in [0..n-1] do
                FFCPut(~U,n,i,j,k,v[k+1]);
            end for;
        end for;
    end for;
    return U;
end function;

procedure FFCApplyAlgebraTransport(C,D,L)
    /* Carry a computed table to the new tensor's normalized basis, rather
       than re-running quartic/quintic/FR polynomial contractions. */
    if not assigned C`StructureConstants then
        return;
    end if;
    n := Degree(C);
    R := BaseRing(C);
    B := IdentityMatrix(R,n);
    for i,j in [1..n-1] do
        B[i+1,j+1] := L[i,j];
    end for;
    T := FFCBasisTransform(C`StructureConstants,B,n);
    anchors := FFCAnchors(n);
    if n eq 6 and assigned C`_Data`Resolvents`SourceDegree and C`_Data`Resolvents`SourceDegree eq 5 then
        anchors := [2,1,4,3,4];
        // Bhargava IV (37), not the generic FR anchors
    end if;
    H := IdentityMatrix(R,n);
    for i in [1..n-1] do
        H[i+1,1] := -FFCGet(T,n,i,anchors[i],anchors[i]);
    end for;
    T := FFCBasisTransform(T,H,n);
    B := H*B;
    D`StructureConstants := T;
    D`_Data`Algebra`BasisChange := B;
    if assigned C`_Data`Algebra`Associative then
        D`_Data`Algebra`Associative := C`_Data`Algebra`Associative;
    end if;
end procedure;

procedure FFCApplyQuadraticTransport(C,D,g,s)
    if not assigned C`StructureConstants then
        return;
    end if;
    R := BaseRing(C);
    P := Parent(C`Model);
    f := C`Model;
    a := MonomialCoefficient(f,P.1^2);
    b := MonomialCoefficient(f,P.1*P.2);
    c := MonomialCoefficient(f,P.2^2);
    /* With e^2+b e+ac=0, e' = beta+s det(g)e. No division by 2. */
    beta := -s*(a*g[1,1]*g[2,1]+b*g[1,2]*g[2,1]+c*g[1,2]*g[2,2]);
    B := Matrix(R,2,2,[1,0,beta,s*Determinant(g)]);
    D`StructureConstants := FFCBasisTransform(C`StructureConstants,B,2);
    D`_Data`Algebra`BasisChange := B;
    if assigned C`_Data`Algebra`Associative then
        D`_Data`Algebra`Associative := C`_Data`Algebra`Associative;
    end if;
end procedure;

function FFCMaterializeAlgebra(C)
    if not assigned C`_Data`Algebra`Pending then
        return false;
    end if;
    task := C`_Data`Algebra`Pending;
    source := task[2];
    T := StructureConstants(source);
    if task[1] eq "Basis" then
        FFCApplyAlgebraTransport(source,C,task[3]);
    elif task[1] eq "Quadratic" then
        FFCApplyQuadraticTransport(source,C,task[3],task[4]);
    elif task[1] eq "BaseChange" then
        phi := task[3];
        C`StructureConstants := [phi(a) : a in T];
    else
        error "Unknown deferred multiplication-table operation";
    end if;
    delete C`_Data`Algebra`Pending;
    return true;
end function;

procedure FFCTransportAlgebra(C,D,L)
    if assigned C`StructureConstants or assigned C`_Data`Algebra`Pending then
        D`_Data`Algebra`Pending := <"Basis",C,L>;
    end if;
end procedure;

procedure FFCTransportQuadratic(C,D,g,s)
    if assigned C`StructureConstants or assigned C`_Data`Algebra`Pending then
        D`_Data`Algebra`Pending := <"Quadratic",C,g,s>;
    end if;
end procedure;
