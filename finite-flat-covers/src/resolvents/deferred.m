// On-demand action and specialization of already requested resolvents.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/basis.m": FFCApplyAlgebraTransport, FFCTransportAlgebra;
import "../algebra/invariants.m": FFCAssignResolventRecipe;
import "../core/arithmetic.m": FFCIntegralInverse;
import "../core/type.m": FFCNewCover;

procedure FFCApplyResolventTransport(C,D,g,h,s)
    R := BaseRing(C);
    n := Degree(C);
    if n eq 4 then
        if not assigned C`_Data`Resolvents`Standard then
            return;
        end if;
        E := C`_Data`Resolvents`Standard;
        F := Resolvent(D);
        L := s^3*Determinant(g)^2*Determinant(h)*h;
        FFCTransportAlgebra(E,F,L);
        // Its own quadratic resolvent remains uncomputed.
    elif n eq 5 then
        if assigned C`_Data`Resolvents`Standard then
            E := C`_Data`Resolvents`Standard;
            L := s^12*Determinant(g)^5*Determinant(h)^3*Transpose(FFCIntegralInverse(g));
            Temp := FFCNewCover();
            Temp`Degree := 6;
            Temp`CoefficientRing := R;
            FFCApplyAlgebraTransport(E,Temp,L);
            F := FiniteFlatCoverFromStructureConstants(Temp`StructureConstants,6 :
                ProjectiveBase := D`ProjectiveBase, Twisted := D`Twisted, AlgebraWeights := E`_Data`Bundle`Algebra,
                CheckAlgebra := false);
            F`_Data`Algebra`BasisChange := Temp`_Data`Algebra`BasisChange;
            if assigned Temp`_Data`Algebra`Traces then
                F`_Data`Algebra`Traces := Temp`_Data`Algebra`Traces;
            end if;
            if assigned Temp`_Data`Algebra`Pairing then
                F`_Data`Algebra`Pairing := Temp`_Data`Algebra`Pairing;
            end if;
            if assigned Temp`_Data`Algebra`Matrices then
                F`_Data`Algebra`Matrices := Temp`_Data`Algebra`Matrices;
            end if;
            if assigned Temp`_Data`Algebra`Associative then
                F`_Data`Algebra`Associative := Temp`_Data`Algebra`Associative;
            end if;
            F`_Data`Resolvents`SourceDegree := 5;
            F`_Data`Resolvents`Normalization := "Bhargava";
            FFCAssignResolventRecipe(D,F,R!4096);
            if assigned E`_Data`Algebra`TraceDiscriminant then
                F`_Data`Algebra`TraceDiscriminant := Determinant(L)^2*E`_Data`Algebra`TraceDiscriminant;
            end if;
            D`_Data`Resolvents`Standard := F;
        end if;
    end if;
end procedure;

procedure FFCMaterializeResolvent(C)
    if not assigned C`_Data`Resolvents`Pending then
        return;
    end if;
    task := C`_Data`Resolvents`Pending;
    source := task[2];
    E := Resolvent(source);
    delete C`_Data`Resolvents`Pending;
    if task[1] eq "Action" then
        FFCApplyResolventTransport(source,C,task[3],task[4],task[5]);
    else
        E,phi := BaseChange(E,task[3] : PreserveGrading := task[4]);
        if Degree(C) eq 5 then
            C`_Data`Resolvents`Standard := E;
            FFCAssignResolventRecipe(C,E,BaseRing(C)!4096);
        else
            C`_Data`Resolvents`Standard := E;
        end if;
    end if;
end procedure;

procedure FFCTransportResolvent(C,D,g,h,s)
    // Remember the map, not its (potentially expensive) image algebra.
    if assigned C`_Data`Resolvents`Standard
        or assigned C`_Data`Resolvents`Pending then
        D`_Data`Resolvents`Pending := <"Action",C,g,h,s>;
    end if;
    if assigned C`_Data`Resolvents`Conjectural or assigned C`_Data`Resolvents`PendingConjectural then
        D`_Data`Resolvents`PendingConjectural := <"Action",C,g,h,s>;
    end if;
end procedure;
