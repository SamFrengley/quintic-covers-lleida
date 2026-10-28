// Preserve experimental choices through actions and specialization, on request.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/invariants.m": FFCAssignResolventRecipe;
import "envelope.m": FFCCorrectionCoerce;

procedure FFCMaterializeConjectural(C)
    if not assigned C`_Data`Resolvents`PendingConjectural then
        return;
    end if;
    task := C`_Data`Resolvents`PendingConjectural;
    source := task[2];
    E := ConjecturalSexticResolvent(source);
    if task[1] eq "BaseChange" then
        D,phi := BaseChange(E,task[3] : PreserveGrading := task[4]);
        FFCAssignResolventRecipe(C,D,D`_Data`Resolvents`DiscriminantFactor);
        C`_Data`Resolvents`Conjectural := D;
        delete C`_Data`Resolvents`PendingConjectural;
        return;
    end if;
    // Clear this recipe before re-entering the public constructor.
    delete C`_Data`Resolvents`PendingConjectural;
    F := ConjecturalSexticResolvent(C);
    R := BaseRing(C);
    if Characteristic(R) ne 2 and assigned E`_Data`Resolvents`BasisChange then
        Raw := BhargavaResolvent(C);
        if assigned Raw`_Data`Algebra`BasisChange then
            K := IsField(R) select R else FieldOfFractions(R);
            J := ChangeRing(F`_Data`Resolvents`BasisChange,K)
            *ChangeRing(Raw`_Data`Algebra`BasisChange,K)
            *ChangeRing(E`_Data`Resolvents`BasisChange,K)^-1;
            F`_Data`Algebra`BasisChange := Matrix(R,6,6,
                [FFCCorrectionCoerce(a,R) : a in Eltseq(J)]);
        end if;
    end if;
end procedure;
