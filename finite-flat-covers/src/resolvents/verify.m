// resolvents / verify
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCGet;

intrinsic VerifyResolvent(C::FinFlatCov : CheckDiscriminant := false, Conjectural := false) -> BoolElt
{Check associativity and the inclusion certificate. Trace determinants are evaluated ONLY when
 CheckDiscriminant := true is explicitly passed.}
    D := Conjectural select ConjecturalSexticResolvent(C) else Resolvent(C);
    if not assigned D`_Data`Resolvents`Verified then
        ok := IsAssociative(C) and IsAssociative(D);
        if Degree(C) eq 5 and assigned D`_Data`Resolvents`Inclusion then
            B := BhargavaResolvent(C);
            inc := D`_Data`Resolvents`Inclusion;
            T := StructureConstants(D);
            U := StructureConstants(B);
            R := BaseRing(C);
            for i,j,k in [0..5] do
                lhs := &+[inc[i+1,a+1]*inc[j+1,b+1]*FFCGet(T,6,a,b,k) : a,b in [0..5]];
                rhs := &+[FFCGet(U,6,i,j,a)*inc[a+1,k+1] : a in [0..5]];
                ok := ok and lhs eq rhs;
            end for;
        end if;
        D`_Data`Resolvents`Verified := ok;
    end if;
    if not D`_Data`Resolvents`Verified then
        return false;
    end if;
    if CheckDiscriminant then
        if not assigned D`_Data`Resolvents`DiscriminantVerified then
            lhs := TraceDiscriminant(D);
            src := TraceDiscriminant(C);
            rhs := Degree(C) eq 5 select D`_Data`Resolvents`DiscriminantFactor*src^3 else src;
            ok := lhs eq rhs;
            if assigned C`Discriminant then
                ok := ok and C`Discriminant eq src;
            end if;
            if assigned D`Discriminant then
                ok := ok and D`Discriminant eq lhs;
            end if;
            D`_Data`Resolvents`DiscriminantVerified := ok;
        end if;
        return D`_Data`Resolvents`DiscriminantVerified;
    end if;
    return true;
end intrinsic;
