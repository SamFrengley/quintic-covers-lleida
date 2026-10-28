// Split-bundle invariants, without computing equations or resolutions.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
// All numbers refer to the supplied cover, not its normalization.

function FFCAlgebraBundleWeights(C)
    if assigned C`_Data`Bundle`Algebra then
        return C`_Data`Bundle`Algebra;
    end if;
    if C`_Data`Presentation`Kind ne "Resolution" then
        error "This model has no recorded algebra-bundle grading";
    end if;
    n := Degree(C);
    w := C`_Data`Bundle`Variables;
    q := C`_Data`Bundle`Equations;
    // For a canonical degree-n resolution, rank(F_1)=n(n-3)/2 and
    // deg(F_1)=(n-3)deg(E). This recovers the common projective twist.
    if #q ne n*(n-3) div 2 or (&+q) mod (n-3) ne 0 then
        error "The equation degrees are inconsistent with an integral canonical bundle grading";
    end if;
    delta := (&+q) div (n-3)-(&+w);
    aw := [0] cat [delta-v : v in w];
    C`_Data`Bundle`Algebra := aw;
    return aw;
end function;

function FFCBothOrders(v)
    frame := v;
    sorted := v;
    Sort(~sorted);
    return <frame,sorted>;
end function;

intrinsic TschirnhausenInvariants(C::FinFlatCov : Sorted := true) -> SeqEnum
{The splitting degrees e_i of E=(pi_*O_C/O_S)^dual. Sorted increasingly by
 default; Sorted:=false follows the actual relative-canonical coordinate frame.
 Polynomial-derived projective models of degree 3--5 are already put in increasing
 FV order, so the two outputs then agree. No geometry or algebra is computed.}
    require C`ProjectiveBase: "Tschirnhausen invariants require ProjectiveBase := true";
    require Type(Sorted) eq BoolElt: "Sorted must be true or false";
    if not assigned C`_Data`Bundle`Tschirnhausen then
        aw := FFCAlgebraBundleWeights(C);
        C`_Data`Bundle`Tschirnhausen := FFCBothOrders(aw[2..#aw]);
    end if;
    data := C`_Data`Bundle`Tschirnhausen;
    return Sorted select data[2] else data[1];
end intrinsic;

intrinsic FirstSyzygyInvariants(C::FinFlatCov : Sorted := true) -> SeqEnum
{The splitting degrees f_i of the Casnati--Ekedahl bundle of quadratic generators.
 It is empty in degrees 2 and 3. In degree 4 it has rank 2, and in degree 5 rank 5.
 Sorted:=false follows the actual equation/Pfaffian frame. Polynomial-derived
 projective models through degree 5 are put into increasing FV order.}
    require C`ProjectiveBase: "First syzygy invariants require ProjectiveBase := true";
    require Type(Sorted) eq BoolElt: "Sorted must be true or false";
    if not assigned C`_Data`Bundle`FirstSyzygy then
        n := Degree(C);
        if n le 3 then
            C`_Data`Bundle`FirstSyzygy := <[],[]>;
        else
            require C`_Data`Presentation`Kind in {"Bhargava","Resolution"}:
                "First syzygy invariants need a canonical relative-canonical presentation";
            aw := FFCAlgebraBundleWeights(C);
            w := C`_Data`Bundle`Variables;
            q := C`_Data`Bundle`Equations;
            delta := aw[2]+w[1];
            f := [2*delta-v : v in q];
            C`_Data`Bundle`FirstSyzygy := FFCBothOrders(f);
        end if;
    end if;
    data := C`_Data`Bundle`FirstSyzygy;
    return Sorted select data[2] else data[1];
end intrinsic;
