// geometry / charts
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../core/arithmetic.m": FFCIsUnit;
import "equations.m": FFCRawModelEquations;
import "../core/names.m": FFCCoordinateRing;

intrinsic LocalDefiningPolynomials(C::FinFlatCov, chart::RngIntElt :
    Simplify := true) -> SeqEnum,
    Map, Mtrx
{On the fibre chart x_chart=1 over a Spec base, remove only equations with a unit syzygy pivot.
 Returns Q, dehomogenization, and U with original equations = U*Q. Cached.}
    require not C`ProjectiveBase: "First use CoverPatch for a Proj base";
    require C`_Data`Presentation`Kind notin {"Algebra","BinaryAlgebra"} and Degree(C) ge 4:
        "Local syzygy simplification is for canonical quadric/Pfaffian models";
    Q := FFCRawModelEquations(C);
    P := Parent(Q[1]);
    r := Rank(P);
    require chart ge 1 and chart le r: "The fibre chart is out of range";
    if not assigned C`_Data`Geometry`LocalEquations then
        C`_Data`Geometry`LocalEquations := AssociativeArray();
    end if;
    key := Sprint(<chart,Simplify>);
    if IsDefined(C`_Data`Geometry`LocalEquations,key) then
        z := C`_Data`Geometry`LocalEquations[key];
        return z[1],z[2],z[3];
    end if;
    A := FFCCoordinateRing(BaseRing(C),r-1);
    images := [];
    j := 1;
    for i in [1..r] do
        if i eq chart then
            Append(~images,A!1);
        else
            Append(~images,A.j);
            j +:= 1;
        end if;
    end for;
    dehom := hom<P -> A | images>;
    q := [dehom(f) : f in Q];
    U := IdentityMatrix(A,#Q);
    if Simplify then
        syz := FirstSyzygies(C);
        S := Matrix(A,Nrows(syz),Ncols(syz),[dehom(f) : f in Eltseq(syz)]);
        while true do
            found := false;
            a := 0;
            b := 0;
            for i in [1..Nrows(S)] do
                for j in [1..Ncols(S)] do
                    if FFCIsUnit(S[i,j]) then
                        found := true;
                        a := i;
                        b := j;
                        break;
                    end if;
                end for;
                if found then
                    break;
                end if;
            end for;
            if not found then
                break;
            end if;
            keep := [i : i in [1..#q] | i ne a];
            cols := [j : j in [1..Ncols(S)] | j ne b];
            inv := A!(S[a,b]^-1);
            /* q_old = E q_new, and relations transform by E^t. */
            E := ZeroMatrix(A,#q,#keep);
            for k in [1..#keep] do
                E[keep[k],k] := 1;
                E[a,k] := -inv*S[keep[k],b];
            end for;
            U := U*E;
            SS := Transpose(E)*S;
            S := Matrix(A,#keep,#cols,[SS[i,j] : i in [1..#keep], j in cols]);
            q := [q[i] : i in keep];
        end while;
    end if;
    original := Matrix(A,#Q,1,[dehom(f) : f in Q]);
    assert original eq U*Matrix(A,#q,1,q);
    z := <q,dehom,U>;
    C`_Data`Geometry`LocalEquations[key] := z;
    return q,dehom,U;
end intrinsic;
