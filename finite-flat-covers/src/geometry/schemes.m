// Native Magma scheme backends; invoked only by geometric accessors.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCGet;
import "equations.m": FFCChosenEquations;

function FFCArithmeticScrollScheme(C,which)
    /* Exact integral elimination, no passage to Q. This is deliberately lazy.
       z_(i,j)=x_i*s^(a_i-j)*t^j, a_i=max(w)+1-w_i >=1.
       The two auxiliary equations impose both irrelevant-locus removals. */
    P,Q,Z,B := CoxData(C : Embedding := which);
    k := BaseRing(P);
    w := BundleWeights(C : Embedding := which);
    r := #w;
    a := [Max(w)+1-v : v in w];
    N := &+[v+1 : v in a];
    PP<[X]> := ProjectiveSpace(k,N-1);
    H := CoordinateRing(PP);
    blocks := [];
    cursor := 0;
    for v in a do
        Append(~blocks,[cursor+j+1 : j in [0..v]]);
        cursor +:= v+1;
    end for;
    top := [];
    bot := [];
    for i in [1..r] do
        top cat:= [H.(blocks[i][j+1]) : j in [0..a[i]-1]];
        bot cat:= [H.(blocks[i][j+2]) : j in [0..a[i]-1]];
    end for;
    scrollQ := [top[i]*bot[j]-top[j]*bot[i] : i,j in [1..#top] | i lt j];
    Scroll := Scheme(PP,scrollQ);
    /* Elimination order: original Cox variables, auxiliary variables, z. */
    old := r+2;
    aux := r+2;
    elim := old+aux;
    E := PolynomialRing(k,elim+N,"lex");
    gens := [Evaluate(q,[E.i : i in [1..old]]) : q in Q];
    Append(~gens,1-E.(old+1)*E.1-E.(old+2)*E.2);
    Append(~gens,1-&+[E.(old+2+i)*E.(2+i) : i in [1..r]]);
    cursor := 0;
    for i in [1..r] do
        for j in [0..a[i]] do
            cursor +:= 1;
            Append(~gens,E.(elim+cursor)-E.(i+2)*E.1^(a[i]-j)*E.2^j);
        end for;
    end for;
    G := GroebnerBasis(ideal<E|gens>);
    imageQ := [];
    for g in G do
        if forall{m : m in Monomials(g) | forall{i : i in [1..elim] | Exponents(m)[i] eq 0}} then
            vals := [H!0 : i in [1..elim]] cat [H.i : i in [1..N]];
            Append(~imageQ,Evaluate(g,vals));
        end if;
    end for;
    return Scheme(Scroll,imageQ),Scroll;
end function;

function FFCNativeAffineBaseScheme(C,which)
    Q,w := FFCChosenEquations(C,which);
    /* Reuse the named ring. Creating ProjectiveSpace(R,n-1) here used
       a NEW anonymous coordinate ring, discarding the X[i] names. */
    P := ProjectiveSpace(Parent(Q[1]));
    return Scheme(P,Q),P;
end function;

function FFCNativeRingScrollScheme(C,which)
    /* AbsoluteRationalScroll is documented for Rng, not only Fld.
       It uses nonpositive fibre weights. Subtracting Max(w) times the
       second grading row is an integral change of grading basis. */
    P,Q,Z,B := CoxData(C : Embedding := which);
    w := BundleWeights(C : Embedding := which);
    T := AbsoluteRationalScroll(BaseRing(P),[Max(w)-v : v in w]);
    AssignNames(~T,[Sprint(Name(P,i)) : i in [1..Rank(P)]]);
    H := CoordinateRing(T);
    vals := [H.i : i in [1..Rank(P)]];
    return Scheme(T,[Evaluate(q,vals) : q in Q]),T;
end function;

function FFCNativeToricScheme(C,which)
    P,Q,Z,B := CoxData(C : Embedding := which);
    T := ToricVariety(CoxRing(P,B,Z,[]));
    AssignNames(~T,[Sprint(Name(P,i)) : i in [1..Rank(P)]]);
    H := CoordinateRing(T);
    return Scheme(T,[H!q : q in Q]),T;
end function;

function FFCNativeScheme(C,which)
    if not C`ProjectiveBase then
        return FFCNativeAffineBaseScheme(C,which);
    end if;
    if IsField(BaseRing(BaseRing(C))) then
        return FFCNativeToricScheme(C,which);
    end if;
    return FFCNativeRingScrollScheme(C,which);
end function;

intrinsic UnderlyingScheme(C::FinFlatCov) -> Sch
{Native Magma scheme in a projective bundle; the Proj construction retains its ground ring.}
    if assigned C`UnderlyingScheme then
        return C`UnderlyingScheme;
    end if;
    if C`Embedding eq "Model" and assigned C`_Data`Geometry`ModelScheme then
        X := C`_Data`Geometry`ModelScheme;
        V := C`_Data`Geometry`ModelAmbient;
    else
        X,V := FFCNativeScheme(C,C`Embedding);
    end if;
    C`UnderlyingScheme := X;
    C`_Data`Geometry`Ambient := V;
    if C`Embedding eq "Model" then
        C`_Data`Geometry`ModelScheme := X;
        C`_Data`Geometry`ModelAmbient := V;
    end if;
    return X;
end intrinsic;

intrinsic AmbientBundle(C::FinFlatCov) -> Sch
{The projective bundle containing UnderlyingScheme(C).}
    X := UnderlyingScheme(C);
    return C`_Data`Geometry`Ambient;
end intrinsic;

intrinsic ProjectiveScrollEmbedding(C::FinFlatCov : Embedding := "Chosen") -> Sch, Sch
{Optional ordinary-projective embedding of a Proj cover and its scroll, by integral elimination.
 Can be expensive.}
    require C`ProjectiveBase: "Use this intrinsic only for a Proj base";
    which := Embedding eq "Chosen" select C`Embedding else Embedding;
    require which in {"Algebra","Model"}: "Unknown embedding";
    if not assigned C`_Data`Geometry`ScrollEmbedding then
        C`_Data`Geometry`ScrollEmbedding := AssociativeArray();
    end if;
    if not IsDefined(C`_Data`Geometry`ScrollEmbedding,which) then
        X,V := FFCArithmeticScrollScheme(C,which);
        C`_Data`Geometry`ScrollEmbedding[which] := <X,V>;
    end if;
    return Explode(C`_Data`Geometry`ScrollEmbedding[which]);
end intrinsic;

intrinsic ModelScheme(C::FinFlatCov) -> Sch
{The small model zero locus, not automatically the finite flat cover at degenerate models.}
    if assigned C`_Data`Geometry`ModelScheme then
        return C`_Data`Geometry`ModelScheme;
    end if;
    X,V := FFCNativeScheme(C,"Model");
    C`_Data`Geometry`ModelScheme := X;
    C`_Data`Geometry`ModelAmbient := V;
    return X;
end intrinsic;

intrinsic IsModelFiniteFlat(C::FinFlatCov) -> BoolElt
{Exact test for Spec(field); over other bases only an explicit user assumption is reported; it is
 NOT a certificate.}
    if C`_Data`Presentation`Flatness eq "Verified" then
        return true;
    end if;
    if not IsField(BaseRing(C)) and C`_Data`Presentation`Flatness eq "Assumed" then
        return true;
    end if;
    if C`_Data`Presentation`Flatness eq "Failed field test" then
        return false;
    end if;
    require not C`ProjectiveBase and IsField(BaseRing(C)):
        "No global projective-model flatness certification is implemented over this base; use the Algebra embedding";
    X := ModelScheme(C);
    ok := Dimension(X) eq 0;
    if ok then
        ok := Degree(X) eq Degree(C);
    end if;
    C`_Data`Presentation`Flatness := ok select "Verified" else "Failed field test";
    return ok;
end intrinsic;

intrinsic AffineAlgebraScheme(C::FinFlatCov) -> Sch
{Spec of the finite free algebra over an affine base (valid also for degenerate models).}
    require not C`ProjectiveBase: "Use CoverPatch first on a Proj base";
    if assigned C`_Data`Geometry`AffineScheme then
        return C`_Data`Geometry`AffineScheme;
    end if;
    d := Degree(C);
    R := BaseRing(C);
    if d eq 1 then
        A<[X]> := AffineSpace(R,1);
        C`_Data`Geometry`AffineScheme := Scheme(A,CoordinateRing(A).1);
        return C`_Data`Geometry`AffineScheme;
    end if;
    A<[X]> := AffineSpace(R,d-1);
    P := CoordinateRing(A);
    T := StructureConstants(C);
    Q := [];
    for i in [1..d-1] do
        for j in [i..d-1] do
            q := P.i*P.j-P!FFCGet(T,d,i,j,0);
            for k in [1..d-1] do
                q -:= FFCGet(T,d,i,j,k)*P.k;
            end for;
            Append(~Q,q);
        end for;
    end for;
    C`_Data`Geometry`AffineScheme := Scheme(A,Q);
    return C`_Data`Geometry`AffineScheme;
end intrinsic;
