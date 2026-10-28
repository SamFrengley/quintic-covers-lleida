// actions / operators
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").

intrinsic '^'(C::FinFlatCov,g::Mtrx) -> FinFlatCov
{Apply the stored left action. For tensor models (C^g)^h=C^(h*g).}
    return ActBy(C,g);
end intrinsic;

intrinsic '^'(C::FinFlatCov,T::Tup) -> FinFlatCov
{C^<g,h> is exactly ActBy(C,g,h); h can also be a list of resolution frames.}
    require #T eq 2: "Use a tuple <g,h>";
    return ActBy(C,T[1],T[2]);
end intrinsic;

intrinsic ActBy(~C::FinFlatCov,g::Mtrx : Twisted := "Stored")
{Replace the caller's variable by the transformed cover.}
    C := ActBy(C,g : Twisted := Twisted);
end intrinsic;

intrinsic ActBy(~C::FinFlatCov,g::Mtrx,h::Mtrx : Twisted := "Stored")
{Reference form of the two-matrix action.}
    C := ActBy(C,g,h : Twisted := Twisted);
end intrinsic;

intrinsic ActBy(~C::FinFlatCov,g::Mtrx,H::List : Twisted := "Stored")
{Reference form of the full-resolution action.}
    C := ActBy(C,g,H : Twisted := Twisted);
end intrinsic;

intrinsic ActBy(~C::FinFlatCov,g::Mtrx,H::SeqEnum : Twisted := "Stored")
{Reference form for a sequence of resolution frames.}
    C := ActBy(C,g,H : Twisted := Twisted);
end intrinsic;
