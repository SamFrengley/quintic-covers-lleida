// Evaluate integral sextic seed polynomials; numeric data is in src/data/.
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "../algebra/tables.m": FFCBlank, FFCConstantTerms, FFCGet, FFCPut;
import "../core/arithmetic.m": FFCSign;
import "../data/resolvent_indices.m": FFCResolventEdges, FFCResolventMinorIndices;
import "../data/seeds.m": FFCResolventSeedTerms;

function FFCResolventEdgeRank(i,j)
    // 1 <= i < j <= 5, in lexicographic order.
    return (i-1)*5-((i-1)*i) div 2+j-i;
end function;

function FFCResolventMinorRank(es)
    // Lexicographic rank of a sorted 4-subset of {1,...,10}.
    rank := 1;
    previous := 0;
    for k in [1..4] do
        for j in [previous+1..es[k]-1] do
            rank +:= Binomial(10-j,4-k);
        end for;
        previous := es[k];
    end for;
    return rank;
end function;

function FFCResolventMinorValues(C)
    if assigned C`_Data`Resolvents`Minors then
        return C`_Data`Resolvents`Minors;
    end if;
    A := C`Model;
    R := BaseRing(C);
    dd := [];
    for es in FFCResolventMinorIndices do
        M := Matrix(R,4,4,[A[r][FFCResolventEdges[es[j]][1],FFCResolventEdges[es[j]][2]] : j,r in [1..4]]);
        Append(~dd,Determinant(M));
    end for;
    C`_Data`Resolvents`Minors := dd;
    return dd;
end function;

procedure FFCResolventSeedValue(dd,which,prefix,~cache,~value)
    R := Universe(dd);
    p := prefix cat [i : i in [1..5] | i notin prefix];
    key := <p[1],p[2],p[3],p[4],p[5]>;
    if IsDefined(cache,key) then
        mapped := cache[key];
    else
        mapped := [R!0 : i in [1..210]];
        for a in [1..210] do
            es := [];
            sg := 1;
            for e in FFCResolventMinorIndices[a] do
                i := p[FFCResolventEdges[e][1]];
                j := p[FFCResolventEdges[e][2]];
                if i gt j then
                    tmp := i;
                    i := j;
                    j := tmp;
                    sg := -sg;
                end if;
                Append(~es,FFCResolventEdgeRank(i,j));
            end for;
            sg *:= FFCSign(es);
            Sort(~es);
            index := FFCResolventMinorRank(es);
            mapped[a] := sg*dd[index];
        end for;
        cache[key] := mapped;
    end if;
    value := R!0;
    for term in FFCResolventSeedTerms(which) do
        a,b,c := Explode([mapped[term[i]] : i in [2..4]]);
        if a ne 0 and b ne 0 and c ne 0 then
            value +:= term[1]*a*b*c;
        end if;
    end for;
    // Five epsilon tensors in (35) give one determinant sign.
    value *:= FFCSign(p);
end procedure;

function FFCSexticResolventConstants(C)
    R := BaseRing(C);
    dd := FFCResolventMinorValues(C);
    T := FFCBlank(R,6);
    cache := AssociativeArray();
    value := R!0;
    anchors := [2,1,4,3,4];
    for i in [1..5] do
        for j in [i+1..5] do
            for k in [1..5] do
                if k in {i,j} then
                    continue;
                end if;
                FFCResolventSeedValue(dd,1,[i,j,k],~cache,~value);
                FFCPut(~T,6,i,j,k,value);
            end for;
        end for;
        for j in [1..5] do
            if i eq j then
                continue;
            end if;
            FFCResolventSeedValue(dd,2,[i,j],~cache,~value);
            FFCPut(~T,6,i,i,j,value);
        end for;
        k := anchors[i];
        for j in [1..5] do
            if j in {i,k} then
                continue;
            end if;
            FFCResolventSeedValue(dd,3,[i,j,k],~cache,~value);
            FFCPut(~T,6,i,j,j,value);
        end for;
    end for;
    for i in [1..5] do
        remaining := [r : r in [1..5] | r ne i];
        j := remaining[1];
        k := remaining[2];
        FFCResolventSeedValue(dd,4,[i,j,k],~cache,~value);
        FFCPut(~T,6,i,i,i,FFCGet(T,6,i,j,j)+FFCGet(T,6,i,k,k)+value);
    end for;
    FFCConstantTerms(~T,6);
    return T;
end function;
