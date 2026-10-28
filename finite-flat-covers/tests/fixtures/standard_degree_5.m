// Integral degree-5 reference resolution: axes plus (1:...:1).
function StandardResolution5(R)
    P<[x]> := PolynomialRing(R,4);
    F := [* *];
    Append(~F,Matrix(P,1,5,[
        (1*x[1]*x[3] + -1*x[1]*x[2]),(1*x[1]*x[4] + -1*x[1]*x[2]),(1*x[2]*x[3] + -1*x[1]*x[2]),(1*x[2]*x[4] + -1*x[1]*x[2]),(1*x[3]*x[4] + -1*x[1]*x[2])
    ]));
    Append(~F,Matrix(P,5,5,[
        (-1*x[4] + 1*x[2]),(1*x[2]),(1*x[2]),(-1*x[4] + 1*x[2]),P!0,(1*x[3] + -1*x[2]),(-1*x[2]),(-1*x[2]),
        (-1*x[2]),(-1*x[2]),P!0,(-1*x[1]),(-1*x[4]),(-1*x[1]),(-1*x[4]),P!0,
        (1*x[1]),(1*x[3]),P!0,P!0,P!0,P!0,P!0,(1*x[1]),
        (1*x[2])
    ]));
    Append(~F,Matrix(P,5,1,[
        (1*x[2]*x[4] + -1*x[1]*x[2]),(1*x[3]*x[4] + -1*x[2]*x[3]),(-1*x[1]*x[4] + 1*x[1]*x[2]),(-1*x[2]*x[4] + 1*x[2]*x[3]),(1*x[1]*x[4] + -1*x[1]*x[3])
    ]));
    return F;
end function;
