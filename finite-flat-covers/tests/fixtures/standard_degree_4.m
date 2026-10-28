// Integral degree-4 reference resolution: axes plus (1:...:1).
function StandardResolution4(R)
    P<[x]> := PolynomialRing(R,3);
    F := [* *];
    Append(~F,Matrix(P,1,2,[
        (1*x[1]*x[3] + -1*x[1]*x[2]),(1*x[2]*x[3] + -1*x[1]*x[2])
    ]));
    Append(~F,Matrix(P,2,1,[
        (-1*x[2]*x[3] + 1*x[1]*x[2]),(1*x[1]*x[3] + -1*x[1]*x[2])
    ]));
    return F;
end function;
