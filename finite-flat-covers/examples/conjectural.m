AttachSpec("spec");
P<z> := PolynomialRing(Integers());
C := FiniteFlatCover(z^5-z-1);
B := Resolvent(C);
S := ConjecturalSexticResolvent(C);
assert not assigned C`Discriminant;
assert not assigned S`Discriminant;
Cp,phi := BaseChange(C,2);
Sp := ConjecturalSexticResolvent(Cp); // specialize the chosen order
print Rank(TracePairing(Sp));
print ConjecturalResolventCertificate(S);
quit;
