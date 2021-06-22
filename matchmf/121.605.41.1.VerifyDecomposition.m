Attach("../groups/gl2.m");
H := sub<GL(2,Integers(11^2))|[[38,50,41,61],[68,68,45,68]]>; // conjugate of 121.605.41.1 containing [-1,0,0,1]
assert GL2Level(H) eq 121 and GL2Index(H) eq 605 and GL2Genus(H) eq 41 and GL2DeterminantIndex(H) eq 1; // uniquely determines H
B := 2*Index(Gamma1(11^4))/6/EulerPhi(121);  // We multiply by 2 because Index compues index in PSL(2,Z), divide by phi(121) because we restrict conductor
B := Integers()!Floor(B);
chi := DirichletGroup(11)!1;
E := EllipticCurve("121b1");
P := PrimesInInterval(1,B);
a := TracesOfFrobenius(E,B);
R<T> := PolynomialRing(Integers());
print "Generating modular form data for 121.2.a.b using the elliptic curve 121b1...";
L121ab := [1-a[i]*T+Integers()!chi(P[i])*P[i]*T^2:i in [1..#P]];
print "Loading modular form data from cmf_14641.2.a.a.txt...";
S14641aa := eval(Split(Read("cmf_14641.2.a.a.txt"),":")[8]);
L14641aa := [R!([1] cat r cat [r[#r-j]*P[i]^j:j in [1..#r-1]] cat (#r gt 0 select [P[i]^#r] else [])) where r:=S14641aa[i] : i in [1..#P]];
print "Loading modular form data from cmf_14641.2.a.c.txt...";
S14641ac := eval(Split(Read("cmf_14641.2.a.c.txt"),":")[8]);
L14641ac := [R!([1] cat r cat [r[#r-j]*P[i]^j:j in [1..#r-1]] cat (#r gt 0 select [P[i]^#r] else [])) where r:=S14641ac[i] : i in [1..#P]];
L := [L121ab[i]*L14641aa[i]*L14641ac[i]:i in [1..#P]];
assert P[5] eq 11 and L[5] eq 1; // Euler factor at 1, as verified by 121.605.41.1.CheckLPolynomialAt11.m
L := Remove(L,5);  P := Remove(P,5);
printf "Computing #X_H(F_q) for H = 121.605.41.1 and primes powers q <= B = %o. This will take 15-30 minutes...", B;
time A := GL2Traces(H,B:PrimePowers);
for i:=1 to #P do
    assert LPolynomialToTraces(L[i]:d:=#A[i]) eq A[i];
end for;
print "Success!";
