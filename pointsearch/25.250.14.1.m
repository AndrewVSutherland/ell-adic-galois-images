// Point searching on X_ns^+(25) = 25.250.14.1.

// Timing - bound = 10, 127 points, 0.310 seconds.
// bound = 20, 511 points, 1.790 seconds.
// bound = 40, 1959 points, 9.490 seconds.
// bound = 100, 12175 points, 85.010 seconds.

Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subdat := GL2Load("../groups/gl2_5adic.txt");
H1 := GL2Lift(subdat["5.10.0.1"]`subgroup,25);
H2 := subdat["25.250.14.1"]`subgroup;
C1 := ConjugacyClasses(H1);
C2 := ConjugacyClasses(H2);
pairsH1 := { <Trace(C1[i][3]),Determinant(C1[i][3])> : i in [1..#C1]};
pairsH2 := { <Trace(C2[i][3]),Determinant(C2[i][3])> : i in [1..#C2]};
printf "There are %o <tr,det> pairs mod 25 in 5.10.0.1.\n",#pairsH1;
printf "There are %o <tr,det> pairs mod 25 in 25.250.14.1.\n",#pairsH2;

F<x> := FunctionField(Rationals());
// jmap for 5.10.0.1
jmap := (320*x^7 + 80*x^6 - 36*x^5 - 25*x^4 - 32/5*x^3 - 9/10*x^2
- 7/100*x - 1/400)/(x^10 - 1/4*x^8 + 1/40*x^6 - 1/800*x^4 + 1/32000*x^2 - 
1/3200000);

bound := 100;
pts := { a/b : a in [-bound..bound], b in [-bound..bound] | (b ne 0) and (GCD(a,b) eq 1) };
printf "Testing %o points.\n",#pts;

t0 := Cputime();
for t in pts do
  j := Evaluate(jmap,t);
  E := MinimalTwist(EllipticCurveWithjInvariant(j));
  chk, D := HasComplexMultiplication(E);
  done := false;
  if chk then
    printf "t = %o gives rise to j = %o, which is CM with D = %o.\n",t,j,D;
    done := true;
  end if;
  p := 2;
  nextprint := 500;
  while (done eq false) do
    if GCD(p,5*Conductor(E)) eq 1 then
      pair := <Integers(25)!TraceOfFrobenius(E,p),Integers(25)!p>;
      if not (pair in pairsH2) then
        done := true;
      end if;
    end if;
    if (p gt nextprint) then
      printf "For t = %o, we needed to test up to %o.\n",t,nextprint;
      nextprint := nextprint*10;
    end if;
    if (done eq false) then
      p := NextPrime(p);
    end if;
  end while;
end for;
printf "Total time = %o.\n",Cputime(t0);
