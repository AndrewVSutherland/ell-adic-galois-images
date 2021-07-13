// Point searching on X_ns^+(49)

// Timing - bound = 10, 0.59 seconds
// bound = 100, 270.47 seconds

Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subdat := GL2Load("../groups/gl2_7adic.txt");

bound := 100;

H1 := GL2Lift(subdat["7.21.0.1"]`subgroup,49);
H2 := subdat["49.1029.69.1"]`subgroup;
C1 := ConjugacyClasses(H1);
C2 := ConjugacyClasses(H2);
pairsH1 := { <Trace(C1[i][3]),Determinant(C1[i][3])> : i in [1..#C1]};
pairsH2 := { <Trace(C2[i][3]),Determinant(C2[i][3])> : i in [1..#C2]};
printf "There are %o <tr,det> pairs mod 49 in 7.21.0.1.\n",#pairsH1;
printf "There are %o <tr,det> pairs mod 49 in 49.1029.69.1.\n",#pairsH2;

F<x> := FunctionField(Rationals());
// jmap for 7.21.0.1
jmap := (8000*x^21 + 33600*x^20 + 55440*x^19 + 87472*x^18 + 204204*x^17 +
236796*x^16 + 38395*x^15 + 80589*x^14 + 179109*x^13 - 524125*x^12 - 691152*x^11 
+ 430248*x^10 + 93464*x^9 - 784224*x^8 + 785856*x^7 + 1142848*x^6 - 956928*x^5 -
720384*x^4 + 598528*x^3 + 129024*x^2 - 172032*x + 32768)/(x^21 + 14*x^20 + 
77*x^19 + 189*x^18 + 77*x^17 - 616*x^16 - 1106*x^15 + 289*x^14 + 2338*x^13 + 
1099*x^12 - 2247*x^11 - 2037*x^10 + 1008*x^9 + 1596*x^8 - 57*x^7 - 658*x^6 - 
140*x^5 + 133*x^4 + 56*x^3 - 7*x^2 - 7*x - 1);

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
    if GCD(p,7*Conductor(E)) eq 1 then
      pair := <Integers(49)!TraceOfFrobenius(E,p),Integers(49)!p>;
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
