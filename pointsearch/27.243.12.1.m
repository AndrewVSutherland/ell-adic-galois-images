// Point searching on X_ns^+(27) = 27.243.12.1.
// After testing, the most efficient way to see if points lift is to
// see if they lift to X_H3.

// Timing - bound = 10, 120 points, 0.520 seconds.
// bound = 20, 504 points, 2.590 seconds.
// bound = 40, 1952 points, 10.620 seconds.
// bound = 80, 7856 points, 43.570 seconds.
// bound = 100, 12168 points, 67.380 seconds.

Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subdat := GL2Load("../groups/gl2_3adic.txt");
H1 := GL2Lift(subdat["9.27.0.2"]`subgroup,27);
H2 := subdat["27.243.12.1"]`subgroup;
C1 := ConjugacyClasses(H1);
C2 := ConjugacyClasses(H2);
pairsH1 := { <Trace(C1[i][3]),Determinant(C1[i][3])> : i in [1..#C1]};
pairsH2 := { <Trace(C2[i][3]),Determinant(C2[i][3])> : i in [1..#C2]};

F<x> := FunctionField(Rationals());
jmap := (-15*x^9 - 81*x^8 - 27*x^7 + 117*x^6 - 81*x^5 + 189*x^4 -
288*x^3 + 216*x - 96)^3/(x^9 - 9*x^7 + 3*x^6 + 27*x^5 - 18*x^4 - 24*x^3 + 27*x^2 - 9*x + 1)^3; 

// The GCD of the homogenized numerator and denominator in jmap is a divisor of 3^29.

// x = infinity is j = -3375 which is CM.
// x = 0 is j = -884736 which is CM.
// x = -1 is j = 1728 which is CM.
// x = 1 is j = 287496 which is CM.
// x = 1/2 is j = 16581375 which is CM.
// x = 1/3 is j = -262537412640768000 which is CM.
// x = -2 is j = -147197952000 which is CM.
// x = 2 is j = -884736000 which is CM.

bound := 100;
pts := { a/b : a in [-bound..bound], b in [-bound..bound] | (b ne 0) and (GCD(a,b) eq 1) };
Exclude(~pts,0);
Exclude(~pts,-1);
Exclude(~pts,1);
Exclude(~pts,1/2);
Exclude(~pts,1/3);
Exclude(~pts,-2);
Exclude(~pts,2);
printf "Testing %o points.\n",#pts;

// Lift point to X_H3.

// The modular curve XH3 is intermediate between X_ns^+(9)
// and X_ns^+(27). We don't provably know all the rational points on
// X_ns^+(27), but if our elliptic curve E lifted to a point on X_ns^+(27)
// then there would have to be a Q(zeta_3) point above j(E) on this intermediate
// modular curve. We use this to rule that out.

// The input is a point on X_ns^+(9)

function XH3lift(pt)
  K<zeta> := CyclotomicField(3);
  R<a,b,c> := PolynomialRing(K,3);
  f := a^4 + (zeta - 1)*a^3*b + (3*zeta + 2)*a^3*c - 3*a^2*c^2 +
    (2*zeta + 2)*a*b^3 - 3*zeta*a*b^2*c + 3*zeta*a*b*c^2 - 2*zeta*a*c^3 -
    zeta*b^3*c + 3*zeta*b^2*c^2 + (-zeta + 1)*b*c^3 + (zeta + 1)*c^4;
  P1 := ProjectiveSpace(K,1);
  C := Curve(ProjectiveSpace(K,2),f);
  xns := map<C -> P1 | [[(zeta-1)*C.1+(-2*zeta-1)*C.2+(zeta-1)*C.3,(-zeta-2)*C.1+(-zeta-2)*C.2+(-zeta+1)*C.3],[1/3*(-zeta + 1)*C.1^3 + 1/3*(4*zeta - 1)*C.1^2*C.2 + 1/3*(-4*zeta + 1)*C.1*C.2^2
    + (zeta + 1)*C.2^3 + 1/3*(2*zeta + 4)*C.1^2*C.3 + zeta*C.1*C.2*C.3 + 
    1/3*(-8*zeta - 4)*C.2^2*C.3 + 1/3*(zeta - 1)*C.1*C.3^2 + 1/3*(5*zeta + 
    1)*C.2*C.3^2 + 1/3*(-2*zeta - 1)*C.3^3,C.2^3 + (zeta - 1)*C.2^2*C.3 + (-2*zeta - 1)*C.2*C.3^2]]>;
  pp := P1!Eltseq(pt);
  X := pp@@xns;
  ret := false;
  rp := RationalPoints(X);
  if #rp ge 1 then
    printf "The given point %o on X_ns^+(9) lifts to a point on X_H!!!!\n",pt;
    printf "This might yield a rational point on X_ns^+(27)!!!\n";
  end if;
  return ret;
end function;

t0 := Cputime();
for t in pts do
  test := XH3lift([t,1]);
end for;
printf "Total time = %o.\n",Cputime(t0);
