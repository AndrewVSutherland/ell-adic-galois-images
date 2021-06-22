//////////////////////////////////////////////////////////////////////////////
//  27.108.6.1
//  X admits an involution iota
//    The quotient by iota is a genus 3 curve C
//    Analytic rank of JC is 3
//
//    Its Jacobian J factors as JC x A
//    A has analytic rank 0 
//    tau(P) := P - iota(P) is necessarily torsion.
//    We enumerate J_tors(Q) as <D1,D2>, isomorphic to (Z/3Z)^2,
//    Then check mod primes which are in the image of a point. 
//    (N.B. tau is injective away from fixed points)
//////////////////////////////////////////////////////////////////////////////

  load "functions.m";
  label := "27.108.6.1";
  X := eval Read("../models/model" cat label cat ".txt");

  ptsX := RationalPoints(X); // 5, some singular
  smPtsX := {@pl :pl in Places(pt),  pt in ptsX | Degree(pl) eq 1@}; // 4

    
  ///////////////////////////////////////////////////////////////////////////
  // X has an involution. We caluculate the fixed points.
  ///////////////////////////////////////////////////////////////////////////
    
  autX:= AutomorphismGroup(X);
    iota := autX.1;
  C := CurveQuotient(AutomorphismGroup(X, [autX.1]));
    "The quotient curve has genus", Genus(C); // 3
    "The involution has", #{@pt : pt in smPtsX | iota(pt) eq pt@}, "rational fixed points";
  // By Riemann--Hurwitz there are two fixed points


  ///////////////////////////////////////////////////////////////////////////
  // Compute an upper bound on the torsion
  ///////////////////////////////////////////////////////////////////////////

  torsionData := {@@}; 
  for p in [5,7] do
      Xp := Curve(Reduction(X,p));
      invs := Invariants(ClassGroup(Xp));
      if Genus(Xp) eq 6 then torsionData := Include(torsionData, invs); end if;
  end for; 
  "Torsion is bounded above by ", torsBound(torsionData); // [ 3, 3]

  
  ///////////////////////////////////////////////////////////////////////////
  // "Sieve"
  ///////////////////////////////////////////////////////////////////////////
  
  p := 2; // torsion is odd order so p = 2 is fine

  // This model has good reduction at 2 (or rather, does not have worse reduction at two)
  A2<x,y> := AffineSpace(Rationals(),2);
  f := (2*x+1)*(x^2+x-1)*y^3-3*(x^3+x^2+1)*x*y^2+(-3*x^4+9*x^3+18*x^2-9*x-6)*y-3*x^4+x^3+6*x^2-5*x-2 ;
  X2 := ProjectiveClosure(Curve(A2,f));    

  IsIsomorphic(X2,X); // true
  
  Xp<[T]> := Curve(Reduction(X2,p));
  "The reduction mod", p, "has genus", Genus(Xp), "and its smooth model has", #Places(Xp,1), "degree 1 points";
  // genus 6, 3 points
  
