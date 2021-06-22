///////////////////////////////////////////////////////////////////////////
//  9.108.4.1
//    Analytic rank is 0
//    We enumerate J_tors(Q) as <D1,D2>, isomorphic to (Z/3Z)^2,
//    then check mod primes which are in the image of a point. 
///////////////////////////////////////////////////////////////////////////

  load "functions.m";
  label := "9.108.4.1";
  C := eval Read("../models/model" cat label cat ".txt");

  
  ///////////////////////////////////////////////////////////////////////////
  // Compute an upper bound on the torsion
  ///////////////////////////////////////////////////////////////////////////

  torsionData := {@@}; 
  for p in [5,7,11] do
      Xp := Curve(Reduction(C,p));
      invs := Invariants(ClassGroup(Xp));
      if Genus(Xp) eq 4 then torsionData := Include(torsionData, invs); end if;
  end for; 
  "Torsion is bounded above by ", torsBound(torsionData); // [ 3, 3 ]

  pts := RationalPoints(C); 
  pts := [pl :pl in Places(pt),  pt in pts | Degree(pl) eq 1];    
    

  ///////////////////////////////////////////////////////////////////////////
  // Find generators for J(Q)
  ///////////////////////////////////////////////////////////////////////////
  
  P1 := Divisor(pts[1]);
    P2 := Divisor(pts[2]); 
    P3 := Divisor(pts[3]);   
  D1 := P3 - P1;
    D2 := P3 - P2;  
  for a,b in [0..2] do 
      <[a,b], IsPrincipal(a*D1 + b*D2)>;
  end for;
  // they're independent 

  
  ///////////////////////////////////////////////////////////////////////////
  // Compute preimage of Abel--Jacobi map using P3 as the base point
  ///////////////////////////////////////////////////////////////////////////  

  "There are", #{<a,b> : a,b in [0..2] | Dimension(RiemannRochSpace(a*D1 + b*D2  + P3 )) gt 0}, "divisors in the image of the Abel--Jacobi map.";
  // Only 3 rational points
  // It has 3 rational cusps

ChangeDirectory("../rational-points-analysis/");
