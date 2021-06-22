///////////////////////////////////////////////////////////////////////////
// 9.108.3.1
//    J has rank 0
//    J_tors(Q) seems to be Z/9Z
// The two known rational points give a divisor of order 3.
// A nontrivial sieving argument works! (See the paper for details)
///////////////////////////////////////////////////////////////////////////

  load "functions.m";
  label := "9.108.3.1";
  C := eval Read("../models/model" cat label cat ".txt");

  // Some Points are singular, so work with places
  pts := RationalPoints(C); // slow; returns [0,1,0], [1,0,0]
  pts := [pl :pl in Places(pt),  pt in pts | Degree(pl) eq 1];    
  

  //////////////////////////////////////////////////////////////////////
  // Compute the local torsion bound
  //////////////////////////////////////////////////////////////////////    

  torsionData := {@@}; 
  for p in [5,13] do
      Xp := Curve(Reduction(C,p));
      invs := Invariants(ClassGroup(Xp));
      if Genus(Xp) eq 3 then torsionData := Include(torsionData, invs); end if;
  end for;                

  "The rational torsion subgroup is a subgroup of", torsBound(torsionData); // [ 9 ]

  
  //////////////////////////////////////////////////////////////////////
  // Compute low degree points
  //////////////////////////////////////////////////////////////////////      

  "The known rational points are ", pts; // returns two points
  
    pt1 := Divisor(pts[1]);
    pt2 := Divisor(pts[2]); 

  // The difference has order 3
  D := pt1-pt2; 
    order(D); // order 3
  

  // Search for quadratic points
  "Low height quadratic points", divisorSearch(C,2,5); // empty; searched up to bound := 30, which took 4144 seconds
   
  // There is no visible rational 9 torsion point.  

  
  ///////////////////////////////////////////////////////////////////////////
  // Verify that no point of order 9 is in the image of Abel--Jacobi
  ///////////////////////////////////////////////////////////////////////////
  
  // Verify mod 2 that there is no pair of points P,Q such that P-Q has order 9
    p := 2;
      Cp:= Curve(Reduction(C,2));
      Genus(Cp); // 3
    ptsCp := RationalPoints(Cp);
    ptsCp := [pl :pl in Places(pt),  pt in ptsCp | Degree(pl) eq 1];    
    exists{<p,q> : p,q in ptsCp |       order(Divisor(p) - Divisor(q)) eq 9}; // false  

    
  ///////////////////////////////////////////////////////////////////////////
  // Compute the preimage of J(Q) under the Abel--Jacobi map
  ///////////////////////////////////////////////////////////////////////////
    
  // We use pt2 as our base point for the Abel--Jacobi map
  // 0*D an 1*D are in the image of Abel--Jacobi, so we verify that 
  // 2*D is not in the image 
    Dimension(RiemannRochSpace(2*D  + pt2 )); // has dimension 0
              
ChangeDirectory("../rational-points-analysis/");
