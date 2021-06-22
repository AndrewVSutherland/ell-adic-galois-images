///////////////////////////////////////////////////////////////////////////
//  27.36.3.1
//    Its Jacobian J factors as E x A
//    E is  -6^2*(-x^3 - 2*y*x^2 + 3*y^2*x) + z^3 = 0, and has rank 1
//    A has rank 0 (X is a Picard curve, and we can do descent on J directly
//    or compute the analytic rank)
//    The map X --> E is the quotient by an involution iota; 
//    tau(P) := P - iota(P) is necessarily torsion.
//    We enumerate J_tors(Q) as <D1,D2>, isomorphic to (Z/3Z)^2,
//    Then check mod primes which are in the image of a point. 
//    (N.B. tau is injective away from fixed points)
// 
//  X has 2 rational cusps, and 1 with j = 0. 
///////////////////////////////////////////////////////////////////////////

  load "functions.m";
  label := "27.36.3.1";
  C := eval Read("../models/model" cat label cat ".txt");

  pts := RationalPoints(C : Bound := 10000); // {@ (-3 : 144342 : 1), (0 : 1 : 0), (0 : -314928 : 1), (1 : 0 : 0) @}
  pts := [pl :pl in Places(pt),  pt in pts | Degree(pl) eq 1];    

   
  ///////////////////////////////////////////////////////////////////////////
  // Analysis of rational points
  ///////////////////////////////////////////////////////////////////////////
  
  psi := CanonicalMap(C);
    Xsm := CanonicalImage(Domain(psi),psi); // very fast
    P2<x,y,z> := AmbientSpace(Xsm);
  fXsm := MinimizeReducePlaneQuartic(DefiningEquation(Xsm));
    fXsm := -Evaluate(fXsm, [-x,-y,z]);
    X := Curve(P2,fXsm);

    
  ///////////////////////////////////////////////////////////////////////////
  // Compute Torsion
  ///////////////////////////////////////////////////////////////////////////

  torsionData := {@@}; 
  for p in [5,7,13] do
      Xp := Curve(Reduction(X,p));
      invs := Invariants(ClassGroup(Xp));
      if Genus(Xp) eq 3 then torsionData := Include(torsionData, invs); end if;
  end for; 
  "Torsion is bounded above by ", torsBound(torsionData); // [ 3, 3 ]

  
  ///////////////////////////////////////////////////////////////////////////
  // find a basis for the torsion
  ///////////////////////////////////////////////////////////////////////////   

  pts := {@ X![0,1,0], X![0,0,1], X![1,0,0] @};
     
  D1 := Divisor(pts[1]) - Divisor(pts[3]); // order 3
   IsPrincipal(3*D1);
    
  D2 := Divisor(pts[2]) - Divisor(pts[3]); // order 3
   IsPrincipal(3*D2);
    
  [<[a,b], IsLinearlyEquivalent(a*D1,b*D2)> : a,b in [0..2]];
  // Conclusion: J_tors(Q) is <D1,D2>

  
  ///////////////////////////////////////////////////////////////////////////
  // Now sieve
  ///////////////////////////////////////////////////////////////////////////  

  p := 2; // torsion is odd order so p = 2 is fine
  C := Curve(Reduction(X,p)); 
    iotaC := map<C -> C | [C.3,C.2,C.1]>;
  pts := {@ C![0,1,0], C![0,0,1], C![1,0,0] @};
    D1 := Divisor(C!pts[1]) - Divisor(C!pts[3]); 
    D2 := Divisor(C!pts[2]) - Divisor(C!pts[3]); 
  [<pt, a,b> : pt in pts, a,b in [0..2] | IsLinearlyEquivalent(a*D1 + b*D2, Divisor(pt) - Divisor(iotaC(pt)) )];    
  // [ <(0 : 0 : 1), 0, 0>, <(0 : 1 : 0), 1, 0>, <(1 : 0 : 0), 2, 0> ]


    ///////////////////////////////////////////////////////////////////////////
    // Calculate fixed points  
    ///////////////////////////////////////////////////////////////////////////  

    fixed := Scheme(P2,[fXsm, y*x-y*z, x^2 - z^2]); 
    Degree(fixed); // 4, consistent with Riemann Roch
    [Degree(irr) : irr in IrreducibleComponents(fixed)]; // 3, 1, so no additional rational fixed points.
              
ChangeDirectory("../rational-points-analysis/");
