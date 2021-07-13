// The goal of this script is to determine the 3-adic image for
// an elliptic curve over Q.

p := 3;
Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subdat := GL2Load("../groups/gl2_" cat IntegerToString(p) cat "adic.txt");

subfilename := "subdata" cat IntegerToString(p) cat ".txt";
subdata := eval Read(subfilename);

coverlist := [];
// We exclude modular curves for which (i) the canonical model was computed
// (ii) the model was unnecessary because of prior work, or (iii)
// we didn't try to compute a model (namely X_ns^+(49)).
excludedlist := ["27.243.12.1", "27.729.43.1", "25.150.8.1", "125.150.8.1", "25.250.14.1", "25.375.22.1", "25.625.36.1", "49.168.12.1", "49.168.12.2", "49.1029.69.1", "49.1372.94.1"];
for i in [1..#subdata] do
  if subdat[subdata[i][1]]`qtwists[1] eq subdata[i][1] then
    if not (subdata[i][1] in excludedlist) then
      Append(~coverlist,<subdata[i][1],subdata[i][3]>);
    end if;
  end if;
end for;

// Make a master list of modular curves

modcurves := <>;
for lab in ["1.1.0.1"] cat [ coverlist[i][1] : i in [1..#coverlist]] do
  filename := Sprintf("model%o.txt",lab);
  Append(~modcurves,<lab,eval Read(filename)>);
end for;

F<t> := FunctionField(Rationals());
masterlist := [];
for i in [1..#subdata] do
  if (subdat[subdata[i][1]]`genus eq 0) and (subdat[subdata[i][1]]`qtwists[1] eq subdata[i][1]) then
    curlab := subdata[i][1];
    // Compute map to the j-line for label curlab
    firsttime := true;
    curmap := 0;
    while (curlab ne "1.1.0.1") do
      ind := Index([ coverlist[i][1] : i in [1..#coverlist]],curlab);
      coverlab := coverlist[ind][2];
      modcurveind1 := Index([ modcurves[i][1] : i in [1..#modcurves]],curlab);
      modcurveind2 := Index([ modcurves[i][1] : i in [1..#modcurves]],coverlab);  

      mapfilename := curlab cat "map" cat coverlab cat ".txt";
      // Specify DD is the domain of the map, and CC is the codomain
      DD := modcurves[modcurveind1][2];
      CC := modcurves[modcurveind2][2];
  
      mp := eval Read(mapfilename);
      if (firsttime) then
        curmap := mp;
        firsttime := false;
      else
        curmap := curmap*mp;
      end if;
      curlab := coverlab;
    end while;
    Append(~masterlist,<subdata[i][1],curmap([t,1])[1]/curmap([t,1])[2]>);
  end if;
end for;
function jmap(lab)
  ind := Index([ masterlist[i][1] : i in [1..#masterlist]],lab);
  return masterlist[ind][2];
end function;

// Load all the fine models from files.

finelabels := [ l : l in GL2QInfinite(subdat) | not GL2ContainsNegativeOne(subdat[l]`subgroup) ];
finelist := [];
for i in [1..#finelabels] do
  Append(~finelist,eval Read("eqf" cat finelabels[i] cat ".txt"));
end for;

// Given a rational function f and an element j in Q, determine
// if (j : 1) is in the image of the morphism induced by f from P^1 -> P^1.

P1 := ProjectiveSpace(Rationals(),1);

function doeslift(f,j)
  rets := [P1|];
  num := Numerator(f);
  denom := Denominator(f);
  poly := num - j*denom;
  rts := Roots(poly);
  if #rts ge 1 then
    for r in rts do
      Append(~rets,P1![r[1],1]);
    end for;
  end if;
  if Degree(num) eq Degree(denom) then
    if LeadingCoefficient(num)/LeadingCoefficient(denom) eq j then
      Append(~rets,P1![1,0]);
    end if;
  end if;
  return rets;
end function;

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
    printf "The given point on X_ns^+(9) lifts to a point on X_H!!!!\n";
    printf "This might yield a rational point on X_ns^+(27)!!!\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
  return ret;
end function;

// The script starts working here.

function threeadic(E)
  jval := jInvariant(E);
  done := false;
  curlab := "1.1.0.1";
  currets := [];

  chk := HasComplexMultiplication(E);
  if chk then
    chk, D := HasComplexMultiplication(E);
    done := true;
    curlab := "CM " cat IntegerToString(D);
    return curlab;
  end if;

  while (done eq false) do
    done := true;
    testlist := [ s : s in subdat[curlab]`children | (subdat[s]`genus eq 0) and (s eq subdat[s]`qtwists[1]) and GL2ContainsComplexConjugation(subdat[s]`subgroup)];
    //printf "Current label %o.\n",curlab;
    //printf "Testing %o.\n",testlist;
    if #testlist ge 1 then
      for tt in testlist do
        j := jmap(tt);
        rets := doeslift(j,jval);
        if #rets ge 1 then
          done := false;
	  curlab := tt;
	  currets := rets;
	  //printf "j-invariant lifts to %o.\n",tt;
	  break;
        end if;
      end for;
    end if;
  end while;

  if curlab eq "9.27.0.2" then
    for r in currets do
      ret2 := XH3lift(r);
      // Complain loudly and break if this point might lift to X_ns^+(27).
    end for;
  end if;

  // Check for subgroups that don't contain the identity.
  if (chk eq false) and (curlab ne "1.1.0.1") then
    testlist := [ s : s in subdat[curlab]`children | (not s eq subdat[s]`qtwists[1])];
    for tt in testlist do
      ind := Index(finelabels,tt);
      X := finelist[ind];
      ainvars := aInvariants(X);
      A := ainvars[4];
      B := ainvars[5];
      for y in currets do
        if (curlab ne tt) then
          if y[2] eq 1 then
            spec := EllipticCurve([0,0,0,Evaluate(A,y[1]),Evaluate(B,y[1])]);
  	    if IsIsomorphic(E,spec) then
	      curlab := tt;
	      //printf "We found a curve in the family of %o that's isomorphic to E.\n",tt;
	    end if;
	  end if;
        else
          // Specialize the elliptic surface at t = infinity.
	  // Only a potential issue for 9.36.0.5 and 9.36.0.8
	  // Test for j = -132651/2.
	  if Degree(Numerator(j)) eq Degree(Denominator(j)) then
            degA := Degree(Numerator(A));
	    degB := Degree(Numerator(B));
	    powt := Max(Ceiling(degA/4),Ceiling(degB/6));
	    A2 := Evaluate(A,1/t)*t^(4*powt);
	    B2 := Evaluate(B,1/t)*t^(6*powt);
	    Aspec := Evaluate(A2,0);
	    Bspec := Evaluate(B2,0);
	    //printf "Aspec = %o, Bspec = %o.\n",Aspec,Bspec;
            spec := EllipticCurve([0,0,0,Aspec,Bspec]);
	    if IsIsomorphic(E,spec) then
	      curlab := tt;
	      //printf "We found a curve in the family of %o that's isomorphic to E.\n",tt;
	    end if;
	  end if;
        end if;
      end for;
    end for;
  end if;
  return curlab;
end function;

DB := CremonaDatabase();
for N in [11..499999] do
  iso := NumberOfIsogenyClasses(DB,N);
  for i in [1..iso] do
    k := NumberOfCurves(DB,N,i);
    for j in [1..k] do
      E := EllipticCurve(DB,N,i,j);
      lab := threeadic(E);
      if (lab ne "1.1.0.1") and (lab[1] ne "C") then
        printf "N=%o, i=%o, j=%o, %o - %o.\n",N,i,j,aInvariants(E),lab;
      end if;	
    end for;
  end for;
end for;

