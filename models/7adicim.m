// The goal of this script is to determine the 3-adic image for
// an elliptic curve over Q.

p := 7;
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

finelabels := [ l : l in GL2QInfinite(subdat) | not GL2ContainsNegId(subdat[l]`subgroup) ];
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

// Give an elliptic curve E and a label, try to rule out the possibility
// that the mod N image of Galois is contained in that subgroup by finding
// a rho_E,N(Frob_q) that is not conjugate in GL(2,Z/NZ) to an element of
// the subgroup. It returns true if the group is ruled out, false otherwise.

function ruleout(E,sublab)
  grp := subdat[sublab]`subgroup;
  lev := subdat[sublab]`level;
  CC := ConjugacyClasses(grp);
  G := GL(2,Integers(lev));
  invars := [ GL2SimilarityInvariant(CC[i][3]) : i in [1..#CC]];
  done := false;
  q := 2;
  ret := true;
  complain := 10000;
  while done eq false do
    if IsPrime(q) and (GCD(q,p*(Integers()!Discriminant(E))) eq 1) then
      fr := G!FrobeniusMatrix(ChangeRing(E,GF(q)));
      // printf "At q = %o, matrix = %o.\n",q,fr;
      invar2 := GL2SimilarityInvariant(fr);
      if (not invar2 in invars) then
        done := true;
      end if;
    end if; 
    q := NextPrime(q);
    if (q gt complain) then
      printf "Having trouble ruling out %o. Tested primes up to %o.\n",sublab,q;
      complain := complain*10;
    end if;
  end while;
  return ret;
end function;

function liftto147(rets)
  R<y> := PolynomialRing(Rationals());
  good := true;
  for i in [1..#rets] do
    x := rets[i][1];
    pol := y^7 + (-21*x^6 + 84*x^5 + 378*x^4 - 7*x^3 - 455*x^2 + 7*x
+ 112)*y^5 + (70*x^9 + 315*x^8 - 343*x^7 - 1883*x^6 + 63*x^5 + 1771*x^4 + 28*x^3
- 119*x^2 - 77*x - 119)*y^4 + (1316*x^12 + 5740*x^11 - 1330*x^10 - 15190*x^9 + 
31143*x^8 + 51674*x^7 - 68159*x^6 - 89299*x^5 + 66759*x^4 + 47999*x^3 - 
22491*x^2 - 8442*x + 1897)*y^3 + (4200*x^15 + 18956*x^14 + 1876*x^13 - 
80262*x^12 - 66360*x^11 + 59654*x^10 - 43456*x^9 - 221907*x^8 + 237174*x^7 + 
505771*x^6 - 231084*x^5 - 405370*x^4 + 88949*x^3 + 133693*x^2 - 11690*x - 
15526)*y^2 + (5600*x^18 - 560*x^17 - 20468*x^16 + 195188*x^15 + 261275*x^14 - 
571998*x^13 + 539322*x^12 + 3314367*x^11 - 2143617*x^10 - 10108742*x^9 + 
1376186*x^8 + 13541437*x^7 + 536830*x^6 - 8564283*x^5 - 1085308*x^4 + 
2560740*x^3 + 492198*x^2 - 293293*x - 73290)*y + 8000*x^21 - 33600*x^20 - 
216440*x^19 + 660772*x^18 + 3749214*x^17 - 1548785*x^16 - 23986109*x^15 - 
13145711*x^14 + 58088625*x^13 + 45371207*x^12 - 78844619*x^11 - 59704673*x^10 + 
64627521*x^9 + 39436943*x^8 - 29221615*x^7 - 11839730*x^6 + 4824309*x^5 - 
134890*x^4 + 850675*x^3 + 1025654*x^2 - 295785*x - 194675;
    if #Roots(pol) ge 1 then
      good := false;
    end if;
  end for;
  return good;
end function;

function liftto196(rets)
  R<y> := PolynomialRing(Rationals());
  good := true;
  for i in [1..#rets] do
    x := rets[i][1];
    pol := y^7 + (-21*x^4 + 112*x^3 - 175*x^2 + 63*x + 28)*y^5 + 
(21*x^6 - 217*x^5 + 756*x^4 - 952*x^3 + 70*x^2 + 371*x + 70)*y^4 + (91*x^8 - 
791*x^7 + 2205*x^6 - 1323*x^5 - 2401*x^4 - 784*x^3 + 8673*x^2 - 4613*x - 
1673)*y^3 + (-112*x^10 + 1428*x^9 - 6510*x^8 + 10570*x^7 + 7007*x^6 - 36113*x^5 
+ 6664*x^4 + 63392*x^3 - 54628*x^2 + 1869*x + 4690)*y^2 + (-84*x^12 + 1099*x^11 
- 4858*x^10 + 6314*x^9 + 7175*x^8 + 7805*x^7 - 141757*x^6 + 233940*x^5 + 
14378*x^4 - 279846*x^3 + 132440*x^2 + 34370*x - 3612)*y + 97*x^14 - 1778*x^13 + 
12257*x^12 - 35497*x^11 + 6594*x^10 + 208992*x^9 - 427539*x^8 + 19010*x^7 + 
763553*x^6 - 544971*x^5 - 351008*x^4 + 365666*x^3 - 728*x^2 - 2660*x + 5536;
    if #Roots(pol) ge 1 then
      good := false;
    end if;
  end for;
  return good;
end function;

// The script starts working here.

function sevenadic(E)
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

  if curlab eq "7.21.0.1" then
    // We must check to see if a rational point lifts to 49.147.9.1
    chk := liftto147(rets);
    if chk eq false then
      printf "We get a rational point on 49.147.9.1!\n";
      bad := 0;
      bad2 := 1/bad;
    end if;
    chk := ruleout(E,"49.1029.69.1");
    if (chk eq false) then
      printf "We might get a rational point on X_ns^+(49).\n";
      bad := 0;
      bad2 := 1/bad;
    end if;
  end if;

  if curlab eq "7.28.0.1" then
    // We must check to see if a rational point lifts to 49.196.9.1
    chk := liftto196(rets);
    if chk eq false then
      printf "We get a rational point on 49.196.9.1!\n";
      bad := 0;
      bad2 := 1/bad;
    end if;
  end if;

  // Handle sporadic points on 7.56.1.2
  if jInvariant(E) eq (3^3*5*7^5/2^7) then
    curlab := "7.56.1.2";
    E1 := EllipticCurve([1,-1,1,-2680,-50053]);
    E2 := EllipticCurve([1,-1,1,-131305,17430697]);
    if IsIsomorphic(E,E1) or IsIsomorphic(E,E2) then
      curlab := "7.112.1.2";
    end if;  
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
      lab := sevenadic(E);
      if (lab ne "1.1.0.1") and (lab[1] ne "C") then
        printf "N=%o, i=%o, j=%o, %o - %o.\n",N,i,j,aInvariants(E),lab;
      end if;	
    end for;
  end for;
end for;

