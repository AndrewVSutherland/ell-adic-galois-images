// This Magma script is being used to compute the resolvent polynomials
// that the Dokchitser's wrote down for use in determining the
// image of elliptic curve Galois representations. Now, I'm using it to
// figure out which twist of a given elliptic curve has p-adic image inside
// particular subgroup not containing -I.

// This script takes as input an integer m (on the command line)
// and computes the universal elliptic curve E_G, where G runs over
// all subgroups in finesublist[m]

// Revised on 10/6/20 and 10/7/20.
// Revised again on 2/4/2021 and 2/8/2021
// Potential issue fixed on 2/15/2021
// Revised on 4/22/21
// Revised again on 5/13/21

Attach("../groups/gl2.m");
load "../groups/gl2data.m";

if (not assigned m) then
  printf "This script requires a label m be passed as a command line argument.\n";
  printf "The usage is something like magma m:=3.8.0.1 whichtwist2.txt";
  quit;
end if;

lev := StringToInteger(Split(m,".")[1]);
chk, p := IsPrimePower(lev);
subdat := GL2Load("../groups/gl2_" cat IntegerToString(p) cat "adic.txt");

if (not m in Keys(subdat)) then
  printf "Error. Label not found.\n";
  bad := 0;
  bad2 := 1/bad;
end if;

subfilename := "subdata" cat IntegerToString(p) cat ".txt";
subdata := eval Read(subfilename);
coverlist := [ <subdata[i][1],subdata[i][3]> : i in [1..#subdata]];

logfilename := "fmodel" cat m cat ".out";
System("rm " cat logfilename);
SetLogFile(logfilename);
printf "Working on subgroup %o.\n",m;
coverlab := subdat[m]`qtwists[1];
printf "Covering group is %o.\n",coverlab;

F<t> := FunctionField(Rationals());
curlab := coverlab;
curfunc := t;
while (curlab ne "1.1.0.1") do
  ind := Index([ coverlist[i][1] : i in [1..#coverlist]],curlab);
  coverlab := coverlist[ind][2];

  DD := eval Read("model" cat curlab cat ".txt");
  CC := eval Read("model" cat coverlab cat ".txt");
  mapfilename := curlab cat "map" cat coverlab cat ".txt";
  mp := eval Read(mapfilename);
  newfunc := mp([curfunc,1])[1];
  curlab := coverlab;
  curfunc := newfunc;
end while;
j := curfunc;

printf "j-invariant map for %o is %o.\n",m,j;
E := EllipticCurve([0,0,0,-27*j*(j-1728),-54*j*(j-1728)^2]);
// Pick a minimal twist.
A := aInvariants(E)[4];
B := aInvariants(E)[5];
denomA := Denominator(A);
denomB := Denominator(B);
FF := Factorization(LCM(denomA,denomB));
multfac := F!1;
for n in [1..#FF] do
  expo := Max(Ceiling(Valuation(denomA,FF[n][1])/2),
  Ceiling(Valuation(denomB,FF[n][1])/3));
  multfac := multfac*FF[n][1]^expo;
end for;
printf "Multfac = %o.\n",multfac;

A := A*multfac^2;
B := B*multfac^3;
cofdenomA := LCM([ Denominator(Coefficient(Numerator(A),i)) : i in [0..Degree(Numerator(A))]]);
cofdenomB := LCM([ Denominator(Coefficient(Numerator(B),i)) : i in [0..Degree(Numerator(B))]]);
FF := Factorization(LCM(cofdenomA,cofdenomB));
multfac := 1;
for n in [1..#FF] do
  pp := FF[n][1];
  expo := Max(Ceiling(Valuation(cofdenomA,pp)/2),
  Ceiling(Valuation(cofdenomB,pp)/3));
  multfac := multfac*pp^expo;
end for;
A := A*multfac^2;
B := B*multfac^3;
FF := Factorization(GCD([PolynomialRing(Integers())!Numerator(A),PolynomialRing(Integers())!Numerator(B)]));
divfac := 1;
Afac := Factorization(PolynomialRing(Integers())!Numerator(A));
Bfac := Factorization(PolynomialRing(Integers())!Numerator(B));
for n in [1..#FF] do
  pp := FF[n][1];
  aind := Index([ Afac[n][1] : n in [1..#Afac]],pp);
  bind := Index([ Bfac[n][1] : n in [1..#Bfac]],pp);
  if aind ne 0 then
    aval := Afac[aind][2];
  else
    aval := 0;
  end if;
  if bind ne 0 then
    bval := Bfac[bind][2];
  else
    bval := 0;
  end if;
  expo := Min(Floor(aval/2),Floor(bval/3));
  divfac := divfac*pp^expo;
end for;
printf "Divfac = %o.\n",divfac;
A := A/((F!divfac)^2);
B := B/((F!divfac)^3);
// Ensure the model is integral.
denomAlist := [ Denominator(Coefficient(Numerator(A),i)) : i in [0..Degree(Numerator(A))]];
denomBlist := [ Denominator(Coefficient(Numerator(B),i)) : i in [0..Degree(Numerator(B))]];
FF := Factorization(LCM(LCM(denomAlist),LCM(denomBlist)));
multfac := F!1;
for n in [1..#FF] do
  expo1 := Max([ Ceiling(Valuation(denomAlist[i],FF[n][1])/2) : i in [1..#denomAlist]]);
  expo2 := Max([ Ceiling(Valuation(denomBlist[i],FF[n][1])/3) : i in [1..#denomBlist]]);
  multfac := multfac*FF[n][1]^Max(expo1,expo2);
end for;  
A := A*multfac^2;
B := B*multfac^3;
Et := EllipticCurve([0,0,0,A,B]);
printf "New model is %o.\n",Et;
D := Numerator(Discriminant(Et));
printf "The discriminant is %o.\n",D;
AAA<zz> := PolynomialRing(Rationals());
D := AAA!D;
FFF := Factorization(D);
squarefreedivs := [ AAA!1 ];
for n in [1..#FFF] do
  adds := [ squarefreedivs[i]*FFF[n][1] : i in [1..#squarefreedivs]];
  squarefreedivs := squarefreedivs cat adds;
end for;
options := [ [] : i in [1..#squarefreedivs]];
printf "There are %o squarefree divisors of the discriminant.\n",#squarefreedivs;
for n in [1..#squarefreedivs] do
  printf "Option %o is %o.\n",n,squarefreedivs[n];
end for;

Gfinegenlist := [ Transpose(g) : g in Generators(subdat[m]`subgroup) ];
Ggenlist := Gfinegenlist cat [GL(2,Integers(subdat[m]`level))![-1,0,0,-1]];
Gfine := sub<GL(2,Integers(subdat[m]`level)) | Gfinegenlist>;
G := sub<GL(2,Integers(subdat[m]`level)) | Ggenlist>;
mm := subdat[m]`level;
conjset := Conjugates(GL(2,Integers(mm)),G);
seq := SetToSequence(conjset);

printf "The order of G is %o.\n",#G;
printf "The level is %o.\n",m;
CC := ConjugacyClasses(G);
printf "There are %o conjugacy classes of G.\n",#CC;
printf "Their sizes are %o.\n",[ CC[i][2] : i in [1..#CC]];

// Use the elliptic function x+y
// Use h(x) = x^3

// Go over all points of order mm
eltorderm := [ [i,j] : i in [1..mm], j in [1..mm] | GCD([i,j,mm]) eq 1 ];

T<x> := PolynomialRing(Integers());

// Only use integral values for t, so we have integral models.
bigdone := false;
curt := 0;
passone := true;
while (bigdone eq false) do
// Increment curt
  goodt := false;
  while (goodt eq false) do
    curt := curt + 1;
    Anew := Evaluate(A,curt);
    Bnew := Evaluate(B,curt);
    if 4*Anew^3 + 27*Bnew^2 ne 0 then
      jval := (6912*Anew^3)/(4*Anew^3 + 27*Bnew^2);
      if not HasComplexMultiplication(EllipticCurveWithjInvariant(jval)) then
        goodt := true;
      end if;
    end if;
  end while;
  printf "Using t = %o.\n",curt;
  E := EllipticCurve([0,0,0,Anew,Bnew]);
  printf "Working on curve %o.\n",aInvariants(E);

  if (mm eq 3) then
    decprec := 1000;
    decprec2 := 1000;
   h := x^3;
  end if;
  if (mm eq 9) then
    decprec := 3000;
    decprec2 := 1000;
    h := x^3;
  end if;
  if (mm eq 27) then
    decprec := 6000;
    decprec2 := 1500;
    h := x^3;
  end if;
  if (mm eq 5) then
    decprec := 1000;
    decprec2 := 1000;
    h := x^3;
  end if;
  if (mm eq 25) then
    decprec := 8000;
    decprec2 := 1500;
    h := x^3;
  end if;
  if (mm eq 7) then
    decprec := 1500;
    decprec2 := 1500;
    h := x^3;
  end if;  

  polylist := [];
  C<I> := ComplexField(decprec);
  CCC<I2> := ComplexField(decprec2);
  R<z> := PolynomialRing(C);
  Rsmall := RealField(50);
  RSTUV<zsmall> := PolynomialRing(Rsmall);
  periodlist := Periods(E : Precision := decprec);

  printf "Enumerating points of order %o.\n",mm;
  hvals1 := [];
  ellvals1 := [];
  hvals2 := [];
  ellvals2 := [];
  count := 0;
  for pt in eltorderm do
    count := count + 1;
    if (count mod 20 eq 0) then
      //printf "Done %o of %o.\n",count,#eltorderm;
    end if;
    ellpt := EllipticExponential(E,(periodlist[1]*pt[1])/mm+(periodlist[2]*pt[2])/mm);
    ellval := p*ellpt[1] + p^2*ellpt[2];
    // ellval is an algebraic integer according to Theorem VII.3.4 from Silverman
    Append(~hvals1,Evaluate(h,ellval));
    Append(~ellvals1,ellval);
    Append(~hvals2,CCC!Evaluate(h,ellval));
    Append(~ellvals2,CCC!ellval);
  end for;

  // Figure out which conjugate we should pick.

  printf "Selecting which conjugate of G we should use.\n";
  choices := [];
  errs := [];
  for choice in [1..#seq] do
    printf "Testing choice %o. ",choice;
    candidate := seq[choice];
    num := C!0;
    pt1 := [1,mm];
    pt2 := [mm,1];
    pt3 := [1,1];
    for g in candidate do
      a := pt1[1];
      b := pt1[2];
      impt := [ g[1][1]*a + g[2][1]*b, g[1][2]*a + g[2][2]*b ];
      impt := [ Integers()!impt[1], Integers()!impt[2]];
      if impt[1] eq 0 then
        impt[1] := mm;
      end if;
      if impt[2] eq 0 then
       impt[2] := mm;
      end  if;
      ind1 := Index(eltorderm,pt1);
      ind2 := Index(eltorderm,impt);
      term1 := hvals2[ind2];
      a := pt2[1];
      b := pt2[2];
      impt := [ g[1][1]*a + g[2][1]*b, g[1][2]*a + g[2][2]*b ];
      impt := [ Integers()!impt[1], Integers()!impt[2]];
      if impt[1] eq 0 then
        impt[1] := mm;
      end if;
      if impt[2] eq 0 then
        impt[2] := mm;
      end if;
      ind1 := Index(eltorderm,pt2);
      ind2 := Index(eltorderm,impt);
      term2 := hvals2[ind2];
      a := pt3[1];
      b := pt3[2];
      impt := [ g[1][1]*a + g[2][1]*b, g[1][2]*a + g[2][2]*b ];
      impt := [ Integers()!impt[1], Integers()!impt[2]];
      if impt[1] eq 0 then
        impt[1] := mm;
      end if;
      if impt[2] eq 0 then
        impt[2] := mm;
      end if;
      ind1 := Index(eltorderm,pt3);
      ind2 := Index(eltorderm,impt);
      term3 := hvals2[ind2];
      num := num + (term1*term2 + term1*term3 + term2*term3);
    end for;
    err := RealField(10)!AbsoluteValue(num - Round(Real(num)));
    printf "For choice %o, we get error %o.\n",choice,err;
    if (err lt 10^(-5)) then
      Append(~choices,choice);
      Append(~errs,err);
    end if;  
  end for;
  badbad := false; 
  if #choices ge 2 then
    printf "We have more than one good choice. Maybe the image of Galois is
smaller than G.\n";
    bad := 0;
    bad2 := 1/bad;
  else
    best := choices[1];
    printf "Choice %o is best.\n",best;
  end if;
  Gtilde := seq[best];
  // Now, find all the conjugates of Gfine inside Gtilde.
  a, b := IsConjugate(GL(2,Integers(mm)),G,Gtilde);
  // Now, b^(-1) Gb = Conjugate(G,b) equals Gtilde
  Gtildenorm := Normalizer(GL(2,Integers(mm)),Gtilde);
  Gfinenew := Conjugate(Gfine,b);
  Gfinenorm := Normalizer(GL(2,Integers(mm)),Gfinenew);
  // Theory says that this will be a subgroup of Gtildenorm
  trans := RightTransversal(Gtildenorm,Gfinenorm);
  numconjs := #trans;
  Gfineconjlist := [ Conjugate(Gfinenew,trans[i]) : i in [1..#trans]];  
  printf "Gfine has %o conjugates inside Gtilde.\n",numconjs;

printf "Computing fpolynomial.\n";
fpolycomp := &*[ z - ellvals1[i] : i in [1..#ellvals1]];
fpolycheck := &*[ z + (Rsmall!AbsoluteValue(ellvals1[i])) : i in [1..#ellvals1]];

newcoefflist := [ Round(Real(Coefficient(fpolycomp,i))) : i in [0..Degree(fpolycomp)]];
maxerr := Max([ RealField(10)!AbsoluteValue(Coefficient(fpolycomp,i) - newcoefflist[i+1]) : i in [0..Degree(fpolycomp)]]);
fpoly := &+[ newcoefflist[i]*x^(i-1) : i in [1..#newcoefflist]];
printf "Maximal error on fpolynomial was %o.\n",maxerr;
maxcofsize := Max([ AbsoluteValue(Coefficient(fpolycheck,i)) : i in [0..Degree(fpolycheck)]]);
printf "Maximal coefficient size of f polynomial was %o.\n",RealField(10)!maxcofsize;
if (maxcofsize gt 10^decprec) then
  printf "The coefficients are too big. We need more decimal precision!\n";
  bad := 0;
  bad2 := 1/bad;
end if;
if (maxerr gt 0.01) then
  printf "The error is too large!\n";
  bad := 0;
  bad2 := 1/bad;
end if;
classlist := [];
CC := ConjugacyClasses(Gtilde);
for i in [1..#CC] do
  // Create polynomial for conjugacy class i
  printf "Working on class %o. ",i;
  cent := Centralizer(Gtilde,CC[i][3]);
  class := [ s^(-1)*CC[i][3]*s : s in Transversal(Gtilde,cent) ];
  Append(~classlist,class);
  poly := R!1;
  polycheck := RSTUV!1;  
  for g in class do
    term := C!0;
    for pt in eltorderm do
      a := pt[1];
      b := pt[2];
      // The action is on the right, because we transposed the groups
      impt := [ g[1][1]*a + g[2][1]*b, g[1][2]*a + g[2][2]*b ];
      impt := [ Integers()!impt[1], Integers()!impt[2]];
      if impt[1] eq 0 then
        impt[1] := mm;
      end if;
      if impt[2] eq 0 then
        impt[2] := mm;
      end if;
      ind1 := Index(eltorderm,pt);
      ind2 := Index(eltorderm,impt);
      term := term + hvals2[ind1]*ellvals2[ind2];      
    end for;
    poly := poly*(z-term);
    polycheck := polycheck*(z + (Rsmall!AbsoluteValue(term)));
  end for;
  roundpoly := 0;
  maxcurerror := RealField(10)!0;
  for n in [0..Degree(poly)] do
    newcoeff := Round(Real(Coefficient(poly,n)));
    rounderr := RealField(10)!AbsoluteValue(Coefficient(poly,n)-newcoeff);
    maxcurerror := Max(rounderr,maxcurerror);
    roundpoly := roundpoly + newcoeff*x^n;
  end for;
  maxcoeff := Max([ AbsoluteValue(Coefficient(polycheck,ijk)) : ijk in [0..Degree(polycheck)]]);
  maxerr := Max(maxerr,maxcurerror);  
  Append(~polylist,roundpoly);    
  printf "Maximal error on polynomial was %o.\n",maxcurerror;
  printf "Maximal coefficient size was %o.\n",RealField(10)!maxcoeff;
  if (maxcoeff gt 10^decprec2) then
    printf "The coefficient size is too big. We need more decimal precision.\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
end for;
printf "Maximal error was %o.\n",maxerr;
if (maxerr gt 0.01) then
  printf "Error! Maximal error was too large!\n";
  bad := 0;
  bad2 := 1/bad;
end if;

// GCD check
for i in [1..#polylist] do
  for j in [i+1..#polylist] do
    deg := Degree(GCD(polylist[i],polylist[j]));
    if (deg gt 0) then
      printf "Error! Polynomials %o and %o have a common factor.\n",i,j;
    end if;
  end for;
end for;

printf "We have p = %o.\n",p;
triv := Elements(DirichletGroup(1))[1];
quadcheck := [ d : d in Divisors(p*Conductor(E)) | IsSquarefree(d)] cat
[ -d : d in Divisors(p*Conductor(E)) | IsSquarefree(d) ];
quadchars := <>;
for n in [1..#quadcheck] do
  d := quadcheck[n];
  if (d eq 1) then
    Append(~quadchars,triv);
  else
    Append(~quadchars,KroneckerCharacter(FundamentalDiscriminant(d)));
  end if;
end for;
bigquadcheck := [ quadcheck : i in [1..numconjs]];
bigquadchars := < quadchars : i in [1..numconjs]>;
done := false;
pp := 0;
while done eq false do
  pp := NextPrime(pp);    
  if GCD(pp,2*p*Conductor(E)) eq 1 then
    FF := GF(pp);
    R<xx> := PolynomialRing(FF);
    I := ideal<R | R!fpoly>;
    Q, phi := quo<R|I>;
    elt := phi(Evaluate(R!h,xx)*xx^pp);
    tr := Trace(elt);
    zerolist := [ i : i in [1..#polylist] | Evaluate(R!polylist[i],tr) eq 0 ];
    if #zerolist gt 1 then
      printf "The prime %o divides the resultant of %o and %o.\n",pp,zerolist[1],zerolist[2];
    end if;
    if #zerolist eq 1 then
      newbigquadchars := <>;
      printf "For pp = %o, we have the following.\n",pp;
      elt := CC[zerolist[1]][3];
      printf "Element is %o.\n",elt;
      chivallist := [];
      for dd in [1..numconjs] do
        chival := 0;
        if (elt in Gfineconjlist[dd]) then
          chival := 1;
        else
          chival := -1;
        end if;
        printf "For conjugate %o, chival = %o.\n",dd,chival;
        indlist := [ k : k in [1..#bigquadchars[dd]] | Evaluate(bigquadchars[dd][k],pp) eq chival ];
        newquadcheck := [ bigquadcheck[dd][i] : i in indlist ];
        newquadchars := < bigquadchars[dd][i] : i in indlist >;
        if (#newquadcheck lt #bigquadcheck[dd]) then
          printf "Old possibilities %o.\n",bigquadcheck[dd];
          printf "Possibilities now %o.\n",newquadcheck;
        end if;
        Append(~newbigquadchars,newquadchars);
        bigquadcheck[dd] := newquadcheck;
      end for;
      //printf "%o.\n",chivallist;
      if &and[ #bigquadcheck[dd] eq 1 : dd in [1..numconjs]] then
        done := true; 
      end if;
      bigquadchars := newbigquadchars;
    end if;
    if #zerolist eq 0 then
      printf "For pp = %o, we didn't find any classes!\n",pp;
      bad := 0;
      bad2 := 1/bad;
    end if;
  end if;
end while;
for dd in [1..numconjs] do
  printf "For conjugate %o, the unique twist is %o.\n",dd,bigquadcheck[dd][1];
end for;
// Insert here!
if (passone eq true) then
  for it in [1..#squarefreedivs] do
    // Make list of OK options.
    evalp := Evaluate(squarefreedivs[it],curt);
    optlist := [];
    for dd in [1..numconjs] do
      opt := evalp/bigquadcheck[dd][1];
      opt := SquarefreeFactorization(Integers()!(opt*Denominator(opt)^2));
      Append(~optlist,opt);
    end for; 
    options[it] := optlist;
  end for;  
  passone := false;
  printf "After t = %o, the options lists were the following.\n",curt;
  for it in [1..#squarefreedivs] do
    printf "For divisor %o, options = %o.\n",squarefreedivs[it],options[it];
  end for; 
else
  for it in [1..#squarefreedivs] do
    evalp := Evaluate(squarefreedivs[it],curt);
    optlist := [];
    for dd in [1..numconjs] do
      opt := evalp/bigquadcheck[dd][1];
      opt := SquarefreeFactorization(Integers()!(opt*Denominator(opt)^2));
      Append(~optlist,opt);
    end for; 
    newoptlist := [ j : j in options[it] | j in optlist ];
    options[it] := newoptlist;
  end for; 
  printf "After t = %o, the options lists were the following.\n",curt;
  for it in [1..#squarefreedivs] do
    printf "For divisor %o, options = %o.\n",squarefreedivs[it],options[it];
  end for; 
  count := &+[ #options[it] : it in [1..#squarefreedivs]];
  if (count eq numconjs) then
    printf "We should have found all of the models!\n";
    bigdone := true;
  end if;   
end if;
end while;

// Choose the simplest model.
modellist := [];
modelsize := [];
for it in [1..#squarefreedivs] do
  for j in [1..#options[it]] do
    twistpoly := options[it][j]*Evaluate(squarefreedivs[it],t);
    denomlcm := LCM([Denominator(Coefficient(Numerator(twistpoly),i)) : i in [0..Degree(twistpoly)]]);
    FF := Factorization(denomlcm);
    multfac := 1;
    for n in [1..#FF] do
      multfac := multfac*FF[n][1]^Ceiling(FF[n][2]/2);
    end for;
    twistpoly := twistpoly*multfac^2;
    model := QuadraticTwist(Et,twistpoly);
    A := aInvariants(model)[4];
    B := aInvariants(model)[5];
    FF := Factorization(GCD([PolynomialRing(Integers())!Numerator(A),PolynomialRing(Integers())!Numerator(B)]));
    divfac := Numerator(F!1);
    Afac := Factorization(PolynomialRing(Integers())!Numerator(A));
    Bfac := Factorization(PolynomialRing(Integers())!Numerator(B));
    for n in [1..#FF] do
      pp := FF[n][1];
      aind := Index([ Afac[n][1] : n in [1..#Afac]],pp);
      bind := Index([ Bfac[n][1] : n in [1..#Bfac]],pp);
      if aind ne 0 then
        aval := Afac[aind][2];
      else
        aval := 0;
      end if;
      if bind ne 0 then
        bval := Bfac[bind][2];
      else
        bval := 0;
      end if;
      expo := Min(Floor(aval/4),Floor(bval/6));
      divfac := divfac*pp^expo;
    end for;
    divfac := Evaluate(divfac,t);
    A := A/(divfac^4);
    B := B/(divfac^6);
    if (Denominator(A) ne 1) or (Denominator(B) ne 1) then
      printf "Error! A or B are not integral.\n";
      bad := 0;
       bad2 := 1/bad;
    end if;
    modelstr := Sprintf("%o",EllipticCurve([0,0,0,A,B]));
    printf "Model option %o is %o.\n",#modellist+1,modelstr;
    Append(~modellist,EllipticCurve([0,0,0,A,B]));
    Append(~modelsize,#modelstr);
  end for;
end for;
simplechoice := Index(modelsize,Min(modelsize));
ainvars := aInvariants(modellist[simplechoice]);
A := ainvars[4];
B := ainvars[5];
R<t> := PolynomialRing(Integers());
A := R!Numerator(A);
B := R!Numerator(B);
fileout := "eqf" cat m cat ".txt";
ls := Split(m,".");
lab := "X" cat ls[1] cat "_" cat ls[2] cat "_" cat ls[3] cat "_" cat ls[4];
System("rm " cat fileout);
PrintFile(fileout,"F<t> := FunctionField(Rationals());");
PrintFile(fileout,Sprintf("%o := EllipticCurve([0,0,0,%o,%o]);",lab,A,B));
PrintFile(fileout,Sprintf("return %o;",lab));
quit;
