// This Magma script is for computing models of modular curves
// by building each modular curve as a cover of a prior one, which must
// have genus zero.

// For this script, the input is a file. This file must contain
// data that specifies a prime p, a subgroup of GL_2(Z/p^n Z), and
// the Fourier expansion of a modular function that is a hauptmodul for
// that subgroup.

// The assumption is that the subgroups of GL_2(Z/p^n Z) act on the left,
// i.e. on column vectors. The prior version of this script were written
// with a right action, and so once the subgroup is parsed, we transpose
// the groups.

// Finally, this version outputs the model and the covering map.

p := 0;

if (not assigned l) then
  printf "This script requires a command line argument.\n";
  printf "The usage is magma l:=label model.m";
  quit;
else
  parse := Split(l,".");
  N := StringToInteger(parse[1],10);
  ind := StringToInteger(parse[2],10);
  gen := StringToInteger(parse[3],10);
  tiebreak := StringToInteger(parse[4],10);
  chk, p, levpower := IsPrimePower(N);
  assert chk;
end if;

// Read subgroup data

Attach("../groups/gl2.m");
load "../groups/gl2data.m";
// GL2Load("gl2_" cat IntegerToString(p) cat "adic.txt");

// For each group H, we must have a covering group Hcover
// and H must literally be a subgroup of Hcover. We precompute
// particular conjugates of the groups in files gl2_padic.txt
// to ensure that this holds. 

subfilename := "subdata" cat IntegerToString(p) cat ".txt";
subdata := eval Read(subfilename);
subind := Index([ subdata[i][1] : i in [1..#subdata]],l);

// These lines are to fool the Magma parser into working.
// These are identifiers that are used inside if statements
// that are referred to again later inside other if statements

E2 := 0;
xmodfunc := 0;
newC := 0;
ymodfunc := 0;
AA := 0;
BB := 0;
C2 := 0;
s2 := 0;
phi3 := 0;
newratfunc := 0;
haupt := 0;
newhaupt := 0;

// Step 1 - Build covering group and read the stored Fourier expansion.

logfilename := "model" cat l cat ".out";
System("rm " cat logfilename);
SetLogFile(logfilename);

coverlabel := subdata[subind][3];
parse := Split(coverlabel,".");
Ncover := StringToInteger(parse[1],10);
indcov := StringToInteger(parse[2],10);
gencover := StringToInteger(parse[3],10);
tiebreak := StringToInteger(parse[4],10);

printf "The degree of that covering map is %o.\n",ind/indcov;
K<zeta> := CyclotomicField(N);
prec := 110*N;
R<q> := PuiseuxSeriesRing(K : Precision := prec);


// At this stage, we take the transposes of the generators.

genlist := Generators(subdata[subind][2]);
H := sub<GL(2,Integers(N)) | [ Transpose(g) : g in genlist]>;
Hcover := 0;
if coverlabel eq "1.1.0.1" then
  Hcover := GL(2,Integers(N));
else
  coverind := Index([subdata[i][1] : i in [1..#subdata]],coverlabel);
  genlist2 := Generators(subdata[coverind][2]);
  Hcover := GL2Lift(sub<GL(2,Integers(Ncover)) | [ Transpose(g) : g in genlist2]>,N);
end if;

// We have stored the Fourier expansion of a hauptmodul
// We suppose that the Fourier expansion was stored with z as the root of unity.
// This root of unity may be different than zeta. The power series ring
// should be defined in the file. The modular function should be called haupt

if (coverlabel ne "1.1.0.1") then
  filename := "modfunc" cat coverlabel cat ".txt";
  str := Read(filename);
  haupt := eval str;
  cycfield := BaseRing(Parent(haupt));
  ordofz := (p/(p-1))*Degree(cycfield);
  pow := Floor(N/ordofz);
  expdenom := ExponentDenominator(haupt);
  newhaupt := R!0;
  for n in [Valuation(haupt)*expdenom..AbsolutePrecision(haupt)*expdenom-1] do
    cof := Eltseq(Coefficient(haupt,n/expdenom));
    term := R!(&+[ cof[i]*zeta^(pow*(i-1)) : i in [1..#cof]]*q^(n/expdenom));
    newhaupt := newhaupt + term;
  end for;
  newhaupt := newhaupt + BigO(q^AbsolutePrecision(haupt));
  haupt := newhaupt;
else
  haupt := jInvariant(q);
end if;

// This function takes an element r of (Z/NZ) and
// lifts it to an integer between 1 and N

function lift(r,N)
  liftr := Integers()!r;
  liftr := liftr mod N;
  if (liftr eq 0) then
    liftr := N;
  end if;
  return liftr;
end function;

// Simplification function. This takes as input a rational function f
// and returns a simplier version of f, obtained by composing
// with a linear fractional transformation. This transformation is also
// returned.

/*
function size(f)
  num := Numerator(f);
  denom := Denominator(f);
  coflist := [ Denominator(Coefficient(num,n)) : n in [0..Degree(num)]];
  coflist := coflist cat [ Denominator(Coefficient(denom,n)) : n in [0..Degree(denom)]];
  mult := LCM(coflist);
  num := num*mult;
  denom := denom*mult;
  if Degree(num) gt 0 then
    ret := &+[ Log(1+AbsoluteValue(Numerator(Coefficient(num,n)))) : n in [0..Degree(num)]];
  else
    ret := Log(1);
  end if;
  if Degree(denom) gt 0 then
    ret := ret + (&+[ Log(1+AbsoluteValue(Numerator(Coefficient(denom,n)))) : n in [0..Degree(denom)]]);
  end if;
  return ret;
end function;
*/

function size(f)
  return #Sprintf("%o",f);
end function;

// Supersimplify functions - This is probably only necessary on
// functions coming from index 3 or 4 covers because the rational
// functions that are output are ridiculously complicated

function transcheck(f)
  //printf "Finding optimal translation.\n";
  t := Parent(f).1;
  done := true;
  if size(Evaluate(f,t-1)) lt size(f) then
    upp := 0;
    mid := -1;
    low := -2;
    while size(Evaluate(f,t+low)) lt size(Evaluate(f,t+mid)) do
      upp := mid;
      mid := low;
      low := low*2;
    end while;
    done := false;
  end if;
  if size(Evaluate(f,t+1)) lt size(f) then
    low := 0;
    mid := 1;
    upp := 2;
    while size(Evaluate(f,t+2*mid)) lt size(f) do
      low := mid;
      mid := 2*mid;
      upp := 2*mid;
    end while;
    done := false;
  end if;
  if done eq false then
    uppsiz := size(Evaluate(f,t+upp));
    midsiz := size(Evaluate(f,t+mid));
    lowsiz := size(Evaluate(f,t+low));
    round := 0;
    while done eq false do
      round := round + 1;
      //printf "Bisection method, round %o.\n",round;
      //printf "low = %o, lowsiz = %o.\n",low,lowsiz;
      //printf "mid = %o, midsiz = %o.\n",mid,midsiz;
      //printf "upp = %o, uppsiz = %o.\n",upp,uppsiz;
      if (upp-low) le 1 then
        done := true;
      else
        check1 := Round((low+mid)/2);
        check2 := Round((mid+upp)/2);
        newsiz1 := size(Evaluate(f,t+check1));
        newsiz2 := size(Evaluate(f,t+check2));
        sizelist := [lowsiz,newsiz1,midsiz,newsiz2,uppsiz];
        ind := Index(sizelist,Min(sizelist));
        if (ind eq 2) then
          upp := mid;
          uppsiz := midsiz;
          mid := check1;
          midsiz := newsiz1;
        end if;
        if (ind eq 3) then
          low := check1;
          lowsiz := newsiz1;
          upp := check2;
          uppsiz := newsiz2;
        end if;
        if (ind eq 4) then
          low := mid;
          lowsiz := midsiz;
          mid := check2;
          midsiz := newsiz2;
        end if;
      end if;
    end while;
    f2 := Evaluate(f,t+mid);
    if size(f2) lt size(f) then
      //printf "It is %o.\n",mid;
      retM := Matrix([[1,mid],[0,1]]);
      //printf "It is %o.\n",mid;
      retM := Matrix([[1,mid],[0,1]]);
    else
      //printf "It is %o.\n",0;
      f2 := f;
      retM := Matrix([[1,0],[0,1]]);
    end if;
  else
    f2 := f;
    //printf "It is %o.\n",0;
    retM := Matrix([[1,0],[0,1]]);
  end if;
  return f2,retM;
end function;

// This function returns the optimal scaling of the
// polynomial g with relatively prime integer coefficients.

function scale(g)
  coflist := Coefficients(g);
  ret := 1;
  if #[ i : i in [1..#coflist] | coflist[i] ne 0] ge 2 then
    gcd1 := GCD([Coefficient(g,i) : i in [1..Degree(g)]]);
    //printf "GCD1 = %o.\n",gcd1;
    gcd2 := GCD([Coefficient(g,i) : i in [0..Degree(g)-1]]);
    //printf "GCD2 = %o.\n",gcd2;
    //printf "Computing prime factorization.\n";
    primelist := PrimeDivisors(LCM(gcd1,gcd2));
    //printf "Done!\n";
    for j in [1..#primelist] do
      p := primelist[j];
      vallist := [ Valuation(Coefficient(g,n),p) : n in [0..Degree(g)]];
      //printf "Checking p = %o.\n",p;
      if Valuation(Coefficient(g,Degree(g)),p) gt 0 then
        //printf "Exponent should be negative.\n";
        //printf "List = %o.\n",[ vallist[n+1]/n : n in [1..Degree(g)]];
        ex := Floor(Min([ vallist[n+1]/n : n in [1..Degree(g)]]));
        ex := -ex;
      else
        //printf "Exponent should be positive.\n";
        //printf "List = %o.\n",[ vallist[n+1]/(Degree(g)-n) : n in [0..Degree(g)-1]];
        ex := Floor(Min([ vallist[n+1]/(Degree(g)-n) : n in [0..Degree(g)-1]]));
      end if;

      ret := ret*p^(ex);
    end for;
  end if;
  return ret;
end function;

function scale2(f)
  t := Parent(f).1;
  num := Numerator(f);
  denom := Denominator(f);
  coflist := [ Denominator(Coefficient(num,n)) : n in [0..Degree(num)]];
  coflist := coflist cat [ Denominator(Coefficient(denom,n)) : n in [0..Degree(denom)]];
  mult := LCM(coflist);
  num := PolynomialRing(Integers())!(num*mult);
  denom := PolynomialRing(Integers())!(denom*mult);
  //printf "Current size = %o.\n",size(f);
  //printf "Scaling numerator.\n";
  r1 := scale(num div Content(num));
  //printf "Scaling denominator.\n";
  r2 := scale(denom div Content(denom));
  primelist := PrimeDivisors(Numerator(r1)*Denominator(r1)*Numerator(r2)*Denominator(r2));
  primevals := [];
  for i in [1..#primelist] do
    v1 := Valuation(r1,primelist[i]);
    v2 := Valuation(r2,primelist[i]);
    if (v1 lt 0) and (v2 lt 0) then
      Append(~primevals,Max(v1,v2));
    else
      if (v1 gt 0) and (v2 gt 0) then
        Append(~primevals,Min(v1,v2));
      else
        Append(~primevals,0);
      end if;
    end if;
  end for;
  if #primelist gt 0 then
    scalfac := &*[ primelist[i]^primevals[i] : i in [1..#primelist]];
  else
    scalfac := 1;
  end if;
  //printf "Scaling factor %o.\n",scalfac;
  newf := Evaluate(f,scalfac*t);
  retsize := size(newf);
  //printf "Size of scaled f = %o.\n",retsize;
  return scalfac,retsize;
end function;

// Supersimplify function

function supersimplify(f)
  printf "Call to supersimplify.\n";
  t := Parent(f).1;
  j := f;
  changemat := Matrix([[1,0],[0,1]]);
  prevsize := size(j);
  prevj := j;
  prevmat := changemat;
  alldone := false;
  while alldone eq false do
  printf "Entering simplification iteration. Current size = %o.\n",prevsize;
  scal, newsize := scale2(j);
  jnew := Evaluate(j,t*scal);
  changemat := changemat*Matrix([[scal,0],[0,1]]);
  printf "Size after scaling = %o.\n",newsize;

  // Do translations - do this by
  // factoring num and denom modulo prime
  // powers

  //printf "Translation check.\n";
  num := PolynomialRing(Rationals())!Numerator(jnew);
  denom := PolynomialRing(Rationals())!Denominator(jnew);
  coflist := [ Denominator(Coefficient(num,n)) : n in [0..Degree(num)]];
  num := num*LCM(coflist);
  num := PolynomialRing(Integers())!num;
  coflist := [ Denominator(Coefficient(denom,n)) : n in [0..Degree(denom)]];
  denom := denom*LCM(coflist);
  denom := PolynomialRing(Integers())!denom;
  if Degree(num) gt 0 then
    FF := Factorization(num);
    sqrfreenum := &*[ FF[i][1] : i in [1..#FF]];
  else
    sqrfreenum := PolynomialRing(Integers())!1;
  end if;
  if Degree(denom) gt 0 then
    FF := Factorization(denom);
    sqrfreedenom := &*[ FF[i][1] : i in [1..#FF]];
  else
    sqrfreedenom := PolynomialRing(Integers())!1;
  end if;
  if (Degree(sqrfreenum) gt 0) and (Degree(sqrfreedenom) gt 0) then
    D := GCD(Discriminant(sqrfreenum),Discriminant(sqrfreedenom));
  end if;
  if Degree(sqrfreenum) eq 0 then
    D := Discriminant(sqrfreedenom);
  end if;
  if Degree(sqrfreedenom) eq 0 then
    D := Discriminant(sqrfreenum);
  end if;
  plist := PrimeDivisors(D);
  for n in [1..#plist] do
    pp := plist[n];
    F := GF(pp);
    RRRR<zzzz> := PolynomialRing(F);
    done := false;
    while done eq false do
      //printf "Translation check at pp = %o.\n",pp;
      num := PolynomialRing(Rationals())!Numerator(jnew);
      denom := PolynomialRing(Rationals())!Denominator(jnew);
      coflist := [ Denominator(Coefficient(num,n)) : n in [0..Degree(num)]];
      num := num*LCM(coflist);
      num := RRRR!num;
      coflist := [ Denominator(Coefficient(denom,n)) : n in [0..Degree(denom)]];
      denom := denom*LCM(coflist);
      denom := RRRR!denom;
      prod := RRRR!1;
      if (num ne 0) then
        prod := prod*num;
      end if;
      if (denom ne 0) then
        prod := prod*denom;
      end if;
      fac := Factorization(prod);
      //printf "Factorization = %o.\n",fac;
      if (#fac eq 1) and Degree(fac[1][1]) eq 1 then
        r := Integers()!(Roots(prod)[1][1]);
        chk1 := Evaluate(jnew,pp*t+r);
        chk2 := Evaluate(jnew,pp*t+(-pp+r));
        size1 := size(chk1);
        size2 := size(chk2);
       //printf "Possible new sizes are %o and %o.\n",size1,size2;
        minsize := Min(size1,size2);
        if (minsize lt newsize) then
          if (size1 eq minsize) then
            jnew := chk1;
            changemat := changemat*Matrix([[pp,r],[0,1]]);
            newsize := size1;
            //printf "Transformation %o. New size = %o.\n",pp*t+r,newsize;
          else
            jnew := chk2;
            changemat := changemat*Matrix([[pp,r-pp],[0,1]]);
            newsize := size2;
            //printf "Transformation %o. New size = %o.\n",pp*t+(-pp+r),newsize;
          end if;
        else
          done := true;
        end if;
      else
        done := true;
      end if;
    end while;
  end for;
  printf "Translation check done. New size = %o.\n",newsize;
  j := jnew;

  // Do some rounds of random substitutions
  done := false;
  bound := 5;
  it := 0;
  ptlist := [];
  for aa in [-bound..bound] do
    for bb in [-bound..bound] do
      for cc in [-bound..bound] do
        for dd in [0..bound] do
          if GCD([aa,bb,cc,dd]) eq 1 then
            if aa*dd - bb*cc ne 0 then
              Append(~ptlist,<aa,bb,cc,dd>);
            end if;
          end if;
        end for;
      end for;
    end for;
  end for;
  printf "Doing up to 5 rounds of substitutions.\n";
  while done eq false do
    it := it + 1;
    cursize := size(j);
    //printf "Beginning iteration %o. Size = %o.\n",it,cursize;
    minsize := cursize;
    for n in [1..#ptlist] do
      pt := ptlist[n];
      aa := pt[1];
      bb := pt[2];
      cc := pt[3];
      dd := pt[4];
      jnew := Evaluate(j,(aa*t+bb)/(cc*t+dd));
      chksize := size(jnew);
      if (chksize lt minsize) then
        //printf "Index %o has size %o. pt = %o\n",n,chksize,pt;
        minsize := chksize;
        ind := n;
      end if;
    end for;
    if minsize lt cursize then
      pt := ptlist[ind];
      aa := pt[1];
      bb := pt[2];
      cc := pt[3];
      dd := pt[4];
      jnew := Evaluate(j,(aa*t+bb)/(cc*t+dd));
      changemat := changemat*Matrix([[aa,bb],[cc,dd]]);
      printf "After round %o size = %o.\n",it,minsize;
      j := jnew;
      //printf "j = %o.\n",j;
      if (it ge 5) then
        done := true;
      end if;
    else
      done := true;
    end if;
  end while;
  // Translation rounds
  printf "Doing two more random checks.\n";
  j, retM := transcheck(j);
  changemat := changemat*retM;
  // Hack for group number 7
  if size(Evaluate(j,t/31)) lt size(j) then
    j := Evaluate(j,t/31);
    changemat := changemat*Matrix([[1,0],[0,31]]);
  end if;
  printf "Final size is %o.\n",size(j);
  if size(j) ge prevsize then
    alldone := true;
    j := prevj;
    changemat := prevmat;
  else
    prevj := j;
    prevmat := changemat;
    prevsize := size(j);
  end if;
  end while;
  return j, changemat;
end function;

FF<tt> := FunctionField(Rationals());
RR<t> :=PolynomialRing(Rationals());
RRR<x,y> := PolynomialRing(Rationals(),2);
ZZ<b> := PolynomialRing(Integers());

// Compute the Weierstrass p-function to a precision of q^(prec/N).
// This is up to and includeing q^(prec/N).
// This routine returns the Fourier expansion
// of normalized version of p((c*t+d)/N;t)
// This is p multiplied by (9/Pi^2)
// We use the formula for the Fourier expansion from Chapter 4 of
// Diamond and Shurman.
// We hope this works just the same for p > 2.

function weier(c,d,N,pr)
  c := c mod N;
  d := d mod N;
  const := R!(-3);
  if (c eq 0) then
    cosval := (1/2)*(zeta^d + zeta^(-d));
    const := const + R!(-18/(cosval - 1));
    pr := pr + 1;
  end if;
  ret := const;
  for m in [1..pr+N] do
    term := K!0;
    list1 := [ r*zeta^(d*r) : r in Divisors(m) | (Floor(m/r)-c) mod N eq 0 ];
    if #list1 gt 0 then
      term := term - 36*(&+list1);
    end if;
    list2 := [ r*zeta^(-d*r) : r in Divisors(m) | (Floor(m/r)-N+c) mod N eq 0];
    if #list2 gt 0 then
      term := term - 36*(&+list2);
    end if;
    if (m mod N eq 0) then
      term := term + 72*SumOfDivisors(Floor(m/N));
    end if;
    ret := ret + term*q^(m/N);
  end for;
  ret := ret + BigO(q^((pr+N+1)/N));
  return ret;
end function;

// This function takes two q-expansions and a degree bound
// The first one is a modular function, the second
// is a modular function of degree 1, and the
// third is a degree bound. This function tries to represent
// the first input as a rational function in the second.
// The two modular functions MUST belong to the same
// power series ring.
// The range of coefficients needed is from
// val2+deg*val1 to val2+deg*val1+2*deg+1

function ratfuncrep(modfunc,haup,deg)
  printf "Call to ratfuncrep with deg = %o.\n",deg;
  if IsWeaklyZero(modfunc) then
    return Parent(tt)!0;
  end if;
  field := BaseRing(Parent(modfunc));
  q := Parent(modfunc).1;
  M := ZeroMatrix(field,2*deg+2,2*deg+2);
  den := ExponentDenominator(haup);
  val1 := Min(0,Valuation(haup)*den);
  val2 := Min(0,Valuation(modfunc)*den);
  //printf "den = %o.\n",den;
  timet := Cputime();
  printf "Building last %o rows of the matrix.\n",deg+1;
  printf "Using coefficients %o to %o.\n",(val2+deg*val1)/den,(val2+deg*val1+2*deg+1)/den;
  for m in [0..deg] do
    haupprec := (m*val1 + 2*deg+2)/den;
    func2 := -(haup + BigO(q^(haupprec)))^(deg-m)*modfunc;
    //printf "For m = %o, the precision on func2 is from %o to %o.\n",m,Valuati\
on(func2),AbsolutePrecision(func2);
    //printf "For m = %o, precision needed is from %o to %o.\n",m,(val2+(deg-m)*val1)/den,(val2+(deg-m)*val1+2*deg+1)/den;
    //printf "Coefficient range %o to %o.\n",(val2+deg*val1)/den,(val2+deg*val1+2*deg+1)/den;
    for n in [1..2*deg+2] do
      M[m+deg+2][n] := Coefficient(func2,(val2+deg*val1+n-1)/den);
    end for;
  end for;
  printf "Time taken was %o.\n",Cputime(timet);
  timet := Cputime();
  printf "Building the first %o rows of the matrix.\n",deg+1;
  for m in [0..deg] do
    haupprec := (val2+m*val1+2*deg+2)/den;
    func2 := (haup+BigO(q^(haupprec)))^(deg-m);
    //printf "For m = %o, precision on func2 ranges from %o to %o.\n",m,Valuati\
on(func2),AbsolutePrecision(func2);
    //printf "Precision needed is %o to %o.\n",(val2+(deg-m)*val1)/den,(val2+(d\
eg-m)*val1+2*deg+1)/den;
    for n in [1..2*deg+2] do
      M[m+1][n] := Coefficient(func2,(val2+deg*val1+n-1)/den);
    end for;
  end for;
  printf "Time taken was %o.\n",Cputime(timet);
  printf "Solving the linear system of size %ox%o.\n",2*deg+2,2*deg+2;
  timet := Cputime();
  V := Nullspace(M);
  printf "Time taken was %o.\n",Cputime(timet);
  printf "Null space has dimension %o.\n",Dimension(V);
  v := V.1;
  QQ := Rationals();
  // We really hope that all the entries of V can be coerced into QQ
  numcoeffs := [ QQ!v[i] : i in [1..deg+1]];
  denomcoeffs := [ QQ!v[i] : i in [deg+2..2*deg+2]];
  mult := LCM([Denominator(v[i]) : i in [1..2*deg+2]]);
  numcoeffs := [ numcoeffs[i]*mult : i in [1..deg+1]];
  denomcoeffs := [ denomcoeffs[i]*mult : i in [1..deg+1]];
  ret := &+[ numcoeffs[i]*tt^(deg+1-i) : i in [1..deg+1]]/&+[ denomcoeffs[i]*tt\
^(deg+1-i) : i in [1..deg+1]];
  // New ret check
  numer := &+[ numcoeffs[i]*tt^(deg+1-i) : i in [1..deg+1]];
  denom := &+[ denomcoeffs[i]*tt^(deg+1-i) : i in [1..deg+1]];
  for d in [2..Dimension(V)] do
    vd := V.d;
    numerd := &+[ (QQ!vd[i])*tt^(deg+1-i) : i in [1..deg+1]];
    denomd := &+[ (QQ!vd[i])*tt^(2*deg+2-i) : i in [deg+2..2*deg+2]];
    if (numerd*denom - numer*denomd) ne 0 then
      printf "ERROR in ratfuncrep! is not unique!\n";
      bad := 0;
      bad2 := 1/bad;
    end if;    
  end for;
/*
  retcheck := &+[ numcoeffs[i]*(haup+BigO(q^AbsolutePrecision(modfunc)))^(deg+1-i) : i in [1..deg+1]]/&\
+[
  denomcoeffs[i]*(haup+BigO(q^AbsolutePrecision(modfunc)))^(deg+1-i) : i in [1..deg+1]];
  if IsWeaklyZero(retcheck - modfunc) then
    printf "Success! The linear system worked.\n";
    printf "The result was %o.\n",ret;
  else
    printf "Error! Solving the linear system failed!\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
*/
  return ret;
end function;

// This function act takes an element of the subspace of Eisenstein series
// represented by a vector giving the coefficients in terms of the
// basislist with entries in K, a level N, a matrix g and it computes the 
// image of this element under the matrix g.

// The action is on the right, as in Shimura.

function act(elt,g,N,basislist)
  newvec := [ K!0 : i in [1..#basislist]];
  det := lift(Determinant(g),N);
  for i in [1..#basislist-1] do
    a := basislist[i][1];
    b := basislist[i][2];
    imag := <lift(g[1][1]*a+g[2][1]*b,N),lift(g[1][2]*a+g[2][2]*b,N)>;
    if (imag[1] gt N/2) then
      imag[1] := N-imag[1];
      imag[2] := N-imag[2];
    end if;
    if ((imag[1] eq 0) or (imag[1] eq N/2)) and (imag[2] gt N/2) then
      imag[1] := N-imag[1];
      imag[2] := N-imag[2];
    end if;
    imag[1] := imag[1] mod N;
    imag[2] := imag[2] mod N;
    ind := Index(basislist,imag);
    if (ind eq 0) then
      printf "Error! The vector %o is not in our basis list!.\n",imag;
      bad := 0;
      bad2 := 1/bad; 
    end if;
    // Act on elt by zeta^i -> zeta^(i*det)
    coeffs := Eltseq(elt[i]);
    newvec[ind] := &+[ coeffs[i]*zeta^((i-1)*det) : i in [1..#coeffs]];
  end for;
  c := newvec[#basislist];
  for i in [1..#basislist] do
    newvec[i] := newvec[i] - c;
  end for;  
  newvec2 := [ newvec[i] : i in [1..#basislist-1]];
  return VectorSpace(K,#basislist-1)!newvec2;
end function;

// Step 2 - Find a subgroup K of H so that K has more cusps that Hcover.

Hcovercusps := GL2CuspCount(Hcover);
indexbound := 1;

found := false;
while (found eq false) do
  L := LowIndexSubgroups(H,<indexbound,indexbound>);
  Lind := 1;
  done := false;
  if #L eq 0 then
    done := true;
  end if;
  while done eq false do
    mo := MinimalOvergroups(GL(2,Integers(N)),L[Lind]);
    overcusps := Max([ GL2CuspCount(mo[i]) : i in [1..#mo]]);
    if (GL2DeterminantIndex(L[Lind]) eq 1) and (GL2CuspCount(L[Lind]) gt overcusps) then
      found := true;
      done := true;
      subsub := L[Lind];
      printf "Setting subsub to be subgroup %o of index %o.\n",Lind,indexbound;
    end if;
    if (done eq false) then
      Lind := Lind + 1;
      if Lind gt #L then
        done := true;
      end if;
    end if;
  end while;
  if (done eq true) and (found eq false) then
    indexbound := indexbound + 1;
  end if;
end while;
cusps := GL2CuspCount(subsub);

// Step 3 - Compute Eisenstein series

// First do the forms that transform nicely under SL_2.
// Note that there are 3*N^2/8 cusps on Gamma(N) if N is a power of 2, and so the space of Eisenstein
// series (which should be spanned by the xcoords) has dimension 3*N^2/8 - 1. The relation between these
// is that the sum of all of them is zero (since the sum of all of them is a holomorphic modular form of
// weight 2 on Gamma(N)).

basislist := [];
for a in [0..Floor(N/2)] do
  for b in [0..N-1] do
    if GCD([a,b,N]) eq 1 then
      addtolist := true;
      if (a eq 0) and (b gt N/2) then
        addtolist := false;
      end if;
      if (a eq N/2) and (b gt N/2) then
        addtolist := false;
      end if;
      if addtolist eq true then
        //printf "Adding %o to the basis list.\n",<a,b>;
        Append(~basislist,<a,b>);
      end if;
    end if;
  end for;
end for;
lastbasis := basislist[#basislist];
dimen := #basislist - 1;
printf "The space of Eisenstein series has dimension %o.\n",dimen;

// Represent an element of M_2(Gamma) that is a linear combination of the p_tau as a list
// of coefficients in Q(zeta) corresponding to the basis vectors.

printf "Computing action of generators of subsub intersect SL_2 on Eisenstein series for Gamma(%o).\n",N;

matlist := [];
sl2sub := subsub meet SL(2,Integers(N));
for g in Generators(sl2sub) do
  // Compute a matrix representing g on the space.
  M := ZeroMatrix(Rationals(),dimen,dimen);
  for i in [1..dimen] do
    // We could call act here, but it is wasteful since we only need the
    // image of a single basis element
    rowmat := ZeroMatrix(K,1,#basislist);
    a := basislist[i][1];
    b := basislist[i][2];
    imag := <lift(g[1][1]*a+g[2][1]*b,N),lift(g[1][2]*a+g[2][2]*b,N)>;
    if (imag[1] gt N/2) then
      imag[1] := N-imag[1];
      imag[2] := N-imag[2];
    end if;
    if ((imag[1] eq 0) or (imag[1] eq N/2)) and (imag[2] gt N/2) then
      imag[1] := N-imag[1];
      imag[2] := N-imag[2];
    end if;
    imag[1] := imag[1] mod N;
    imag[2] := imag[2] mod N;
    indind := Index(basislist,imag);
    if (indind eq 0) then
      printf "Error! The vector %o is not in our basis list!.\n",imag;
      bad := 0;
      bad2 := 1/bad; 
    end if;
    rowmat[1][indind] := 1;
    if rowmat[1][#basislist] ne 0 then
      c := rowmat[1][#basislist];
      for j in [1..#basislist] do
        rowmat[1][j] := rowmat[1][j] - c;
      end for;
    end if;
    for j in [1..dimen] do
      M[j][i] := rowmat[1][j];
    end for;
  end for;
  Append(~matlist,M);
end for;

I := IdentityMatrix(Rationals(),dimen);
if #matlist eq 0 then
  Append(~matlist,I);
end if;
printf "Finding vectors invariant under subsub intersect SL_2.\n";
Ker := Kernel(Transpose(matlist[1]-I));
for m in [2..#matlist] do
  Ker := Ker meet Kernel(Transpose(matlist[m]-I));
end for;
kerbasis := Basis(Ker);
printf "The dimension of the space of Eisenstein series for subsub intersect SL_2 is %o.\n",#kerbasis;
if (#kerbasis ne (cusps - 1)) then
  printf "Error! We didn't get enough Eisenstein series!.\n";
end if;

// Now we look at the Q-span of the forms with coefficients in Q(zeta_N)
// that are linear combinations of the elements in K.

phiN := EulerPhi(N);
printf "Computing the action of the generators of subsub on the Q-vector space of dimension %o.\n",phiN*#kerbasis;
matlist := [];
genlist := SetToSequence(Generators(subsub));
for g in genlist do
  M := ZeroMatrix(Rationals(),phiN*#kerbasis,phiN*#kerbasis);
  for k in [1..#kerbasis] do
    // Compute image of zeta^i*(kth basis vector) under the action of g
    basisvec := act(kerbasis[k],g,N,basislist);
    //printf "Basis vector is %o.\n",[ basisvec[j] : j in [1..dimen]];
    //printf "Attempting to coerce into K.\n";
    kelt := Ker![ basisvec[j] : j in [1..dimen]];
    coords := Coordinates(Ker,kelt);

    det := Integers()!Determinant(g);
    for i in [0..phiN-1] do
      // Write the image of zeta^i*(kth basis vector) to column
      // (i+1) + phiN*k
      fac := Eltseq(zeta^(i*det));
      for j in [0..phiN-1] do
        for m in [1..#kerbasis] do
          entry := coords[m]*fac[j+1];
          M[(m-1)*phiN+(j+1)][i+1 + phiN*(k-1)] := entry;
        end for;
      end for;
    end for;
  end for;
  Append(~matlist,M);
end for;

I := IdentityMatrix(Rationals(),phiN*#kerbasis);
if #matlist eq 0 then
  Append(~matlist,I);
end if;
printf "Finding vectors invariant under subsub.\n";
Ker2 := Kernel(Transpose(matlist[1]-I));
for m in [2..#matlist] do
  Ker2 := Ker2 meet Kernel(Transpose(matlist[m]-I));
end for;
ker2basis := Basis(Ker2);
printf "The dimension is %o.\n",#ker2basis;

// Translate back to the original form

finalbasismat := ZeroMatrix(K,#ker2basis,dimen);
Vsp := VectorSpace(K,dimen);
for n in [1..#ker2basis] do
  vec := Vsp!0;
  for m in [1..phiN*#kerbasis] do
    formnum := Floor((m-1)/phiN) + 1;
    rootnum := m - phiN*(formnum-1) - 1;
    vec := vec + ker2basis[n][m]*zeta^rootnum*(Vsp!kerbasis[formnum]);
  end for;
  finalbasismat[n] := vec;
end for;

// Enumerate the representatives of the right cosets of subsub in covergp 
// sorted by coset of sub in covergp

// S1 and S2 are sets of representatives for the right cosets

S1 := SetToSequence(RightTransversal(Hcover,H));
S2 := SetToSequence(RightTransversal(H,subsub));

bigind := Index(Hcover,subsub);
printf "The index of subsub in covergp is %o.\n",bigind;

cnt := 0;
donegood := false;
mx := 1;
while (donegood eq false) do
  // Create all sequences of non-negative integers of length #ker2basis 
  // that sum to mx
  seqstotry := [ [] ];
  for j in [1..#ker2basis] do
    cur := seqstotry;
    new := [];
    for a in cur do
      if (#a eq 0) then
        maxind := mx;
      else
        maxind := mx - &+a;
      end if;
      for j in [0..maxind] do
        Append(~new,a cat [j]);
      end for; 
    end for;
    seqstotry := new;
  end for;
  donegood2 := false;
  it := 1;
  Reverse(~seqstotry);
  while (donegood2 eq false) do
    seq := seqstotry[it];
    cnt := cnt + 1;
    formtry := &+[ seq[m]*finalbasismat[m] : m in [1..#ker2basis]];
    //printf "We have selected a 'random' element of the Eisenstein subspace.\n";
    imagelist := [];
    images := {};
    for i in [1..#S1] do
      imlist := [];
      for j in [1..#S2] do
        im := act(formtry,S2[j]*S1[i],N,basislist);
        Include(~images,im);
        Append(~imlist,im);
      end for;
      Append(~imagelist,imlist);
    end for;
    printf "Form try attempt %o. Number of images is %o.\n",cnt,#images;
    if cnt eq 156 then
      bad := 0;
      bad2 := 1/bad;
    end if;
    // Test element has #images under covergp.
    if (#images eq bigind) then
      donegood2 := true;
      donegood := true;
      printf "The element %o works. It was number %o.\n",seq,cnt;
    else
      it := it + 1;
      if (it gt #seqstotry) then
        donegood2 := true;
        printf "Incrementing mx. Now mx = %o.\n",mx;	
      end if;
    end if;
  end while;
  if (donegood eq false) and (donegood2 eq true) then
    mx := mx + 1;
  end if;
end while;

// Step 4 - Compute Fourier expansions

printf "Computing Weierstrass p-function Fourier expansions.\n";
xcoords := ZeroMatrix(R,N,N);
for i in [1..#basislist-1] do
  a := basislist[i][1];
  b := basislist[i][2];
  //printf "Computing expansion %o of %o.\n",i,#basislist-1;
  xcoords[a+1][b+1] := weier(a,b,N,prec);
end for;

fourierlist := [];
fouriernum := 0;
for i in [1..#S1] do
  ilist := [];
  for j in [1..#S2] do
    fouriernum := fouriernum + 1;
    printf "Computing Fourier expansion %o.\n",fouriernum;
    fourier := &+[ imagelist[i][j][k]*xcoords[basislist[k][1]+1][basislist[k][2]+1] : k in [1..#basislist-1]];
    Append(~ilist,fourier);
  end for;
  Append(~fourierlist,ilist);
end for;

printf "Symmetrizing.\n";
wt := 0;
formsused := [];
if (subsub eq H) then
  wt := 2;
  formsused := [ fourierlist[i][1] : i in [1..#fourierlist]];
else
  wt := 4;
  termnum := 0;
  for i in [1..#S1] do
    formtouse := R!0;
    maxnum := #S1*#S2*(#S2-1)/2;
    for j in [1..#S2] do
      for j2 in [j+1..#S2] do
        termnum := termnum+1;
        printf "Doing term %o of %o.\n",termnum,maxnum;
        formtouse := formtouse + fourierlist[i][j]*fourierlist[i][j2];
      end for;
    end for;
    Append(~formsused,formtouse);
  end for;
end if;
printf "Done!\n";
chk := #{ formsused[i] : i in [1..#formsused]};
if (chk lt #S1) then
  printf "Error - the number of roots is %o. This is less than %o.\n",chk,#S1;
  printf "Trying again.\n";
  wt := 6;
  formsused := [];
  termnum := 0;
  for i in [1..#S1] do
    formtouse := R!0;
    maxnum := #S1*(#S2)*(#S2-1)*(#S2-2)/6;
    for j in [1..#S2] do
      for j2 in [j+1..#S2] do
        for j3 in [j2+1..#S2] do
          termnum := termnum + 1;
          printf "Doing term %o of %o.\n",termnum,maxnum;
          formtouse := formtouse + fourierlist[i][j]*fourierlist[i][j2]*fourierlist[i][j3];
        end for;
      end for;
    end for;
    Append(~formsused,formtouse);
  end for;
  rechk := #{ formsused[i] : i in [1..#formsused]};
  printf "This time we have %o roots.\n",rechk;
  if (rechk lt #S1) then
    printf "We're still screwed!\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
end if;

effwt := 0;
if (wt eq 6) then
  effwt := 6;
  denomfunc := Eisenstein(6,q : Precision := Ceiling(2*prec/N));
end if;
if (wt eq 4) then
  effwt := 4;
  denomfunc := Eisenstein(4,q : Precision := Ceiling(2*prec/N));
end if;
if (wt eq 2) then
  effwt := 6;
  denomfunc := Eisenstein(6,q : Precision := Ceiling(2*prec/N))/Eisenstein(4,q : Precision := Ceiling(2*prec/N));
end if;

// Step 5 - Compute the minimal polynomial over Q(X(cover)) of
// the modular function formsused[1]/denomfunc.

degbound := Ceiling((effwt*ind)/(12*(ind/indcov)));
S<xxx> := PolynomialRing(R);
poly := S!1;
for i in [1..#S1] do
  poly := poly*(denomfunc*xxx - formsused[i]);
end for;
poly := poly/(denomfunc^Degree(poly));
modf := formsused[1]/denomfunc;

// Step 6 - Now that we have a model, work with it!

coefflist := [];
for m in [0..Degree(poly)-1] do
  printf "Call to ratfunc with m = %o.\n",m;
  ret := ratfuncrep(Coefficient(poly,m),haupt,(Degree(poly)-m)*degbound);
  //printf "Return of ratfunc is %o.\n",ret;
  Append(~coefflist,ret);
  printf "Result has degree %o.\n",Max(Degree(Numerator(ret)),Degree(Denominator(ret)));
end for;
Append(~coefflist,1);
FFF<x> := FunctionField(Rationals());
SSS<y> := PolynomialRing(FFF);
curveeq := &+[ Evaluate(coefflist[i],x)*y^(i-1) : i in [1..#coefflist]];
printf "Curve equation is %o.\n",curveeq;
if not IsIrreducible(curveeq) then
  printf "Error! We didn't get a good primitive element!\n";
  printf "The factorization is %o.\n",Factorization(curveeq);
  bad := 0;
  bad2 := 1/bad;
end if;

// How to work with the model?

// Option 1 - If the genus is 0 and the index is high, don't simplify the
// model but instead find a way to make it line up with a model that
// Sutherland and Zywina already computed.

opttouse := 2;
if (gen eq 0) and (ind/indcov ge 15) then
  opttouse := 1;
end if;

if opttouse eq 1 then
  // Finish everything in here.
  // Need to do this for Elkies curve, and the non-split and split Cartan's mod 7.
  printf "Genus is zero, but degree of cover is very high.\n";
  printf "Using the models already computed by Sutherland and Zywina.\n";
  FFF<t> := FunctionField(Rationals());
  fielddeg := Integers()!(ind/indcov);
  degtry := fielddeg + 1;  
  if l eq "9.27.0.1" then
    desiredratfunc := 3^7*(t^2-1)^3*(t^6+3*t^5+6*t^4+t^3-3*t^2+12*t+16)^3*(2*t^3+3*t^2-3*t-5)/(t^3-3*t-1)^9;
    degtry := 56;
  end if;
  if l eq "7.21.0.1" then
    desiredratfunc := (2*t-1)^3*(t^2-t+2)^3*(2*t^2+5*t+4)^3*(5*t^2+2*t-4)^3/(t^3+2*t^2-t-1)^7;
    degtry := 25;
  end if;
  if l eq "7.28.0.1" then
    desiredratfunc := t*(t+1)^3*(t^2-5*t+1)^3*(t^2-5*t+8)^3*(t^4-5*t^3+8*t^2-7*t+7)^3/(t^3-4*t^2+3*t+1)^7;
  end if;
  // We could just write down an equation that desiredratfunc satisfies
  // and ask Magma to solve that in the function field of the curve.
  // This is not feasible though in cases where the degree is high.
  // We need to first guess the root.
  RRR<xx,yy> := PolynomialRing(Rationals(),2);
  simpleeq := Evaluate(Denominator(desiredratfunc),yy)*xx - Evaluate(Numerator(desiredratfunc),yy);
  denom := LCM([ Denominator(coefflist[i]) : i in [1..#coefflist]]);
  complexeq := &+[ RRR!Evaluate(Numerator(denom*coefflist[i]),xx)*yy^(i-1) : i in [1..#coefflist]];
  // We do this by specializing complexeq at many values of x
  // and computing a root of simpleeq or each such x.
  // Then guessing a rational function based on its values.

  xmax := 2*degtry+2;
  F<a> := PolynomialRing(Rationals());
  xlist := [];
  xval := 1;
  while #xlist lt xmax do
    if IsIrreducible(Evaluate(simpleeq,[xval,a])) then
      Append(~xlist,xval);
    end if;
    xval := xval + 1;
  end while;
  bigmatlst := [ ZeroMatrix(Rationals(),#xlist,2*degtry+2) : j in [1..fielddeg]];
  for i in [1..#xlist] do
    xval := xlist[i];
    printf "Iteration %o of %o.\n",i,#xlist;
    simplespec := Evaluate(simpleeq,[xval,a]);
    complexspec := Evaluate(complexeq,[xval,a]);
    K<w> := NumberField(complexspec);
    printf "Number field root finding.\n";
    timing := Cputime();
    rts := Roots(PolynomialRing(K)!simplespec);
    printf "Done. There were %o roots. Time taken was %o sec.\n",#rts,Cputime(timing);
    elts := Eltseq(rts[1][1]);
    //printf "Value 1 = %o.\n",elts[1];
    for ii in [1..degtry+1] do
      entry1 := xval^(ii-1);
      for j in [1..fielddeg] do
        entry2 := -xval^(ii-1)*elts[j];
        bigmatlst[j][i][ii] := entry1;
        bigmatlst[j][i][ii+degtry+1] := entry2;
      end for;
    end for;
  end for;
  ratfuncs := [];
  for j in [1..fielddeg] do
    printf "Computing null space %o of %o.\n",j,fielddeg;
    NN := NullSpace(Transpose(bigmatlst[j]));
    dim := Dimension(NN);
    v := NN.1;
    num := &+[ v[i]*t^(i-1) : i in [1..degtry+1]];
    denom := &+[ v[degtry+1+i]*t^(i-1) : i in [1..degtry+1]];
    Append(~ratfuncs,num/denom);
    printf "ratfuncs %o of %o. Has degree %o.\n",j,fielddeg,Degree(num/denom);
  end for;
  printf "Testing.\n";
  xval := xval + 1;
  simplespec := Evaluate(simpleeq,[xval,a]);
  complexspec := Evaluate(complexeq,[xval,a]);
  K<w> := NumberField(complexspec);
  printf "Number field root finding.\n";
  timing := Cputime();
  rts := Roots(PolynomialRing(K)!simplespec);
  printf "Done. There were %o roots. Time taken was %o sec.\n",#rts,Cputime(timing);
  elts := Eltseq(rts[1][1]);
  shouldbe := [ Evaluate(ratfuncs[i],xval) : i in [1..fielddeg]];
  if elts eq shouldbe then
    printf "Testing worked!\n";
  else
    printf "Fail!\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
  // Do the computation to check that the root works.
  SSS<xxx> := PolynomialRing(FFF);
  ffpol := Evaluate(complexeq,[t,xxx]);
  AA<www> := FunctionField(ffpol);
  rootcheck := &+[ Evaluate(ratfuncs[i],t)*www^(i-1) : i in [1..#ratfuncs]];
  printf "Doing computation to verify root.\n";
  verify := Evaluate(Numerator(desiredratfunc),rootcheck) - t*Evaluate(Denominator(desiredratfunc),rootcheck);
  if (verify eq 0) then
    printf "Root verification complete.\n";
  else
    printf "Root verification failed!!!\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
  newhaupt := &+[ Evaluate(ratfuncs[i],haupt)*modf^(i-1) : i in [1..#ratfuncs]];
  // Now do file writing.
  fileout := "modfunc" cat l cat ".txt";
  printf "Writing Fourier expansion of generator to file.\n";
  System("rm " cat fileout);
  KK<z> := CyclotomicField(N);
  RRRRR<qq> := PuiseuxSeriesRing(KK);
  PrintFile(fileout,Sprintf("KK<z> := CyclotomicField(%o);\n",N));
  PrintFile(fileout,"RRRRR<qq> := PuiseuxSeriesRing(KK);");
  expdenom := ExponentDenominator(newhaupt);
  bestexpdenom := LCM([ Denominator(a/expdenom) : a in [expdenom*Valuation(newhaupt)..expdenom*AbsolutePrecision(newhaupt)-1] | Coefficient(newhaupt,a/expdenom) ne 0]);
  endprec := Floor(bestexpdenom*AbsolutePrecision(newhaupt))/bestexpdenom;
  reparsedhaupt := BigO(qq^endprec);
  for m in [bestexpdenom*Valuation(newhaupt)..bestexpdenom*endprec-1] do
    cof := KK!Eltseq(Coefficient(newhaupt,m/bestexpdenom));
    reparsedhaupt := reparsedhaupt + cof*qq^(m/bestexpdenom);
  end for;
  PrintFile(fileout,"haupt := ");
  PrintFileMagma(fileout,reparsedhaupt);
  PrintFile(fileout,";");
  PrintFile(fileout,"return haupt;");
  printf "Fourier expansion of hauptmodul written to %o. Done with model computation.\n",fileout;
  printf "Verified the pre-computed covering due to Sutherland and Zywina.\n";
  FFFF<x> := FunctionField(Rationals());
  printf "The map is j = %o.\n",FFFF!desiredratfunc;
  // Write model to file
  modelfilename := "model" cat l cat ".txt";
  System("rm " cat modelfilename);
  PrintFile(modelfilename,"X := ProjectiveSpace(Rationals(),1);");
  PrintFile(modelfilename,"return X;");
  // Write covering map
  mapfilename := l cat "map" cat coverlabel cat ".txt";
  System("rm " cat mapfilename);
  lsplit := Split(l,".");
  coversplit := Split(coverlabel,".");
  PrintFile(mapfilename,"x := DD.1;");
  PrintFile(mapfilename,"z := DD.2;");
  mapname := "map" cat Sprintf("%o_%o_%o_%oto%o_%o_%o_%o",lsplit[1],lsplit[2],lsplit[3],lsplit[4],coversplit[1],coversplit[2],coversplit[3],coversplit[4]);
  // Determine numerator and denominator polynomials
  QQQQ<x,z> := PolynomialRing(Rationals(),2);
  newratfunc := desiredratfunc;
  deg := Max(Degree(Numerator(newratfunc)),Degree(Denominator(newratfunc)));
  cofs := Coefficients(Numerator(newratfunc));
  numpoly := &+[ cofs[i]*x^(i-1)*z^(deg-i+1) : i in [1..#cofs]];
  cofs := Coefficients(Denominator(newratfunc));
  denompoly := &+[ cofs[i]*x^(i-1)*z^(deg-i+1) : i in [1..#cofs]];
PrintFile(mapfilename,mapname cat Sprintf(" := map<DD -> CC | [%o,%o]>;",numpoly,denompoly));
  PrintFile(mapfilename,"return " cat mapname cat ";");
  quit;
end if;

// Option 2 - If the genus is > 0 or the index isn't too high, simplify
// the model using van Hoeij and Novocin's "A Reduction Algorithm for Algebraic Function Fields"

K := FunctionField(curveeq);
n := Degree(K);

printf "Finding maximal order finite in function field extension. This may take a while.\n";
motime := Cputime();
SetVerbose("MaximalOrder",1);
// Step 1 - Find a basis for OK
OK := MaximalOrderFinite(K);
printf "Time taken was %o.\n",Cputime(motime);
SetVerbose("MaximalOrder",0);
basis1 := [ OK.i : i in [1..n]];
basis1mat := Matrix(FFF,[ Eltseq(K!OK.i) : i in [1..n]]);
// Step 2 - Find a basis for Oinfinity
OK2 := MaximalOrderInfinite(K);
basis2 := [ OK2.i : i in [1..Degree(K)]];
basis2mat := Matrix(FFF,[ Eltseq(K!OK2.i) : i in [1..n]]);
// Step 3 - Write each element of OK as an LC of elements in OK2.
changemat := basis1mat*basis2mat^(-1);
// Step 4 - Let D be the LCM of the denominators of the entries in changemat.
D := LCM([ Denominator(d) : d in Eltseq(changemat)]);
alist := [[Numerator(D*changemat[i][j]) : j in [1..n]] : i in [1..n]];

curb := basis1;
done := false;
it := 0;
while done eq false do
  it := it + 1;
  printf "Iteration %o.\n",it;
  // Step 5 - Compute max degrees and vectors
  vmat := ZeroMatrix(Rationals(),n,n);
  mlist := [];
  dlist := [];
  for i in [1..Degree(K)] do
    mi := Max([ Degree(a) : a in alist[i]]);
    for j in [1..Degree(K)] do
      vmat[i][j] := Coefficient(alist[i][j],mi);
    end for;
    di := mi - Degree(D);
    Append(~dlist,di);
    Append(~mlist,mi);
  end for;
  printf "mlist = %o.\n",mlist;
  // Step 6 - Test linear independence.
  rkv := Rank(vmat);
  if (rkv eq n) then
    done := true;
  else
    c := Basis(NullSpace(vmat))[1];
    // Step 7 - Update
    maxdi := Max([ dlist[i] : i in [1..#dlist] | c[i] ne 0]);
    ind := 0;
    for i in [1..n] do
      if dlist[i] eq maxdi then
        if c[i] ne 0 then
	  ind := i;
	end if;
      end if;
    end for;
    printf "Updating...\n";
    newb := &+[ c[k]*x^(dlist[ind]-dlist[k])*curb[k] : k in [1..n]];
    curb[ind] := newb;    
    for j in [1..n] do
      newa := &+[ c[k]*x^(dlist[ind]-dlist[k])*alist[k][j] : k in [1..n]];
      alist[ind][j] := newa;
    end for;
    printf "Done.\n";
  end if;
end while;

dtouse := Max(dlist);
base := [];
for i in [1..#dlist] do
  for l in [0..dtouse-dlist[i]] do
    Append(~base,x^l*curb[i]);
  end for;
end for;
printf "Working with basis of size %o.\n",#base;
printf "Simplest element defining the field has index %o.\n",dtouse-dlist[1]+2;

tvals := [];
starval := -2;
done := false;
while done eq false do
  if &and [ Evaluate(Denominator(coefflist[i]),starval) ne 0 : i in [1..#coefflist]] then
    spec := &+[ Evaluate(coefflist[i],starval)*y^(i-1) : i in [1..#coefflist]];
    if IsIrreducible(spec) then
      Append(~tvals,starval);
    end if;
    starval := starval + 1;
    if #tvals eq 7 then
    // Using 7 points seems to work fairly well. I don't know if it always will work.  
      done := true;
    end if;
  else
    starval := starval + 1;
  end if;
end while;
printf "Using tvals = %o.\n",tvals;

// Manually building specializations.
RR<tt> := PolynomialRing(Rationals());

imagemat := ZeroMatrix(Rationals(),#base,#tvals*n);
resfields := [];
specvallists := <>;
for k in [1..#tvals] do
  spec := &+[ Evaluate(coefflist[i],tvals[k])*tt^(i-1) : i in [1..#coefflist]]; 
  resfield := NumberField(spec);
  specvals := [];
  printf "Computing specialization %o of %o.\n",k,#tvals;
  for i in [1..#base] do
    elt := base[i];
    ee := Eltseq(elt);
    specbasei := &+[ Evaluate(ee[j],tvals[k])*resfield.1^(j-1) : j in [1..Degree(resfield)]];
    Append(~specvals,specbasei);
  end for;
  Append(~specvallists,specvals);
  Append(~resfields,resfield);
  printf "Computing LLLed maximal order.\n";
  OKK := LLL(MaximalOrder(resfield));
  OKmat := Matrix(Rationals(),[Eltseq(resfield!OKK.i) : i in [1..n]]);
  for i in [1..#base] do
    im := Vector(Eltseq(specvals[i]))*OKmat^(-1);
    for j in [1..n] do
      imagemat[i][(k-1)*n+j] := im[j];
    end for;
  end for;
end for;

// Find the elements in the Q-span of base that land in O_K_i
// for each i with 1 <= i <= #tvals

printf "Clearing denominators.\n";
for i in [1..#base] do
  denom := LCM([ Denominator(e) : e in Eltseq(imagemat[i])]);
  base[i] := base[i]*denom;
  for k in [1..#tvals] do
    specvallists[k][i] := specvallists[k][i]*denom;
  end for;
  for j in [1..#tvals*n] do
    imagemat[i][j] := imagemat[i][j]*denom;
  end for;
end for;
printf "Saturating.\n";
sat := Saturation(ChangeRing(imagemat,Integers()));
chk, X := IsConsistent(imagemat,ChangeRing(sat,Rationals()));
printf "LLLing. (Just for fun. It's not real yet.)\n";
L2, X2 := LLL(sat);
changemat := ChangeRing(X2,Rationals())*X;
newbase := [];
printf "Changing coordinates.\n";
newbasespecs := < [ resfields[j]!0 : i in [1..#base]] : j in [1..#tvals]>;
for i in [1..#base] do
  newbase[i] := &+[ changemat[i][j]*base[j] : j in [1..#base]];
  for k in [1..#tvals] do
    specik := &+[ changemat[i][j]*specvallists[k][j] : j in [1..#base]];
    newbasespecs[k][i] := specik;
  end for;
end for;

// The elements of newbase should be ``pretty good''. Let's see if
// we can make them better.

RRR := RealField(167);
SetDefaultRealField(RRR);
newlat := ZeroMatrix(RRR,#base,#tvals*n);
for k in [1..#tvals] do
  r, s := Signature(resfields[k]);
  for i in [1..#base] do
    vec := ZeroMatrix(RRR,1,n);
    elts := Conjugates(newbasespecs[k][i]);
    for l in [1..r] do
      vec[1][l] := Real(elts[l]);
    end for;
    for l in [1..s] do
      vec[1][r+2*l-1] := Real(elts[r+2*l-1]);
      vec[1][r+2*l] := Imaginary(elts[r+2*l]);
    end for;
    for l in [1..n] do
      newlat[i][(k-1)*n+l] := vec[1][l];
    end for;
  end for;
end for;
L3, X3 := LLL(newlat);
newerbase := [];
printf "Changing coordinates.\n";
for i in [1..#base] do
  newerbase[i] := &+[ X3[i][j]*newbase[j] : j in [1..#base]];
  newerbase[i] := newerbase[i] - Trace(newerbase[i])/Degree(K);  
end for;
minpolys := [ MinimalPolynomial(newerbase[i]) : i in [1..#newerbase]];
rightdeg := [ j : j in [1..#base] | Degree(minpolys[j]) eq Degree(K) ];
sizes := [ #Sprintf("%o",minpolys[j]) : j in rightdeg];
minsize, rightdegind := Min(sizes);
modelind := rightdeg[rightdegind];
printf "Minimal size model has %o characters. Index is %o.\n",minsize,modelind;
niceplane := minpolys[modelind];
printf "Simplified equation is %o.\n",niceplane;
printf "In this equation, Q(x) is the function field of the modular curve with label %o.\n",coverlabel;
printf "And Q(x,y) is the function field of the modular curve with label %o.\n",l;

// If gen ge 1, model is in P^2. Write to file.
if (gen ge 1) then
  QQQQ<x,y> := PolynomialRing(Rationals(),2);
  newpoly := eval Sprintf("%o",niceplane);
  C := ProjectiveClosure(Curve(AffineSpace(Rationals(),2),newpoly));
  // Write model to file
  modelfilename := "model" cat l cat ".txt";
  System("rm " cat modelfilename);
P2<X,Y,Z> := ProjectiveSpace(Rationals(),2);
  PrintFile(modelfilename,"P2<X,Y,Z> := ProjectiveSpace(Rationals(),2);");
  PrintFile(modelfilename,Sprintf("X := Curve(P2,[ %o ]);",Evaluate(DefiningPolynomial(C),[X,Y,Z])));
  PrintFile(modelfilename,"return X;");
  // Write covering map
  mapfilename := l cat "map" cat coverlabel cat ".txt";
  System("rm " cat mapfilename);
  lsplit := Split(l,".");
  coversplit := Split(coverlabel,".");
  PrintFile(mapfilename,"x := DD.1;");
  PrintFile(mapfilename,"y := DD.2;");
  PrintFile(mapfilename,"z := DD.3;");
mapname := "map" cat Sprintf("%o_%o_%o_%oto%o_%o_%o_%o",lsplit[1],lsplit[2],lsplit[3],lsplit[4],coversplit[1],coversplit[2],coversplit[3],coversplit[4]); 
  PrintFile(mapfilename,mapname cat " := map<DD -> CC | [x,z]>;");
  PrintFile(mapfilename,"return " cat mapname cat ";");
  quit;
end if;

if (gen eq 0) then
  // Then we're not done, and we need to make it isomorphic to P^1.
  // There are two ways to handle this. But first, we compute the Fourier
  // expansion of the parameter y in the equation above.
  ffelt := Eltseq(newerbase[modelind]);
  yfourier := &+[ Evaluate(ffelt[i],haupt)*modf^(i-1) : i in [1..#ffelt]];

  // Way 1 - see if all the coefficients of niceplane are linear.
  cofs := [ Coefficient(niceplane,i) : i in [0..Degree(niceplane)]];
  if &and [ Degree(Denominator(cofs[i])) eq 0 : i in [1..#cofs]] and (&and [ Degree(Numerator(cofs[i])) le 1 : i in [1..#cofs]]) then
    // We can take the simplified equation and solve for x in terms of y.
    cofs2 := [ Evaluate(Numerator(cofs[i]),tt) : i in [1..#cofs]];
    num := &+[ Coefficient(cofs2[i],0)*x^(i-1) : i in [1..#cofs]];
    denom := &+[ Coefficient(cofs2[i],1)*x^(i-1) : i in [1..#cofs]];
    param := -num/denom;
    uniformize := yfourier;
    initratfunc := param;
    printf "Initial covering map is %o.\n",initratfunc;
  else
  // Way 2 - Use Magma to parametrize the genus zero curve.
    R<xxxx,yyyy> := PolynomialRing(Rationals(),2);
    cofs := [ Numerator(Coefficient(niceplane,i)) : i in [0..Degree(niceplane)]];
    newcurveeq := &+[ Evaluate(cofs[i],xxxx)*yyyy^(i-1) : i in [1..Degree(niceplane)+1]];
    C := ProjectiveClosure(Curve(AffineSpace(Rationals(),2),newcurveeq));
    bound := 10;
    found := false;
    while found eq false do
      printf "Searching for a non-singular rational point with bound %o.\n",bound;
      plist := PointSearch(C,bound);
      it := 1;
      done := false;
      while done eq false do
        pt := plist[it];
        if not IsSingular(C!pt) then
          P := C!pt;
          done := true;
          found := true;
        else
          it := it + 1;
        end if;
        if (it gt #plist) then
          done := true;
          bound := bound*2;
        end if;
      end while;
      if bound gt 60000 then
        printf "No point found. Giving up.\n";
        bad := 0;
        bad2 := 1/bad;
      end if;
    end while;
    printf "Parametrizing the curve.\n";
    A := Parametrization(C,P);
    printf "Found it!\n";
    xparam := A([x,1])[1];
    yparam := A([x,1])[2];
    printf "We have X = %o.\n",xparam;
    printf "We have Y = %o.\n",yparam;
    // Build a polynomial ring over FF, the rational function field.
    RRRR<xx> := PolynomialRing(FF);
    SSSS<yy> := FunctionField(Evaluate(newcurveeq,[tt,xx]));
    TTTT<zz> := PolynomialRing(SSSS);
    num := Numerator(yparam);
    denom := Denominator(yparam);
    uniformpoly := Evaluate(denom,zz)*yy - Evaluate(num,zz);
    unifunc := Roots(uniformpoly)[1][1];
    seqlist := ElementToSequence(unifunc);
    truncprec := Ceiling(AbsolutePrecision(modf)+20);
    printf "Computing uniformizer coefficients.\n";
    coefflist := [ Evaluate(seqlist[i],haupt+BigO(q^truncprec)) : i in [1..#seqlist]];
    printf "Computing uniformizer...\n";
    uniformize := &+[ coefflist[i]*yfourier^(i-1) : i in [1..#seqlist]];
    newpoly := MinimalPolynomial(unifunc);
    denom := LCM([Denominator(Coefficient(newpoly,i)) : i in [0..Degree(newpoly)]]);
    newpoly2 := &+[ Evaluate(RR!(denom*Coefficient(newpoly,i)),yyyy)*xxxx^i : i in [0..Degree(newpoly)]];
    if not Degree(newpoly2,yyyy) eq 1 then
      printf "Something is wrong! We don't have a uniformizer!\n";
      printf "The polynomial is %o.\n",newpoly2;
      bad := 0;
      bad2 := 1/bad;
    end if;
    cofs := Coefficients(newpoly2,yyyy);
    initratfunc := -Evaluate(cofs[1],[tt,0])/Evaluate(cofs[2],[tt,0]);
    printf "Initial covering map is %o.\n",initratfunc;
  end if;
  // Now we need to simplify.
  newratfunc, M := supersimplify(initratfunc);
  printf "The final model is y = %o.\n",newratfunc;
  printf "Here Q(y) is the function field of %o, and Q(x) is the
function field of %o.\n",l,coverlabel;
  //printf "M = %o.\n",M;
  M := ChangeRing(M,Rationals());
  M := M^(-1);
  newhaupt := (M[1][1]*uniformize + M[1][2])/(M[2][1]*uniformize + M[2][2]);
  // And write the Fourier expansion to a file.
  fileout := "modfunc" cat l cat ".txt";
  //printf "Writing Fourier expansion of generator to file.\n";
  System("rm " cat fileout);
  KK<z> := CyclotomicField(N);
  RRRRR<qq> := PuiseuxSeriesRing(KK);
  PrintFile(fileout,Sprintf("KK<z> := CyclotomicField(%o);\n",N));
  PrintFile(fileout,"RRRRR<qq> := PuiseuxSeriesRing(KK);");
  expdenom := ExponentDenominator(newhaupt);
  bestexpdenom := LCM([ Denominator(a/expdenom) : a in [expdenom*Valuation(newhaupt)..expdenom*AbsolutePrecision(newhaupt)-1] | Coefficient(newhaupt,a/expdenom) ne 0]);
  endprec := Floor(bestexpdenom*AbsolutePrecision(newhaupt))/bestexpdenom;
  reparsedhaupt := BigO(qq^endprec);
  for m in [bestexpdenom*Valuation(newhaupt)..bestexpdenom*endprec-1] do
    cof := KK!Eltseq(Coefficient(newhaupt,m/bestexpdenom));
    reparsedhaupt := reparsedhaupt + cof*qq^(m/bestexpdenom);
  end for;
  PrintFile(fileout,"haupt := ");
  PrintFileMagma(fileout,reparsedhaupt);
  PrintFile(fileout,";");
  PrintFile(fileout,"return haupt;");
  printf "Fourier expansion of hauptmodul written to %o. Done with model computation.\n",fileout;
// Write model to file
  // Write model to file
  modelfilename := "model" cat l cat ".txt";
  System("rm " cat modelfilename);
  PrintFile(modelfilename,"X := ProjectiveSpace(Rationals(),1);");
  PrintFile(modelfilename,"return X;");
  // Write covering map
  mapfilename := l cat "map" cat coverlabel cat ".txt";
  System("rm " cat mapfilename);
  lsplit := Split(l,".");
  coversplit := Split(coverlabel,".");
  PrintFile(mapfilename,"x := DD.1;");
  PrintFile(mapfilename,"z := DD.2;");
  mapname := "map" cat Sprintf("%o_%o_%o_%oto%o_%o_%o_%o",lsplit[1],lsplit[2],lsplit[3],lsplit[4],coversplit[1],coversplit[2],coversplit[3],coversplit[4]);
  // Determine numerator and denominator polynomials
  QQQQ<x,z> := PolynomialRing(Rationals(),2);
  deg := Max(Degree(Numerator(newratfunc)),Degree(Denominator(newratfunc)));
  cofs := Coefficients(Numerator(newratfunc));
  numpoly := &+[ cofs[i]*x^(i-1)*z^(deg-i+1) : i in [1..#cofs]];
  cofs := Coefficients(Denominator(newratfunc));
  denompoly := &+[ cofs[i]*x^(i-1)*z^(deg-i+1) : i in [1..#cofs]];
  PrintFile(mapfilename,mapname cat Sprintf(" := map<DD -> CC | [%o,%o]>;",numpoly,denompoly));
  PrintFile(mapfilename,"return " cat mapname cat ";");
  quit;  
end if;  
