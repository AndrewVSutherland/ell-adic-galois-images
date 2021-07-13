// This Magma script does clever point searching on X_ns^+(l^k)
// for l >= 3 a prime and k >= 1.

Attach("../groups/gl2.m");
load "../groups/gl2data.m";

l := 3;
k := 2;
N := l^k;
bound := 10^9;

// For N = 9
// 10^10 - 638.460 seconds.
// 10^9 - 98.269 seconds.
// 10^8 - 20.820 seconds.
// 10^7 - 7.730 seconds.
// 10^6 - 5.599 seconds.
// For N = 5
// 10^6 - 12.449 seconds.
// 2*10^7 - 158.62 seconds. This is high enough to find two non-integral
// j-invariants
// For N = 19
// 10^6 - 6.44 seconds.
// 10^7 - 14.570 seconds.
// 10^8 - 63.289 seconds.
// 10^9 - 360.319 seconds.


G := GL2NormalizerNonsplitCartan(N);
CC := ConjugacyClasses(G);

// Key ideas:

// 1. For each prime p not dividing l, determine the elliptic curves
// E/F_p which have the property that their Frobenius is conjugate to
// an element of the subgroup N_ns^+(l^k).

// 2. If j(E) has denominator that's a multiple of p and p is not equal to l,
// then E has multiplicative reduction at p, and so E reduces to a cusp of
// X_ns^+(l^k). But the cusps are a single Galois orbit of size
// (l^(k-1))(l-1)/2. This can be seen from the double coset description
// of the cusps and amounts to knowing for which e a product of an element
// of a non-split Cartan normalizer and a unipotent matrix can
// have an eigenvalue of 1 and an eigenvalue of e.
// This implies that p = +- 1 (mod l^k).

// 3. If j(E) has a denominator that's a multiple of p then E has
// split multiplicative reduction over an at most quadratic extension of Q_p.
// The proof of Proposition V.6.1 of Silverman's ATAEC shows that
// ord_p(j(E)) is a multiple of l^k. (Note that this argument breaks if l = 2
// and the result is false in that case.)

printf "Point search bound = %o.\n",bound;

// Determine possible denominators. There aren't very many!
// For l = 3, k = 2 and bound = 10^24, there are 49 possible.
printf "Determining denominators.\n";
primfacs := [ p : p in [2..Floor(bound^(1/N))] | IsPrime(p) and ((p eq l) or (p mod N eq 1) or (p mod N eq (N-1)))];
if #primfacs eq 0 then
  prd := [ 1 ];
else
  prd := &*[ p : p in primfacs ];
end if;
denomlist := [];
for r in [0..Floor((bound^(1/N)-1)/N)] do
  k := N*r + 1;
  bad := false;
  done := false;
  it := 1;
  kdiv := k;
  while (done eq false) do
    if (it gt #primfacs) then
      done := true;
      if (kdiv ne 1) then
        bad := true;
      end if;
    else      
      vl := Valuation(kdiv,primfacs[it]);
      kdiv := kdiv/primfacs[it]^vl;
      if (kdiv eq 1) then
       done := true;
      else
        it := it + 1;
      end if;
    end if;
  end while;
  if (bad eq false) then
    // What's the maximum power of l^N we can multiply by and be under the bound?
    maxexp := Floor((Log(bound)-N*Log(k))/(Log(l)*N));
    for s in [0..maxexp] do
      Append(~denomlist,k^N*l^(N*s));
    end for;
  end if;  
end for;
for r in [1..Floor((bound^(1/N)+1)/N)] do
  k := N*r - 1;
  bad := false;
  done := false;
  it := 1;
  kdiv := k;
  while (done eq false) do
    if (it gt #primfacs) then
      done := true;
      if (kdiv ne 1) then
        bad := true;
      end if;
    else      
      vl := Valuation(kdiv,primfacs[it]);
      kdiv := kdiv/primfacs[it]^vl;
      if (kdiv eq 1) then
       done := true;
      else
        it := it + 1;
      end if;
    end if;
  end while;
  if (bad eq false) then
    // What's the maximum power of l^N we can multiply by and be under the bound?
    maxexp := Floor((Log(bound)-N*Log(k))/(Log(l)*N));
    for s in [0..maxexp] do
      Append(~denomlist,k^N*l^(N*s));
    end for;
  end if;  
end for;
Sort(~denomlist);

// Now, let's sieve.
prims := [];
done := false;
curp := 2;
// skip 2
prd := 1;
while (done eq false) do
 curp := NextPrime(curp);
 if (curp ne l) then
   prd := prd*curp;
   Append(~prims,curp);
   if prd gt (10*bound) then
     done := true;
   end if;
 end if;
end while;
maxprim := prims[#prims];

// Slow Frobenius matrix computer
function FrobeniusMatrix(E)
/*  Input is an elliptic curve E defined over F_p.
     The output is a matrix A in M(2,Z) so that for any integer N>1
relatively prime to p,
     the action of Frob_p on E[N] corresponds, with respect to some
choice of basis, to A modulo N.
*/
     Fp:=BaseRing(E);
     q:=#Fp;// assert IsPrime(q); // extension fields not supported
     a:=TraceOfFrobenius(E);
     j:=jInvariant(E);

     Delta :=a^2-4*q;
     Delta0:=FundamentalDiscriminant(Delta);
     _,f:=IsSquare(Delta div Delta0);

     for v in Sort(Divisors(f)) do
        D:=Delta0*v^2;
        if Evaluate(HilbertClassPolynomial(D),j) eq 0 then
           b:=f div v;
           return [(a-(Delta div b)) div 2, ((Delta div b)*(1- Delta div
b^2)) div 4, b, (a+(Delta div b)) div 2],a,b;
        end if;
     end for;
end function;

// Given an odd prime p,
// find a quadratic non-residue mod p.

function nonres(p)
  it := 2;
  ret := it;
  done := false;
  while (done eq false) do
    if LegendreSymbol(it,p) eq -1 then
      ret := it;
      done := true;
    else
      it := it + 1;
    end if;
  end while;
  return ret;
end function;

GG := GL(2,Integers(N));
CM := ClassMap(GG);
NSclasses := [ CM(GG!CC[i][3]) : i in [1..#CC]];

p := 2;
done := false;
onestouse := [];
prd := 1;
data := [];
while done eq false do
  p := NextPrime(p);
  if (p eq l) then
    p := NextPrime(p);
  end if;
  if (p ge 200) then
    done := true;
  else
    printf "Testing p = %o.\n",p;
    F := GF(p);
    nonsqr := nonres(p);
    goodj := [];
    for j in [1..p-1] do
      added := false;
      if (j ne (1728 mod p)) then
        E := EllipticCurveWithjInvariant(F!j);
        FM := GG!FrobeniusMatrix(E);
        if CM(FM) in NSclasses then
          Append(~goodj,j);
        end if;
      end if;
    end for;
    // Assume j = 0 and j = 1728 are points on X_ns^+(l^k) mod p.
    /*
    j0 := j0Points(N,f,p);
    if (j0 ge 1) then
      Append(~goodj,0);
    end if;
    if (p gt 3) then
      j1728 := j1728Points(N,f,p);
      if (j1728 ge 1) then
        Append(~goodj,1728);
      end if;
    end if;
    */
    Append(~goodj,0);
    if (p ge 5) then
      Append(~goodj,1728 mod p);
    end if;  
    Sort(~goodj);
    happy := (#goodj/p);
    printf "The fraction of good j's is %o.\n",RealField(5)!happy;
    if (#goodj gt #Set(goodj)) then
      printf "Error at p = %o.\n",p;
    end if;
    Append(~data,<p,goodj>);
  end if;  
end while;

uppbound := 10*bound;

printf "Enumerating subsets.\n";

primelist := [ <data[i][1],Log(#data[i][2]/data[i][1])/Log(data[i][1])> : i in [1..#data]];
compfunc := func<x,y | x[2]-y[2]>;
Sort(~primelist,compfunc);

done := false;
// Determine the best primes to use
nm := 0;
curprd := 1;
it := 1;
while (done eq false) do
  curprd := curprd*primelist[it][1];
  if (curprd gt uppbound) then
    done := true;
  else
    it := it + 1;
  end if;
end while;
// So it is the size.
printf "Searching for subsets of size at most %o using good primes.\n",it+4;
goodps := {};
itt := 1;
while #goodps le (it+4) do
  if &and [ GCD(primelist[itt][1],primfacs[j]) eq 1 : j in [1..#primfacs]] then
    Include(~goodps,primelist[itt][1]);
  end if;
  itt := itt + 1;
end while;
goodsets := [];
goodsetclassnum := [];
for s in Subsets(goodps) do
  curprod := &*s;
  if (curprod gt 2*bound) and (curprod lt uppbound) then
    Append(~goodsets,s);
    Append(~goodsetclassnum,&*[ #data[i][2] : i in [1..#data] | data[i][1] in s]);
  end if;
end for;
printf "There were %o good subsets found.\n",#goodsets;
mn, goodind := Min(goodsetclassnum);
printf "The minimal number of classes was %o.\n",Min(goodsetclassnum);
chosenset := goodsets[goodind];
printf "Chosen subset is %o.\n",chosenset;

// Now do some CRTing
printf "Starting CRTing.\n";
prd := &*chosenset;
possible := {};
onestouse := [];
for i in [1..#data] do
  if data[i][1] in chosenset then
    Append(~onestouse,data[i]);
  end if;
end for;
plist := [ onestouse[i][1] : i in [1..#onestouse]];
cnt := 0;
R := Integers(prd);
cp := CartesianProduct([ onestouse[i][2] : i in [1..#onestouse]]);
siz := #cp;
for s in cp do
  cnt := cnt + 1;
  if (cnt mod 100000 eq 0) then
    printf "Done %o of %o. Number possible so far is %o.\n",cnt,siz,#possible;
  end if;
  jval := CRT([ s[i] : i in [1..#onestouse]],plist);
  for d in denomlist do
    if GCD(jval,d) eq 1 then
      num1 := Integers()!(R!(jval*d));
      num2 := Integers()!(R!(jval*d))-prd;
      if AbsoluteValue(num1) le bound then
        Include(~possible,Rationals()!(num1/d));
      end if;
      if AbsoluteValue(num2) le bound then
        Include(~possible,Rationals()!(num2/d));
      end if;
    end if;  
  end for;
end for;
possible := SetToSequence(possible);
printf "We found %o possible j-invariants. Doing further testing.\n",#possible;
tested := [];
for ii in [1..#possible] do
  if (ii mod 100000 eq 0) then
    printf "Tested %o.\n",ii;
  end if;
  jj := possible[ii];
  bad := false;
  it := 1;
  done := false;
  while (done eq false) do
    if GCD(Denominator(jj),data[it][1]) eq 1 then
      red := Integers()!(GF(data[it][1])!jj);
      if not red in data[it][2] then
        bad := true;
	done := true;
      end if;
    end if;
    if (done eq false) then
      it := it + 1;
      if (it gt #data) then
        done := true;
      end if;
    end if;
  end while;
  if (bad eq false) then
    Append(~tested,jj);
  end if;
end for;
printf "Of those %o pass the test.\n",#tested;

// Compile nonres*squares mod N.
nonsqrs := { Integers(N)!(nonres(l)*x^2) : x in [0..N-1]};

// Further testing
goodjs := [];
bound2 := 1000;
printf "Testing remaining j's up to %o.\n",bound2;
for i in [1..#tested] do
  jj := tested[i];
  E := MinimalTwist(EllipticCurveWithjInvariant(jj));
  if (i mod 1000 eq 0) then
    printf "Working on number %o.\n",i;
  end if;
  p := plist[#plist];
  done := false;
  good := true;
  while (p lt bound2) and (done eq false) do
    p := NextPrime(p);
    if (GCD(p,l*Conductor(E)) eq 1) then
      tr := TraceOfFrobenius(E,p);
      if (tr mod N ne 0) then
        elt := tr^2 - 4*p;
        if not (elt in nonsqrs) then
          done := true;
          good := false;
        end if;
      end if;
    end if;
  end while;
  if (good eq true) then
    Append(~goodjs,jj);
  end if;
end for;
printf "There are %o j's that pass the test.\n",#goodjs;
printf "They are %o.\n",goodjs;

