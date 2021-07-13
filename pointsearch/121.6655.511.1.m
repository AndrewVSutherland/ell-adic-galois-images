// Mordell-Weil sieve for X_ns^+(121).

// It takes about 6400 seconds to verify that there is no k with
// |k| <= lcm(1,2,...,233) so that k*P is the image on X_ns^+(11) of a rational point
// on X_ns^+(121).
// This implies that if Q is a non-CM point on X_ns^+(121), then
// j(Q) has height > about 10^(10^200). 

t0 := Cputime();
Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subs := GL2Load("../groups/gl2_11adic.txt");
G := subs["121.6655.511.1"]`subgroup;
CC := ConjugacyClasses(G);
pairs := { <Trace(CC[i][3]),Determinant(CC[i][3])> : i in [1..#CC]};
// 92% of the <trace,det> pairs for X_ns^+(11) are in X_ns^+(121).

EE := EllipticCurve([0,-1,1,-7,10]);
P1 := ProjectiveSpace(Rationals(),1);
// Use the model compute by Chen and Cummins in Math. Comp.
// j((X,Y)) = (B + CY)/A
R<X> := PolynomialRing(Rationals());
A := (X^5 - 119*X^4 + 1381*X^3 - 2642*X^2 - 9313*X + 19249)^11;
B :=
(-98387520*X^54 - 220438794499*X^53 - 53420217837899*X^52+
6338048458979853*X^51 + 71475058557035848*X^50-
44291597887311980733*X^49 + 3242711585656502142337*X^48-
123595289334495611502045*X^47+ 2465220203610361958991252*X^46+
4714178266732077504326779*X^45- 2230431303801367431478586543*X^44+
92332146130690688142517974663*X^43-
2507289782484853611270309175397*X^42+
53359697809475207245060557363937*X^41-
942047948418627104106931499116639*X^40+
14114007315932826893573283384330808*X^39-
183690447317522366668854840197651161*X^38+
2171510861410311795157039184686867406*X^37-
24911038397772665326423913919305711163*X^36+
291169675293150416804617731761995291067*X^35-
3415529427584012398564140280662798038067*X^34+
37855207962015462701067289499903775336771*X^33-
374992775331213422799775513202374746471447*X^32+
3207001025188524833125521692358292634027949*X^31-
23141471939301096287187426104081929791336253*X^30+
137360034469063724618182923106280369775169352*X^29-
638617861348315025223322860571024211741905470*X^28+
2013006888766112251485827113833063752292822797*X^27-
1166820457630183374266235764879683724824730753*X^26-
35448755737371974992340224606099228330400359378*X^25+
281145492835905205314154378132072415664685281266*X^24-
1275116642123942750922015094862993429873903104392*X^23+
3568711769977516712360325915844869782908014276967*X^22-
2726507178866477380574048143644325194320130884262*X^21 -
31447406024550699683476578355464224641763394892606*X^20
+ 197361861608467000470304339921230248072363968371848*X^19
- 643843434857848539194345398112509232578975566640912*X^18
+ 1128465811680636343908207782177026746693398274553346*X^17
+ 524140684586680712601096167837041759847337764905845*X^16
- 10885187911246093023626114863052011064731450879359939*X^15
+ 39857128619273491965616000165383486337766191277815834*X^14
- 84589728306889040578344459661369455545325068373188045*X^13
+ 88500068455184117632678312070023099514040525790222556*X^12
+ 104398778112711569893288221924610365293381106411320929*X^11
- 726902167552191816655792183457716265829393178314290203*X^10
+ 1922066025331454173287246580581811058539922937509487197*X^9
- 3492260106307174621894306341112753326884644246511613126*X^8
+ 4822306854049822036578236210158621331526397751603080867*X^7
- 5206498890378369345974012647584825537483793460792861627*X^6
+ 4404285062296867833339540949860778861874260792846590353*X^5
- 2876755961598229733762335392724553413116008544800512599*X^4
+ 1405323891345305062625580442426700486014326484361169531*X^3
- 484366886859956010863945499018675725522237006939513480*X^2
+ 105171426618171439624835342819839690818149446384628800*X
- 10824748863501827168751917307247790074531337625536000);
  
  C :=
-1331*(X^3 + 769*X^2 - 6563*X + 33607) *(512*X^8 + 61144*X^7 -
6442069*X^6 + 172304133*X^5 - 1536518406*X^4 + 4337330046*X^3 +
6950207639*X^2 - 49462585951*X + 62713879832) *(X^12 + 8279*X^11 +
24882*X^10 + 1026960*X^9 - 12744710*X^8 + 101685573*X^7 -
834657362*X^6 + 2839501456*X^5 - 3824254676*X^4 - 17889937351*X^3 +
132513794655*X^2 - 294458963550*X + 217556206213) *(X^14 + 10*X^13 -
2075*X^12 + 30428*X^11 + 758769*X^10 - 8519313*X^9 + 76367126*X^8 -
92006079*X^7 - 2344653619*X^6 + 11698230071*X^5 - 11140635495*X^4 -
55927459933*X^3 + 185519871981*X^2 - 221506967280*X + 98133150272)
*(X^16-75*X^15+3295*X^14-92424*X^13 + 1947917*X^12 - 30142674*X^11 +
329659022*X^10 - 2543487848*X^9 + 14048607628*X^8 - 56478689465*X^7 +
167296164552*X^6 - 366229712039*X^5 + 586536468642*X^4 -
668442965082*X^3 + 512872346720*X^2 - 236894208325*X + 49952548375);

RR<x,y,z> := PolynomialRing(Integers(),3);
Bhom := &+[ Integers()!(Coefficient(B,i))*x^i*z^(55-i) : i in [0..55]];
Chom := &+[ Integers()!(Coefficient(C,i))*x^i*z^(54-i) : i in [0..54]];
Ahom := &+[ Integers()!(Coefficient(A,i))*x^i*z^(55-i) : i in [0..55]];
jmap := map<EE -> P1 | [Evaluate(Bhom+Chom*y,[EE.1,EE.2,EE.3]),Evaluate(Ahom,[EE.1,EE.2,EE.3])]>;

P := EE![4,5,1];
// Mordell-Weil sieve.

// j = 0 and j = 1728 are rational points on the curve.

// New method. 

it := 15;
curN := LCM([ i : i in [1..it]]);
permissiblek := [ k : k in [0..curN-1]];

reallydone := false;

param := 233;
bound := LCM([ i : i in [1..param]]) - 1; 

pp := 2;
firstrun := true;
while (reallydone eq false) do
printf "Starting with N = %o and #permissiblek = %o.\n",curN,#permissiblek;
done := false;
p := 2;
while (done eq false) do
  if IsPrime(p) and (p ne 11) then
    EE2 := ChangeRing(EE,GF(p));
    Pred := EE2![4,5,1];
    o := Order(Pred);
    g := GCD(o,curN);
    if (firstrun eq true) or (Valuation(o,pp) ge Valuation(curN,pp)) then
      P1Fp := ProjectiveSpace(GF(p),1);
      jmap2 := map<EE2 -> P1Fp | [Evaluate(Bhom+Chom*y,[EE2.1,EE2.2,EE2.3]),Evaluate(Ahom,[EE2.1,EE2.2,EE2.3])]>;    
      jlist := [ jmap2(k*Pred) : k in [1..o]];
      goodk := {};
      for k in [1..o] do
        if jlist[k] eq P1Fp![1,0] then
          Include(~goodk,(k mod g));
        else
          EFp := EllipticCurveWithjInvariant(jlist[k][1]);
	  good := false;
          t1 := TraceOfFrobenius(EFp);
          t2 := -t1;
          if <Integers(121)!t1,Integers(121)!p> in pairs then
	    good := true;
	  end if;
          if <Integers(121)!t2,Integers(121)!p> in pairs then
	    good := true;
	  end if;	
	  if (jlist[k][1] eq 0) then
	    good := true;
	  end if;
	  if (jlist[k][1] eq 1728) then
	    good := true;
	  end if;	
          if (good eq true) then
	    Include(~goodk,(k mod g));
	  end if;  
	end if;
      end for;
      if #goodk lt g then
        newperm := [ k : k in permissiblek | (k mod g) in goodk ];
        if #newperm lt #permissiblek then
          printf "After p = %o, cut the number of k's from %o to %o.\n",p,#permissiblek,#newperm;
	  permissiblek := newperm;
        end if;
      end if;
    end if;
  end if;
  if (#permissiblek lt 50000) then
    done := true;
  end if;
  p := NextPrime(p);
  if (p eq 11) then
    p := 13;
  end if;
end while;

foundnext := false;
firstrun := false;
while (foundnext eq false) do
  it := it + 1;
  chk, pp := IsPrimePower(it);
  if (chk eq true) then
    newperm := Sort([ (k+i*curN) : k in permissiblek, i in [0..pp-1]]);
    curN := curN*pp;
    permissiblek := newperm;
    foundnext := true;
  end if;
end while;
if (curN gt bound) then
  reallydone := true;
end if;
end while;

// Let's finish off the numbers.
newperm := [ k - curN : k in permissiblek] cat permissiblek;
permissiblek := newperm;

printf "In the final step, there are %o permissible k.\n",#permissiblek;
p := 2;
done := false;
while (done eq false) do
  if IsPrime(p) and (p ne 11) then
    EE2 := ChangeRing(EE,GF(p));
    Pred := EE2![4,5,1];
    o := Order(Pred);
    P1Fp := ProjectiveSpace(GF(p),1);
    jmap2 := map<EE2 -> P1Fp | [Evaluate(Bhom+Chom*y,[EE2.1,EE2.2,EE2.3]),Evaluate(Ahom,[EE2.1,EE2.2,EE2.3])]>;
    jlist := [ jmap2(k*Pred) : k in [1..o]];
    goodk := [];
    for k in [1..o] do
      if jlist[k] eq P1Fp![1,0] then
        Append(~goodk,(k mod o));
      else
        EFp := EllipticCurveWithjInvariant(jlist[k][1]);
	good := false;
        t1 := TraceOfFrobenius(EFp);
        t2 := -t1;
        if <Integers(121)!t1,Integers(121)!p> in pairs then
	  good := true;
	end if;
        if <Integers(121)!t2,Integers(121)!p> in pairs then
	  good := true;
	end if;	
	if (jlist[k][1] eq 0) then
	  good := true;
	end if;
	if (jlist[k][1] eq 1728) then
	  good := true;
	end if;	
        if (good eq true) then
	  Append(~goodk,(k mod o));
	end if;
      end if;
    end for;
    if (#goodk lt o) then
      newperm := [ k : k in permissiblek | (k mod o) in goodk ];
      if #newperm lt #permissiblek then
        printf "After p = %o, cut the number of k's from %o to %o.\n",p,#permissiblek,#newperm;      
        permissiblek := newperm;
      end if;
    end if;
  end if;
  if #permissiblek eq 7 then
    done := true;
  else
    p := NextPrime(p);
    if (p eq 11) then
      p := 13;
    end if;
  end if;
end while;
printf "All k*P ruled out (with |k| <= %o) except for -5 <= k <= 1.\n",curN;
printf "Total time was %o seconds.\n",Cputime(t0);
