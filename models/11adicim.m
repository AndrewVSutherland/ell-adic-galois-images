// The goal of this script is to determine the 3-adic image for
// an elliptic curve over Q.

p := 11;
Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subdat := GL2Load("../groups/gl2_11adic.txt");

// Give an elliptic curve E and a label, try to rule out the possibility
// that the mod N image of Galois is contained in that subgroup by finding
// a rho_E,N(Frob_q) that is not conjugate in GL(2,Z/NZ) to an element of
// the subgroup. It returns true if the group is ruled out, false otherwise.
// This version should be fast, and the script pre-computes the
// Similarity invariants for X_ns^+(11) and X_ns^+(121).

function ruleout(E,sublab,invars)
  grp := subdat[sublab]`subgroup;
  lev := subdat[sublab]`level;
  G := GL(2,Integers(lev));
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
      done := true;
      ret := false;
    end if;
  end while;
  return ret;
end function;

// The next function checks to see if a j-invariant lifts to X_ns^+(11).

function xns11(E)
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

RR<x,y,z> := PolynomialRing(Rationals(),3);
Bhom := &+[ Coefficient(B,i)*x^i*z^(55-i) : i in [0..55]];
Chom := &+[ Coefficient(C,i)*x^i*z^(54-i) : i in [0..54]];
Ahom := &+[ Coefficient(A,i)*x^i*z^(55-i) : i in [0..55]];
jmap := map<EE -> P1 | [Evaluate(Bhom+Chom*y,[E.1,E.2,E.3]),Evaluate(Ahom,[E.1,E.2,E.3])]>;

// Only rational point in base locus is (0 : 1 : 0), which maps to j = 0.
jj := jInvariant(E);
pt := P1![jj,1];
X := pt@@jmap;
ret := false;
rp := RationalPoints(X);
//printf "Rational points on X = %o.\n",rp;
if #rp ge 2 then
  ret := true;
else
  if jj eq 0 then
    ret := true;
  else
    ret := false;
  end if;
end if;
return ret;
end function;

// The script starts working here.

CC := ConjugacyClasses(subdat["11.55.1.1"]`subgroup);
ns11invars := [ GL2SimilarityInvariant(CC[i][3]) : i in [1..#CC]];
CC := ConjugacyClasses(subdat["121.6655.511.1"]`subgroup);
ns121invars := [ GL2SimilarityInvariant(CC[i][3]) : i in [1..#CC]];

function elevenadic(E)
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

  if jInvariant(E) eq (-11^2) then
    curlab := "11.60.1.4";
    E1 := EllipticCurve([1,1,1,-305,7888]);
    if IsIsomorphic(E,E1) then
      curlab := "11.120.1.4";
    end if;
    E2 := EllipticCurve([1,1,0,-2,-7]);
    if IsIsomorphic(E,E2) then
      curlab := "11.120.1.9";
    end if;
  end if;
  
  if jInvariant(E) eq (-11*131^3) then
    curlab := "11.60.1.3";
    E1 := EllipticCurve([1,1,0,-3632,82757]);
    if IsIsomorphic(E,E1) then
      curlab := "11.120.1.3";
    end if;
    E2 := EllipticCurve([1,1,1,-30,-76]);
    if IsIsomorphic(E,E2) then
      curlab := "11.120.1.8";
    end if;
  end if;

  if curlab eq "1.1.0.1" then
    chk := ruleout(E,"11.55.1.1",ns11invars);
    if (chk eq false) then
      // Test lift to non-split Cartan modulo 11.
      chk2 := xns11(E);
      if chk2 then
        curlab := "11.55.1.1";
	chk3 := ruleout(E,"121.6655.511.1",ns121invars);
	if chk3 eq false then
          printf "Couldn't rule out possibility of lifting to non-split Cartan modulo 121!\n";
	  bad := 0;
	  bad2 := 1/bad;
        end if;
      end if;
    end if;
  end if;

  return curlab;
end function;

DB := CremonaDatabase();
for N in [1..499999] do
  iso := NumberOfIsogenyClasses(DB,N);
  for i in [1..iso] do
    k := NumberOfCurves(DB,N,i);
    for j in [1..k] do
      E := EllipticCurve(DB,N,i,j);
      lab := elevenadic(E);
      if (lab ne "1.1.0.1") and (lab[1] ne "C") then
        printf "N=%o, i=%o, j=%o, %o - %o.\n",N,i,j,aInvariants(E),lab;
      end if;	
    end for;
  end for;
end for;
