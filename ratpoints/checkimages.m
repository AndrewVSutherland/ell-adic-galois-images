// The goal of this script is to verify that the l-adic images for the
// sporadic points in Table 1 are not smaller than the labels given there.

// The script takes about an hour to run, with most of the time on the level 37
// subgroups.

Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subdat5 := GL2Load("../groups/gl2_5adic.txt");
subdat7 := GL2Load("../groups/gl2_7adic.txt");
subdat11 := GL2Load("../groups/gl2_11adic.txt");
subdat13 := GL2Load("../groups/gl2_13adic.txt");
subdat17 := GL2Load("../groups/gl2_17adic.txt");
subdat37 := GL2Load("../groups/gl2_37adic.txt");

// Give an elliptic curve E and a label, try to rule out the possibility
// that the mod N image of Galois is contained in that subgroup by finding
// a rho_E,N(Frob_q) that is not conjugate in GL(2,Z/NZ) to an element of
// the subgroup. It returns true if the group is ruled out, false otherwise.

function ruleout(E,grp)
  printf "Computing conjugacy classes.\n";
  t := Cputime();
  CC := ConjugacyClasses(grp);
  printf "Done. Time taken was %o sec.\n",Cputime(t);
  invars := [ GL2SimilarityInvariant(CC[i][3]) : i in [1..#CC]];
  lev := Characteristic(BaseRing(grp));
  p := PrimeFactors(lev)[1];
  G := GL(2,Integers(lev));
  done := false;
  q := 2;
  ret := true;
  complain := 10^4;
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
  end while;
  return ret;
end function;

// This function shows that the l-adic image for E cannot be a proper subgroup
// of the subgroup with label lab.

function showmaximal(E,lab)
  lev := StringToInteger(Split(lab,".")[1]);
  chk, p := IsPrimePower(lev);
  sb := 0;
  if (p eq 5) then
    sb := subdat5;
  end if;
  if (p eq 7) then
    sb := subdat7;
  end if;
  if (p eq 11) then
    sb := subdat11;
  end if;
  if (p eq 13) then
    sb := subdat13;
  end if;
  if (p eq 17) then
    sb := subdat17;
  end if;
  if (p eq 37) then
    sb := subdat37;
  end if;  
  H := sb[lab]`subgroup;
  Hlift := GL2Lift(H,lev*p);
  printf "Computing level %o maximal subgroups for %o.\n",lev*p,lab;
  M := MaximalSubgroups(Hlift);
  printf "Done. There are %o.\n",#M;
  for i in [1..#M] do
    if GL2DeterminantIndex(M[i]`subgroup) eq 1 then
      ver := ruleout(E,M[i]`subgroup);
      if (ver eq true) then
        printf "Group %o ruled out.\n",i;
      else
        printf "Group %o not ruled out.\n",i;
      end if;
    end if;
  end for;
  return true;
end function;

// The confirmation that the 2-adic images for the 8 sporadic points
// on 2-adic modular curves was done in connection with the paper
// "Elliptic curves over Q and 2-adic images of Galois". See the file
// "magscript.txt" in the ancillary files associated with that document.

// 5-adic

j1 := 2^4*3^2*5^7*23^3;
E1 := MinimalTwist(EllipticCurveWithjInvariant(j1));
lab := "25.50.2.1";
showmaximal(E1,lab);

j2 := 2^122*3^3*5^7*29^3/7^5;
E2 := MinimalTwist(EllipticCurveWithjInvariant(j2));
lab := "25.75.2.1";
showmaximal(E2,lab);

// 7-adic

E1 := EllipticCurve([1,-1,1,-2680,-50053]);
E2 := EllipticCurve([1,-1,1,-131305,17430697]);
lab := "7.112.1.2";
showmaximal(E1,lab);

// 11-adic

E1 := EllipticCurve([1,1,1,-30,-76]);
lab := "11.120.1.8";
showmaximal(E1,lab);
E2 := EllipticCurve([1,1,0,-3632,82757]);
lab := "11.120.1.3";
showmaximal(E2,lab);
E3 := EllipticCurve([1,1,0,-2,-7]);
lab := "11.120.1.9";
showmaximal(E3,lab);
E4 := EllipticCurve([1,1,1,-305,7888]);
lab := "11.120.1.4";
showmaximal(E4,lab);

// 13-adic - maximal subgroups also have level 13.

j1 := 2^4*5*13^4*17^3/3^13;
j2 := -2^12*5^3*11*13^4/3^13;
j3 := 2^18*3^3*13^4*127^3*139^3*157^3*283^3*929/(5^13*61^13);

E1 := MinimalTwist(EllipticCurveWithjInvariant(j1));
E2 := MinimalTwist(EllipticCurveWithjInvariant(j2));
E3 := MinimalTwist(EllipticCurveWithjInvariant(j3));

lab := "13.91.3.2";
showmaximal(E1,lab);
showmaximal(E2,lab);
showmaximal(E3,lab);

// 17-adic

j4 := -17*373^3/2^17;
j5 := -17^2*101^3/2;

E4 := MinimalTwist(EllipticCurveWithjInvariant(j4));
lab := "17.72.1.2";
showmaximal(E4,lab);
E5 := MinimalTwist(EllipticCurveWithjInvariant(j5));
lab := "17.72.1.4";
showmaximal(E5,lab);

// 37-adic

j6 := -7*11^3;
j7 := -7*137^3*2083^3;

E6 := MinimalTwist(EllipticCurveWithjInvariant(j6));
lab := "37.114.4.1";
showmaximal(E6,lab);
E7 := MinimalTwist(EllipticCurveWithjInvariant(j7)); 
lab := "37.114.4.2";
showmaximal(E7,lab);


