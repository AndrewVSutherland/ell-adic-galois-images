// This Magma script is for computing models of modular curves
// by building weight 2 Eisenstein series and then getting the entire weight
// 4 space by multiplying them and hitting with Hecke operators.

// This script also computes the values at cusps of the elements of
// weight 2, 6 and 8 and uses this to provably identify the subspace
// of cusp forms.

// This script won't work for modular curves X_H with genus less than 3.
// Also, it will completely fail on subgroups H where there is a subgroup
// K containing H so that X_K and X_H have the same number of cusps.

// The new feature is that it should work for an arbitrary level and subgroup.
// One should be able to find E4 and E6 as ratios of elements of the canonical
// ring.

if (not assigned l) then
  printf "This script requires a command line argument.\n";
  printf "The usage is magma l:=label canmodel.m";
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

Attach("../groups/gl2.m");
load "../groups/gl2data.m";

padicdata := GL2Load("../groups/gl2_" cat IntegerToString(p) cat "adic.txt");

phiN := EulerPhi(N);
G := GL(2,Integers(N));
genlist := Generators(padicdata[l]`subgroup);
HH := sub<G | [ Transpose(g) : g in genlist]>;

// Conjugate HH to contains [1,0,0,-1] if possible.

if not (G![1,0,0,-1] in HH) then
  printf "Trying to conjugate HH to make it contain [1,0,0,-1].\n";
  CC := ConjugacyClasses(HH);
  lst := [ IsConjugate(G,CC[i][3],G![1,0,0,-1]) : i in [1..#CC]];
  ind := Index(lst,true);
  if (ind gt 0) then
    chk, mat := IsConjugate(G,CC[ind][3],G![1,0,0,-1]);
    printf "Yes, we can conjugate HH by %o to make it contains [1,0,0,-1].\n",mat;
    printf "Doing so.\n";
    HH2 := Conjugate(HH,mat);
    HH := HH2;
  else
    printf "No, we can't conjugate HH to make it contains [1,0,0,-1].\n";
  end if;
end if;

// We need to choose a Hecke prime, a prime for which Hecke operators
// act in a nice and predictable way. We can always choose a prime p = 1 (mod N).
// If the group contains [1,0,0,-1] we can choose any prime p = -1 (mod N). 
// Any odd level group which has non-cuspidal real points must contain an 
// element conjugate to [1,0,0,-1]. 

nicereflect := false;
if G![1,0,0,-1] in HH then
  nicereflect := true;
end if;
heckeprime := 2;
done := false;
while (done eq false) do
  if (heckeprime mod N eq 1) then
    done := true;
  end if;
  if (heckeprime mod N eq (N-1)) and (nicereflect eq true) then
    done := true;
  end if;
  if (done eq false) then
    heckeprime := NextPrime(heckeprime);
  end if;
end while;
printf "Using the prime %o for Hecke operators.\n",heckeprime;

logfilename := "model" cat l cat ".out";
System("rm " cat logfilename);
SetLogFile(logfilename);
modelfilename := "modelfile" cat l cat ".txt";
System("rm " cat modelfilename);
sub := HH;
ind := Index(G,HH);
K<zeta> := CyclotomicField(N);
RR<qq> := PuiseuxSeriesRing(K);

// Goal: Choose precision to automatically take into account
// the field of definition of the Fourier coefficients and the cusp width
// of the cusp at infinity.

Tsub := sub<G | G![1,1,0,1]>;
cuspwidth := Index(Tsub, HH meet Tsub);
printf "The modular forms for this subgroup have a Fourier expansion expressible in terms of q^(1/%o).\n",cuspwidth;
U, mp := UnitGroup(Integers(N));
gens := [ mp(U.i) : i in [1..#Generators(U)]];
elts := [ G![1,0,0,gens[i]] : i in [1..#gens]];
Galsub := sub<G | elts> meet HH;
gens2 := [ (Galsub.i)[2][2] : i in [1..#Generators(Galsub)]];

// The Fourier coefficients all live in the fixed field of Galsub, thought
// of as a subgroup of (Z/NZ)^x.
// Now, let's find that fixed field.

A := Automorphisms(K);
sortedlist := [];
for i in [1..N] do
  if GCD(i,N) eq 1 then
    ind := Index([ A[j](zeta) - zeta^i : j in [1..#A]],0);
    Append(~sortedlist,<i,A[ind]>);
  end if;
end for;

SS := Subfields(K);
grp := sub<GL(1,Integers(N)) | gens2>;
fielddeg := Index(GL(1,Integers(N)),grp);
if fielddeg eq 1 then
  K2 := Rationals();
  chk, embed := IsSubfield(K2,K);
end if;
cnt := 0;
for i in [1..#SS] do
  if Degree(SS[i][1]) eq fielddeg then
    prim := SS[i][2](SS[i][1].1);
    good := true;
    for g in Generators(grp) do
      ind := Index([ sortedlist[k][1] : k in [1..#sortedlist]],Integers()!g[1][1]);
      if sortedlist[ind][2](prim) ne prim then
        good := false;
      end if;
    end for;
    if good eq true then
      cnt := cnt + 1;
      printf "Found good field number %o.\n",cnt;
      K2<z> := SS[i][1];
      embed := SS[i][2];
      if (cnt gt 1) then
        printf "Error! We found a second good field. That's a problem.\n";
	bad := 0;
	bad2 := 1/bad;
      end if;
    end if;
  end if;  
end for;
R<q> := PuiseuxSeriesRing(K2);

printf "The Fourier coefficients of the modular forms live in the field %o.\n",K2;

// The map embed is from K2 to K. We can pull back an element from K to
// K2 via (elt)@@embed if elt is actually in K2.

// Use some sort of automatic precision chooser. Increase it
// if the Fourier coefficients live in a smaller field. Also increase it
// if the cusp width is smaller than normal.

prec := 720*N*(N div cuspwidth)*(phiN div fielddeg);

printf "Precision goes up to q^%o.\n",prec/N;

// Simplify a Q-vector space. This script takes a matrix M
// and finds the lattice of elements L where all the coordinates are integers.
// Then it finds an LLL-reduced basis for that lattice. It returns
// a square matrix that indicates which linear combinations of the rows of M
// are the LLL-reduced basis

function nicefy(M)
  M0, T := EchelonForm(M);
  // Rows of T give current basis.
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  printf "Nicefying %ox%o matrix with denominator %o.\n",NumberOfRows(M),NumberOfColumns(M),denom;
  M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
  printf "Computing saturation.\n";
  //SetVerbose("Saturation",2);
  AA := Saturation(M2);
  printf "Done.\n";
  chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
  curbat := denom*mult*T;
  printf "Calling LLL.\n";
  newlatbasismat, change := LLL(AA : Proof := false);
  printf "Done.\n";
  finalbat := ChangeRing(change,Rationals())*curbat;
  return finalbat;
end function;

U, mp := UnitGroup(Integers(N));
lst := [ G![1,0,0,mp(U.i)] : i in [1..NumberOfGenerators(U)]];
lst := [ G![1,1,0,1] ] cat lst;
P := sub<G | lst>;
Q := sub<G | G![1,1,0,1]>;

A, B := CosetAction(G,HH);

galoisorbs := Orbits(A(P));
orbs := Orbits(A(Q));

mults := [];
for i in [1..#galoisorbs] do
  Append(~mults,#[ j : j in orbs | j subset galoisorbs[i]]);
end for;

orbitreps := OrbitRepresentatives(A(P));
rt := RightTransversal(G,HH);
mats := [];
for i in [1..#orbitreps] do
  // For each i, find a permutation g in B so that g(1) = orbitreps[i][2];
  ind := Index([ Image(A(rt[j]),1) eq orbitreps[i][2] : j in [1..#rt]],true);
  Append(~mats,rt[ind]);
end for;

einfty := GL2CuspCount(HH);
NN, HHH := SL2Level(HH);
SL2 := SL(2,Integers(NN));
pi := CosetAction(SL2,HHH);
e2 := #Fix(pi(SL2![0,1,-1,0]));
e3 := #Fix(pi(SL2![0,1,-1,-1]));
gengen := GL2Genus(HH);
printf "Subgroup %o has genus %o. It has %o cusps and %o Galois orbits of cusps with sizes %o.\n",l,gengen,einfty,#galoisorbs,mults;

// printf "Galois orbit matrices are %o.\n",mats;

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

// This function takes an element of K and computes its complex conjugate.

function conjfunc(a)
  es := Eltseq(a);
  return &+[ es[i]*zeta^(1-i) : i in [1..phiN]];
end function;

// Compute the Weierstrass p-function to a precision of q^(prec/N).
// This is up to and includeing q^(prec/N).
// This routine returns the Fourier expansion
// of normalized version of p((c*t+d)/N;t)
// This is p multiplied by (9/Pi^2)
// We use the formula for the Fourier expansion from Chapter 4 of
// Diamond and Shurman.

function weier(c,d,N,pr)
  c := c mod N;
  d := d mod N;
  const := RR!(-3);
  if (c eq 0) then
    cosval := (1/2)*(zeta^d + zeta^(-d));
    const := const + RR!(-18/(cosval - 1));
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
    ret := ret + term*qq^(m/N);
  end for;
  ret := ret + BigO(qq^((pr+N+1)/N));
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


// Step 3 - Compute Eisenstein series

// First do the forms that transform nicely under SL_2.
// Note that there are 3*N^2/8 cusps on Gamma(N) if N is a power of 2, and so the space of Eisenstein
// series (which should be spanned by the xcoords) has dimension 3*N^2/8 - 1. The relation between these
// is that the sum of all of them is zero (since the sum of all of them is a holomorphic modular form of
// weight 2 on Gamma(N)).

subsub := HH;

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
if (#kerbasis ne (einfty - 1)) then
  printf "Error! We didn't get enough Eisenstein series!.\n";
end if;

// Now we look at the Q-span of the forms with coefficients in Q(zeta_N)
// that are linear combinations of the elements in K.

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

// So finalbasismat has the coefficients of the weight 2 Eisenstein
// series for the subgroup

// Step 4 - Compute Fourier expansions

printf "Computing Weierstrass p-function Fourier expansions.\n";
xcoords := ZeroMatrix(RR,N,N);
// Values at the cusp at infinity of weight 2 Eisenstein series
eisenstein_cuspvals := ZeroMatrix(K,N,N);
for i in [1..#basislist-1] do
  a := basislist[i][1];
  b := basislist[i][2];
  printf "Computing expansion %o of %o.\n",i,#basislist-1;
  xcoords[a+1][b+1] := weier(a,b,N,prec);
  eisenstein_cuspvals[a+1][b+1] := Coefficient(xcoords[a+1][b+1],0);
end for;

printf "Computing actual Eisenstein series.\n";
eisfourier := [];
eisbasis := [];
for i in [1..Dimension(Ker2)] do
  curfourier := R!0;
  printf "Doing series %o.\n",i;
  for j in [1..#basislist-1] do
    a := basislist[j][1];
    b := basislist[j][2];
    curfourier := curfourier + finalbasismat[i][j]*xcoords[a+1][b+1];    
  end for;
  ee := Eltseq(LeadingCoefficient(curfourier));
  divfac := GCD([ Integers()!ee[i] : i in [1..#ee]]);
  curfourier := curfourier/divfac;
  Append(~eisbasis,finalbasismat[i]/divfac);
  Append(~eisfourier,curfourier);
end for;

// Use full precision when nicefying Eisenstein series
eismat := ZeroMatrix(Rationals(),#eisfourier,(prec*cuspwidth+1)*fielddeg);
printf "LLL-ing Eisenstein series Fourier expansions.\n";
for i in [1..#eisfourier] do
  for j in [0..prec+N] do
    for k in [1..phiN] do
      ind := fielddeg*j+k;
      eismat[i][ind] := Eltseq(Coefficient(eisfourier[i],j/N))[k];
    end for;
  end for;
end for;
fb := nicefy(eismat);

// Compute Fourier expansions, and values at cusps.

newfourier := [];
newfouriercuspvals := [];
cuspV := VectorSpace(K,#mats);
for i in [1..#eisfourier] do
  newf := &+[ fb[i][j]*eisfourier[j] : j in [1..#eisfourier]];
  newbasiscoeffs := &+[ fb[i][j]* eisbasis[j] : j in [1..#eisfourier]];
  curcuspvals := cuspV!0;
  for j in [1..#mats] do
    curmat := mats[j];
    hitby := act(newbasiscoeffs,curmat,N,basislist);
    cuspval := K!0;
    for kk in [1..#basislist-1] do
      a := basislist[kk][1];
      b := basislist[kk][2];
      cuspval := cuspval + hitby[kk]*Coefficient(xcoords[a+1][b+1],0);      
    end for;
    curcuspvals[j] := cuspval;
  end for;

  // Now, reread the Fourier expansion.
  absprec := AbsolutePrecision(newf);
  curfourier2 := O(q^(Floor(absprec*cuspwidth)/cuspwidth));
  for j in [0..Floor(absprec*cuspwidth)-1] do
    curfourier2 := curfourier2 + (Coefficient(newf,j/cuspwidth)@@embed)*q^(j/cuspwidth);
  end for;
  Append(~newfourier,curfourier2);
  Append(~newfouriercuspvals,curcuspvals);
end for;

// U(d) operator
// It takes a power series f, and returns f|U(d)

function U(f,d)
  qqq := Parent(f).1;
  expodenom := ExponentDenominator(f);
  start := Integers()!(Valuation(f)*expodenom);
  en := Integers()!((AbsolutePrecision(f))*expodenom - 1);
  ret := 0;
  for n in [start..en] do
    if (n mod d eq 0) then
      ret := ret + Coefficient(f,n/expodenom)*qqq^(n/(d*expodenom));
    end if;
  end for;
  ret := ret + BigO(qqq^(Ceiling(AbsolutePrecision(f)*expodenom/d)/expodenom));
  return ret;
end function;

// V(d) operator
// It takes a power series f, and returns f|V(d)

function V(f,d)
  qqq := Parent(f).1;
  expodenom := ExponentDenominator(f);
  start := Integers()!(Valuation(f)*expodenom);
  en := Integers()!((AbsolutePrecision(f))*expodenom - 1);
  ret := 0;
  for n in [start..Min(en,Ceiling(prec/d)+1)] do
    ret := ret + Coefficient(f,n/expodenom)*qqq^((n*d)/(expodenom));
  end for;
  ret := ret + BigO(qqq^(Min(en,Ceiling(prec/d)+1)/expodenom));
  return ret;
end function;

// Compute space of weight 6 forms.

numtouse := #eisfourier;
len := 3;
printf "Trying %o-tuples of the first %o Eisenstein series.\n",len,numtouse;
tuplist0 := Subsequences({i : i in [1..numtouse]},len);
tuplist := [];
for s in tuplist0 do
  if Sort(s) eq s then
    Append(~tuplist,s);
  end if;
end for;
Sort(~tuplist);
ggg := gengen;
expecteddim := 3*einfty + 5*(ggg-1);

printf "Multiplying. Choosing order randomly.\n";
prods := [];
wt6cuspvals := [];
maxprec := Floor(prec*cuspwidth/(N*heckeprime));
wt6fouriermat := ZeroMatrix(Rationals(),0,(maxprec+1)*fielddeg);
done := false;
perm := Random(Sym(#tuplist));
j := 1;
while done eq false do
  printf "Doing product %o of %o. ",j,#tuplist;
  pp := tuplist[Image(perm,j)];
  ppp := &*[ newfourier[pp[k]] : k in [1..len]];
  vecseq := &cat[ Eltseq(Coefficient(ppp,j/cuspwidth)) : j in [0..maxprec]];
  tempwt6 := VerticalJoin(wt6fouriermat,Matrix(Rationals(),1,(maxprec+1)*fielddeg,vecseq));
  if Rank(tempwt6) eq NumberOfRows(tempwt6) then
    printf "We get basis element %o of %o.\n",NumberOfRows(tempwt6),expecteddim;
    wt6fouriermat := tempwt6;
    Append(~prods,ppp);
    curcuspvals := cuspV![ &*[ newfouriercuspvals[pp[k]][l] : k in [1..len]] : l in [1..#mats]];
    Append(~wt6cuspvals,curcuspvals);
    if NumberOfRows(wt6fouriermat) eq expecteddim then
      done := true;
    else
      j := j + 1;
    end if;
  else
    printf "We didn't get anything new!\n";
    j := j + 1;
    if (j gt #tuplist) then
      printf "We didn't get everything we expected!\n";
      done := true;
    end if;
  end if;
end while;

printf "Applying T_%o.\n",heckeprime;

// If p = 1 (mod N), then the value of f | T(p) at a cusp is (1+p^(k-1))
// times the value of at that cusp.
// If p = -1 (mod N) and [1 0][0 -1] is in the group, then the value
// of f | T(p) at a cusp is (1+p^(k-1))*(the conjugate of the value of f
// at that cusp).

for j in [1..#prods] do
  printf "Doing form %o. ",j;
  ppp := U(prods[j],heckeprime)+heckeprime^5*V(prods[j],heckeprime);
  vecseq := &cat[ Eltseq(Coefficient(ppp,j/cuspwidth)) : j in [0..maxprec]];
  tempwt6 := VerticalJoin(wt6fouriermat,Matrix(Rationals(),1,(maxprec+1)*fielddeg,vecseq));
  if Rank(tempwt6) eq NumberOfRows(tempwt6) then
    printf "Form %o hit with T_%o gives us a new basis element in weight 6.\n",j,heckeprime;
    wt6fouriermat := tempwt6;
    Append(~prods,ppp);
    if (heckeprime mod N eq 1) then
      Append(~wt6cuspvals,wt6cuspvals[j]*(1+heckeprime^5));
    else
      newvec := cuspV![ conjfunc(wt6cuspvals[j][kk]) : kk in [1..#mats]];
      Append(~wt6cuspvals,newvec*(1+heckeprime^5));
    end if;
  else
    printf "We didn't get anything new.\n";
  end if;
end for;
printf "Done. In the end we got %o weight 6 forms.\n",NumberOfRows(wt6fouriermat);

kkk := 6;
ggg := gengen;
einfinity := einfty;
dim := (kkk-1)*(ggg-1) + Floor(kkk/4)*e2 + Floor(kkk/3)*e3 + Floor(kkk/2)*einfinity;
printf "The dimension of M_6 is %o.\n",dim;

if (dim ne NumberOfRows(wt6fouriermat)) then
  printf "Error! We didn't get enough weight 6 modular forms!!!\n";
  bad := 0;
  bad2 := 1/bad;
end if;

E4 := Eisenstein(4,q : Precision := maxprec+1);

// Compute the subspace of weight 6 cusp forms

printf "Computing the subspace of weight 6 cusp forms.\n";
wt6cuspdim := (kkk-1)*(ggg-1) + Floor(kkk/4)*e2 + Floor(kkk/3)*e3 + Floor(kkk/2-1)*einfinity;

nullmat := ZeroMatrix(Rationals(),dim,#mats*phiN);
for i in [1..dim] do
  nullmat[i] := VectorSpace(Rationals(),#mats*phiN)!(&cat [ Eltseq(wt6cuspvals[i][j]) : j in [1..#mats]]);
end for;
BB := Basis(NullSpace(nullmat));
printf "We get a space of dimension %o. It should be %o.\n",#BB,wt6cuspdim;
if (#BB ne wt6cuspdim) then
  bad := 0;
  bad2 := 1/bad;
end if;

wt6cuspmat := ZeroMatrix(Rationals(),wt6cuspdim,(maxprec+1)*fielddeg);
for i in [1..#BB] do
  newvec := &+[ BB[i][j]*wt6fouriermat[j] : j in [1..dim]];
  wt6cuspmat[i] := newvec;
end for;
/*
changebat := nicefy(wt6cuspmat);
wt6cuspmat := changebat*wt6cuspmat;
*/

// Make a matrix whose row space is weight 6 forms divided by E4.
printf "Making weight 2 list 1.\n";
wt6cuspformlist := [];
for i in [1..wt6cuspdim] do
  wt6cuspform := &+[ wt6cuspmat[i][j]*K2.1^((j-1) mod fielddeg)*q^(Floor((j-1)/fielddeg)/cuspwidth) : j in [1..NumberOfColumns(wt6cuspmat)]] + BigO(q^((maxprec+1)/cuspwidth));
  Append(~wt6cuspformlist,wt6cuspform);
end for;

wt2list1 := [ (wt6cuspformlist[i]+BigO(q^((maxprec+1)/cuspwidth)))/E4 : i in [1..wt6cuspdim]];
numcols := Min([ Integers()!(cuspwidth*AbsolutePrecision(wt2list1[i])) : i in [1..#wt2list1]])-1;
wt2mat1 := ZeroMatrix(Rationals(),#wt2list1,(numcols+1)*fielddeg);
for i in [1..#wt2list1] do
  for j in [0..numcols] do
    for k in [1..fielddeg] do
      wt2mat1[i][fielddeg*j+k] := Eltseq(Coefficient(wt2list1[i],j/cuspwidth))[k];
    end for;
  end for;
end for;
//wt2mat1nice := nicefy(wt2mat1);

// Compute space of weight 8 forms.

numtouse := #eisfourier;
len := 4;
printf "Trying %o-tuples of the first %o Eisenstein series.\n",len,numtouse;
tuplist0 := Subsequences({i : i in [1..numtouse]},len);
tuplist := [];
for s in tuplist0 do
  if Sort(s) eq s then
    Append(~tuplist,s);
  end if;
end for;
Sort(~tuplist);
expecteddim := 4*einfty + 7*(ggg-1);

printf "Multiplying. Choosing order randomly.\n";
prods := [];
wt8cuspvals := [];
maxprec := Floor(prec*cuspwidth/(N*heckeprime));
wt8fouriermat := ZeroMatrix(Rationals(),0,(maxprec+1)*fielddeg);
perm := Random(Sym(#tuplist));
j := 1;
done := false;
while (done eq false) do
  printf "Doing product %o of %o. ",j,#tuplist;
  pp := tuplist[Image(perm,j)];
  ppp := &*[ newfourier[pp[k]] : k in [1..len]];
  vecseq := &cat[ Eltseq(Coefficient(ppp,j/cuspwidth)) : j in [0..maxprec]];
  tempwt8 := VerticalJoin(wt8fouriermat,Matrix(Rationals(),1,(maxprec+1)*fielddeg,vecseq));
  if Rank(tempwt8) eq NumberOfRows(tempwt8) then
    wt8fouriermat := tempwt8;
    printf "We get basis element %o of %o.\n",NumberOfRows(wt8fouriermat),expecteddim;
    Append(~prods,ppp);
    curcuspvals := cuspV![ &*[ newfouriercuspvals[pp[k]][l] : k in [1..len]] : l in [1..#mats]];
    Append(~wt8cuspvals,curcuspvals);
    if NumberOfRows(wt8fouriermat) eq expecteddim then
      done := true;
    else
      j := j + 1;
    end if;
  else
    printf "We didn't get anything new.\n";
    j := j + 1;
    if (j gt #tuplist) then
      done := true;
      printf "We didn't get everything we expected!\n";
    end if;
  end if;
end while;

printf "Applying T_%o.\n",heckeprime;
for j in [1..#prods] do
  printf "Doing form %o. ",j;
  ppp := U(prods[j],heckeprime)+heckeprime^7*V(prods[j],heckeprime);
  vecseq := &cat[ Eltseq(Coefficient(ppp,j/cuspwidth)) : j in [0..maxprec]];
  tempwt8 := VerticalJoin(wt8fouriermat,Matrix(Rationals(),1,(maxprec+1)*fielddeg,vecseq));
  if Rank(tempwt8) eq NumberOfRows(tempwt8) then
    printf "Form %o hit with T_%o gives us a new basis element in weight 8.\n",j,heckeprime;
    wt8fouriermat := tempwt8;
    Append(~prods,ppp);
    if (heckeprime mod N eq 1) then
      Append(~wt8cuspvals,wt8cuspvals[j]*(1+heckeprime^7));
    else
      newvec := cuspV![ conjfunc(wt8cuspvals[j][kk]) : kk in [1..#mats]];
      Append(~wt8cuspvals,newvec*(1+heckeprime^7));
    end if;
  else
    printf "We didn't get anything new.\n";
  end if;
end for;
printf "Done. In the end we got %o weight 8 forms.\n",NumberOfRows(wt8fouriermat);

kkk := 8;
ggg := gengen;
einfinity := einfty;
dim := (kkk-1)*(ggg-1) + Floor(kkk/4)*e2 + Floor(kkk/3)*e3 + Floor(kkk/2)*einfinity;
printf "The dimension of M_8 is %o.\n",dim;

if (dim ne NumberOfRows(wt8fouriermat)) then
  printf "Error! We didn't get enough weight 8 forms!!!\n";
  bad := 0;
  bad2 := 1/bad;
end if;
E6 := Eisenstein(6,q : Precision := maxprec+1);

// Compute the subspace of weight 8 cusp forms

kkk := 8;
printf "Computing the subspace of weight 8 cusp forms.\n";
wt8cuspdim := (kkk-1)*(ggg-1) + Floor(kkk/4)*e2 + Floor(kkk/3)*e3 + Floor(kkk/2-1)*einfinity;

nullmat := ZeroMatrix(Rationals(),dim,#mats*phiN);
for i in [1..dim] do
  nullmat[i] := VectorSpace(Rationals(),#mats*phiN)!(&cat [ Eltseq(wt8cuspvals[i][j]) : j in [1..#mats]]);
end for;
BB := Basis(NullSpace(nullmat));
printf "We get a space of dimension %o. It should be %o.\n",#BB,wt8cuspdim;
if (#BB ne wt8cuspdim) then
  bad := 0;
  bad2 := 1/bad;
end if;

wt8cuspmat := ZeroMatrix(Rationals(),wt8cuspdim,(maxprec+1)*fielddeg);
for i in [1..#BB] do
  newvec := &+[ BB[i][j]*wt8fouriermat[j] : j in [1..dim]];
  wt8cuspmat[i] := newvec;
end for;
//changebat := nicefy(wt8cuspmat);
//wt8cuspmat := changebat*wt8cuspmat;

// Make a matrix whose row space is weight 8 forms divided by E6.
printf "Making weight 2 list 2.\n";
wt8cuspformlist := [];
for i in [1..wt8cuspdim] do
  wt8cuspform := &+[ wt8cuspmat[i][j]*K2.1^((j-1) mod fielddeg)*q^(Floor((j-1)/fielddeg)/cuspwidth) : j in [1..NumberOfColumns(wt8cuspmat)]] + BigO(q^((maxprec+1)/cuspwidth));
  Append(~wt8cuspformlist,wt8cuspform);
end for;

wt2list2 := [ (wt8cuspformlist[i]+BigO(q^((maxprec+1)/cuspwidth)))/E6 : i in [1..wt8cuspdim]];
numcols := Min([ Integers()!(cuspwidth*AbsolutePrecision(wt2list2[i])) : i in [1..#wt2list2]])-1;
wt2mat2 := ZeroMatrix(Rationals(),#wt2list2,(numcols+1)*fielddeg);
for i in [1..#wt2list2] do
  for j in [0..numcols] do
    for k in [1..fielddeg] do
      wt2mat2[i][fielddeg*j+k] := Eltseq(Coefficient(wt2list2[i],j/cuspwidth))[k];
    end for;
  end for;
end for;
//wt2mat2nice := nicefy(wt2mat2);
wt21 := wt2mat1;
wt22 := wt2mat2;
V := RowSpace(wt21) meet RowSpace(wt22);
B := Basis(V);
intermat0 := Matrix([ Eltseq(B[i]) : i in [1..#B]]);
fb := nicefy(intermat0);
intermat := fb*intermat0;

// intermat should be a matrix whose rows are the q-expansions of a basis 
// for S_2.
kkk := 2;
dim := ggg;
printf "The dimension of S_2 is %o. We got %o forms in S_2.\n",dim,NumberOfRows(
intermat);

cuspforms := [];
for i in [1..ggg] do
  curform := &+[ intermat[i][j]*K2.1^((j-1) mod fielddeg)*q^(Floor((j-1)/fielddeg)/cuspwidth) : j in [1..NumberOfColumns(intermat)]] + BigO(q^(maxprec/cuspwidth));
  Append(~cuspforms,curform);
end for;

// Output cusp forms to model file.

ABCD<xx> := PolynomialRing(Rationals());
PrintFile(modelfilename,"A<xx> := PolynomialRing(Rationals());");
PrintFile(modelfilename,Sprintf("fieldpol := %o;",ABCD!DefiningPolynomial(K2)));
PrintFile(modelfilename,"K2<z> := NumberField(fieldpol);");
PrintFile(modelfilename,"R<q> := PuiseuxSeriesRing(K2);");
for i in [1..ggg] do
  PrintFile(modelfilename,Sprintf("cusp%o := %o;",i,cuspforms[i]));
end for;

// Compute canonical model

printf "Building canonical model.\n";
len := 2;
// This generic case should work as long as C isn't hyperelliptic or trigonal
if (ggg eq 3) then
  len := 4;
end if;
numtouse := #cuspforms;
tuplist := [];
bigset := { i : i in [1..len+numtouse-1]};
S := Subsets(bigset,numtouse-1);
for s in S do
  s2 := Sort(SetToSequence(s));
  mults := [ s2[1]-1] cat [ s2[i]-s2[i-1]-1 : i in [2..numtouse-1]] cat [ len+numtouse-1 - s2[numtouse-1]];
  newtup := [];
  for j in [1..numtouse] do
    if (mults[j] ne 0) then
      newtup := newtup cat [ j : k in [1..mults[j]]];
    end if;
  end for;
  Append(~tuplist,newtup);
end for;
tuplist := Sort(tuplist);

printf "Multiplying.\n";
prods := [];
for j in [1..#tuplist] do
  //printf "Doing product %o of %o.\n",j,#tuplist;
  pp := tuplist[j];
  ppp := &*[ cuspforms[pp[k]] : k in [1..len]];
  Append(~prods,ppp);
end for;
printf "Done.\n";
printf "Matricizing.\n";
bigmat := ZeroMatrix(Rationals(),#prods,(maxprec+1)*cuspwidth);
for i in [1..#prods] do
  for j in [0..maxprec-1] do
    for k in [1..fielddeg] do
      ind := fielddeg*j+k;
      bigmat[i][ind] := Eltseq(Coefficient(prods[i],j/cuspwidth))[k];
    end for;
  end for;
end for;
printf "Done.\n";
NN := NullSpace(bigmat);
B := Basis(NN);
if #B eq 0 then
  printf "No relations found!\n";
  bad := 0;
  bad2 := 1/bad;
end if;
relationmat := ZeroMatrix(Rationals(),#B,#prods);
for i in [1..#B] do
  ee := Eltseq(B[i]);
  for j in [1..#prods] do
    relationmat[i][j] := ee[j];
  end for;
end for;
newrels := nicefy(relationmat);
newrelationmat := newrels*relationmat;

// Handle the trigonal case
istrigonal := false;
if (ggg eq 4) then
  istrigonal := true;
end if;

tuplist2 := [];
len2 := 0;
if istrigonal then
  len2 := 3;
  bigset := { i : i in [1..len2+numtouse-1]};
  S := Subsets(bigset,numtouse-1);
  for s in S do
    s2 := Sort(SetToSequence(s));
    mults := [ s2[1]-1] cat [ s2[i]-s2[i-1]-1 : i in [2..numtouse-1]] cat [ len2+numtouse-1 - s2[numtouse-1]];
    newtup := [];
    for j in [1..numtouse] do
      if (mults[j] ne 0) then
        newtup := newtup cat [ j : k in [1..mults[j]]];
      end if;
    end for;
    Append(~tuplist2,newtup);
  end for;
  tuplist2 := Sort(tuplist2);

  printf "Searching for cubic relations. Multiplying.\n";
  prods := [];
  for j in [1..#tuplist2] do
    //printf "Doing product %o of %o.\n",j,#tuplist;
    pp := tuplist2[j];
    ppp := &*[ cuspforms[pp[k]] : k in [1..len2]];
    Append(~prods,ppp);
  end for;
  printf "Done.\n";
  printf "Matricizing.\n";
  bigmat := ZeroMatrix(Rationals(),#prods,(maxprec+1)*fielddeg);
  for i in [1..#prods] do
    for j in [0..maxprec-1] do
      for k in [1..fielddeg] do
        ind := fielddeg*j+k;
        bigmat[i][ind] := Eltseq(Coefficient(prods[i],j/cuspwidth))[k];
      end for;
    end for;
  end for;
  printf "Done.\n";
  NN := NullSpace(bigmat);
  BB := Basis(NN);
  if #BB eq 0 then
    printf "No relations found!\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
  relationmat2 := ZeroMatrix(Rationals(),#BB,#prods);
  for i in [1..#BB] do
    ee := Eltseq(BB[i]);
    for j in [1..#prods] do
      relationmat2[i][j] := ee[j];
    end for;
  end for;
  newrels2 := nicefy(relationmat2);
  newrelationmat2 := newrels2*relationmat2;
end if;

SSS := PolynomialRing(Rationals(),numtouse);
// Assign names, going from a to z, then aa, ab, ac, etc.
alphabet := ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"];
namelist := [];
for i in [1..numtouse] do
  namei := "";
  curval := i-1;
  done := false;
  while (done eq false) do
    rem := curval mod 26;
    curval := Integers()!((curval-rem)/26);
    namei := alphabet[rem+1] cat namei;
    if (curval eq 0) then
      done := true;
    end if;
    if (curval gt 0) then
      curval := curval - 1;
    end if;
  end while;
  Append(~namelist,namei);
end for;
AssignNames(~SSS,namelist);
vars := [ SSS.i : i in [1..numtouse]];
monlist := [ &*[ vars[tuplist[i][j]] : j in [1..len]] : i in [1..#tuplist]];
relations := [];
for i in [1..#B] do
  relat := &+[ newrelationmat[i][j]*monlist[j] : j in [1..#tuplist]];
  Append(~relations,relat);
end for;
if istrigonal then
  I := ideal<SSS | relations>;
  monlist2 := [ &*[ vars[tuplist2[i][j]] : j in [1..len2]] : i in [1..#tuplist2]];
  for i in [1..#BB] do
    relat := &+[ newrelationmat2[i][j]*monlist2[j] : j in [1..#tuplist2]];
  end for;
  if not (relat in I) then
    printf "Adding a new degree %o relation.\n",len2;
    Append(~relations,relat);
    I := ideal<SSS | relations>;
  end if;
end if;

C := Curve(ProjectiveSpace(Rationals(),numtouse-1),relations);
printf "The curve C is defined by %o.\n",relations;

PrintFile(modelfilename,"namelist := ");
PrintFileMagma(modelfilename,namelist);
PrintFile(modelfilename,";");
PrintFile(modelfilename,Sprintf("SSS := PolynomialRing(Rationals(),%o);",numtouse));
PrintFile(modelfilename,"AssignNames(~SSS,namelist);");
for i in [1..#namelist] do
  PrintFile(modelfilename,Sprintf("%o := SSS.%o;",namelist[i],i));
end for;
PrintFile(modelfilename,Sprintf("relations := %o;",relations));
PrintFile(modelfilename,Sprintf("C := Curve(ProjectiveSpace(Rationals(),%o),relations);",numtouse-1));

// Compute bases for graded pieces of canonical ring

// Riemann-Roch says we're guaranteed to find E6 as a ratio
// of a weight k and weight k-6 elements of the canonical ring
// if k >= (3*einfty + 2*e3 + e2 + 1)/(g-1) + 7.

E4d := Ceiling(((2*einfty+e3+e2+1)/(ggg-1)+5)/2);
E6d := Ceiling(((3*einfty+2*e3+e2+1)/(ggg-1)+7)/2);
maxd := E6d;
printf "Setting maxd = %o.\n",maxd;

canring := [ <cuspforms,vars>];
for d in [2..maxd] do
  dimen := (2*d-1)*(ggg-1);
  // Coefficients go from q^(d/N) to q^((d+maxprec)/N)
  fouriermat := ZeroMatrix(Rationals(),0,(maxprec-1)*fielddeg);
  prds := [ <i,j> : i in [1..#cuspforms], j in [1..#canring[d-1][1]]];
  done := false;
  curind := 1;
  newfourier := [];
  newvars := [];
  printf "Working on weight %o forms. Need %o.\n",2*d,dimen;
  while (done eq false) do
    e1 := prds[curind][1];
    e2 := prds[curind][2];
    pp := cuspforms[e1]*canring[d-1][1][e2];
    vecseq := &cat[ Eltseq(Coefficient(pp,j/cuspwidth)) : j in [d..d+maxprec-2]];
    tempfouriermat := VerticalJoin(fouriermat,Matrix(Rationals(),1,(maxprec-1)*fielddeg,vecseq));
    if Rank(tempfouriermat) eq NumberOfRows(tempfouriermat) then
      printf "Product <%o,%o> gives us element %o of %o for d = %o.\n",e1,e2,NumberOfRows(tempfouriermat),dimen,d;
      fouriermat := tempfouriermat;
      Append(~newfourier,pp);
      Append(~newvars,canring[1][2][e1]*canring[d-1][2][e2]);
      if NumberOfRows(tempfouriermat) eq dimen then
        done := true;
	Append(~canring,<newfourier,newvars>);
      end if;
    end if;
    if (done eq false) then
      curind := curind + 1;
      if (curind gt #prds) then
        done := true;
	Append(~canring,<newfourier,newvars>);
      end if;
    end if;
  end while;
end for;

smalld := E4d-2;
bigd := E4d;
E4 := Eisenstein(4,q : Precision := 2*Ceiling((maxprec-1)/cuspwidth)); 

E4mat := ZeroMatrix(Rationals(),0,(maxprec-1)*fielddeg);
for i in [1..#canring[smalld][1]] do
  pp := E4*canring[smalld][1][i];
  vecseq := &cat[ Eltseq(Coefficient(pp,j/cuspwidth)) : j in [smalld..smalld+maxprec-2]];
  E4mat := VerticalJoin(E4mat,Matrix(Rationals(),1,(maxprec-1)*fielddeg,vecseq));  
end for;
for j in [1..#canring[bigd][1]] do
  vecseq := &cat[ Eltseq(-Coefficient(canring[bigd][1][j],i/cuspwidth)) : i in [smalld..smalld+maxprec-2]];
  E4mat := VerticalJoin(E4mat,Matrix(Rationals(),1,(maxprec-1)*fielddeg,vecseq));
end for;

smalld := E6d-3;
bigd := E6d;
E6 := Eisenstein(6,q : Precision := 2*Ceiling((maxprec-1)/cuspwidth)); 

E6mat := ZeroMatrix(Rationals(),0,(maxprec-1)*fielddeg);
for i in [1..#canring[smalld][1]] do
  pp := E6*canring[smalld][1][i];
  vecseq := &cat[ Eltseq(Coefficient(pp,j/cuspwidth)) : j in [smalld..smalld+maxprec-2]];
  E6mat := VerticalJoin(E6mat,Matrix(Rationals(),1,(maxprec-1)*fielddeg,vecseq));  
end for;
for j in [1..#canring[bigd][1]] do
  vecseq := &cat[ Eltseq(-Coefficient(canring[bigd][1][j],i/cuspwidth)) : i in [smalld..smalld+maxprec-2]];
  E6mat := VerticalJoin(E6mat,Matrix(Rationals(),1,(maxprec-1)*fielddeg,vecseq));
end for;

printf "Searching for E4.\n";
NN1 := NullSpace(E4mat);
M1 := Matrix(Basis(NN1));
printf "Dimension of null space is %o.\n",Dimension(NN1);
printf "Searching for E6.\n";
NN2 := NullSpace(E6mat);
M2 := Matrix(Basis(NN2));
printf "Dimension of null space is %o.\n",Dimension(NN2);
cb1 := nicefy(M1);
cb2 := nicefy(M2);
E4sol := (cb1*M1)[1];
E6sol := (cb2*M2)[1];

smalld := E4d-2;
bigd := E4d;
E4elt := &+[ E4sol[i+#canring[smalld][1]]*canring[bigd][2][i] : i in [1..#canring[bigd][1]]]/&+[ E4sol[i]*canring[smalld][2][i] : i in [1..#canring[smalld][1]]];

smalld := E6d-3;
bigd := E6d;
E6elt := &+[ E6sol[i+#canring[smalld][1]]*canring[bigd][2][i] : i in [1..#canring[bigd][1]]]/&+[ E6sol[i]*canring[smalld][2][i] : i in [1..#canring[smalld][1]]];

PrintFile(modelfilename,Sprintf("E4elt := (%o)/(%o);",Numerator(E4elt),Denominator(E4elt)));
PrintFile(modelfilename,Sprintf("E6elt := (%o)/(%o);",Numerator(E6elt),Denominator(E6elt)));

// Sometimes this next line is a problem.
// jcanring := (1728*E4elt^3)/(E4elt^3 - E6elt^2);
//jmap := map<C -> ProjectiveSpace(Rationals(),1) | [Numerator(jcanring),Denominator(jcanring)]>;
PrintFile(modelfilename,"jcanring := (1728*E4elt^3)/(E4elt^3-E6elt^2);");

PrintFile(modelfilename,"jmap := map<C -> ProjectiveSpace(Rationals(),1) | [Numerator(jcanring),Denominator(jcanring)]>;");
quit;

