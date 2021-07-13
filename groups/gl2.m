/*
    This module implements a number of Magma intrinsics for working with open subgroups H of GL(2,Zhat).
    All such subgroups are represented by their projections to GL(2,Z/NZ).
    The integer N can be be any integer for which H is the full preimage of its reduction modulo N (the least such N is the level of H).
    The trivial subgroup is represented by the trivial subgroup of GL(2,Z) (since Magma won't let us define the ring Integers(1)=Z/Z).

    Some notable intrinsics include:

    GL2Level(H) -- computes the level of H (the least N for which H is the preimage of its reduction mod N).
    GL2Index(H) -- the index of H in GL(2,Zhat), equivalently, its index in GL(2,ZNZ)
    GL2Genus(H) -- the genus of the modular curve X_H
    GL2CuspCount(H) -- the number of cusps of X_H (over Qbar)
    GL2RationalCuspCount(H) - the number of rational cusps of X_H
    GL2PointCount(H,q) -- the number of Fq-rational points on X_H
    GL2PointCounts(H,B) -- the number of Fp-rational points on X_H for primes p <= B (or prime powers)
    GL2Lpolynomial(H,q) -- the L-polynomial of X_H over F_q
    GL2Lattice(L,I) -- labeled lattice of subgroups of level dividing L of index at most I (with surjective det by default)
    GL2Label(H) -- an expensive way to directly compute the label of a single subgroup (this will force a lattice computation)
    GL2IsogenyClass(H) -- for subgroups of genus 1, returns the Cremona label and rank of the isogeny class of J_H
    GL2FrobeniusMatrix(E) -- returns a matrix in GL(2,Z) whose reduction modulo n gives the action of Frobenius on the
                             n-torsion subgroup of the given elliptic curve E over a finite field
    GL2nTorsionFrobenius(E,n) -- the reduction of GL2FrobeniusMatrix(E) modulo n
    GL2FrobeniusMatrices(E,B) -- given E/Q returns the list of Frobenius matrices of E mod p for primes p <= B of good reduction

    After attaching this file you can type GL2<tab> (or GL1<tab>) to see all available functions.

    A few additional intrinsics that are used by the GL2* intrinsics that may be of independent intrest include:

    PrimitiveDivisionPolynomial(E,n) -- the polynomial whose roots are the x-coordinates of the points of order n on E
    TorsionDegree(E,n) -- the minimal degree of an extension over which E has a rational point of order n
    EndomorphismRingData(E) -- given E/Fq returns the tr pi_E and the discriminant of the ring End(E) cap Q(pi_E)
                               (when E is ordinary this amounts to computing the endomorphism ring).
*/


function index(S,f:Project:=func<x|x>,Unique:=false)
    A := AssociativeArray();
    if Unique then
        for x in S do A[f(x)] := Project(x); end for;
    else
        for x in S do y := f(x); A[y] := IsDefined(A,y) select Append(A[y],Project(x)) else [Project(x)]; end for;
    end if;
    return A;
end function;

function lmset(M)
    return Sort([r cat [Multiplicity(M,r)]:r in Set(M)]);
end function;

function sqmod(f,g)
    Fp := GF(257); RFp := PolynomialRing(Fp);
    fp := RFp!f; gp := RFp!g;
    A := Factorization(gp);
    if #[a:a in A|a[2] eq 1 and not IsSquare(quo<RFp|a[1]>!fp)] gt 0 then return false; end if;
    return IsSquare(quo<PolynomialRing(BaseRing(g))|g>!f);
end function;

intrinsic PrimitiveDivisionPolynomial (E::CrvEll, n::RngIntElt) -> RngUpolElt
{ The monic polynomial whose roots are the x-coordinates of kbar-points of order n on E/k. }
    f := DivisionPolynomial(E,n);
    if IsPrime(n) then return f; end if;
    for p in PrimeDivisors(n) do f := ExactQuotient(f,GCD(f,DivisionPolynomial(E,ExactQuotient(n,p)))); end for;
    return f;
end intrinsic;

intrinsic IsogenyDegree (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The minimal degree of an extension over which E has a rational cyclic isogeny of degree n (which must be a prime power < 60). }
    if n eq 1 then return 1; end if;
    require IsPrimePower(n) and n lt 60: "n must be a prime power less than 60.";
    R<x> := PolynomialRing(BaseRing(E));
    m := Min([Degree(a[1]):a in Factorization(Evaluate(ClassicalModularPolynomial(n),[jInvariant(E),x]))]);
    return m;
end intrinsic;

intrinsic IsogenyGaloisGroup (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The Galois group of the minimal extension over which all cyclic n-isogenies from E are defined (n must be a prime power < 60). }
    if n eq 1 then return CyclicGroup(1); end if;
    require IsPrimePower(n) and n lt 60: "n must be a prime power less than 60.";
    R<x> := PolynomialRing(BaseRing(E));
    return GaloisGroup(Evaluate(ClassicalModularPolynomial(n),[jInvariant(E),x]));
end intrinsic;

intrinsic TorsionOrbits (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The multiset of sizes of Galois orbits of E[n] for an elliptic curve E. }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    E := WeierstrassModel(MinimalModel(E));  f := HyperellipticPolynomials(E);
    psi := PrimitiveDivisionPolynomial(E,n);
    A := Factorization(psi);
    R := PolynomialRing(BaseRing(f));
    return {* sqmod(f,a[1]) select Degree(a[1])^^(2*a[2]) else (2*Degree(a[1]))^^a[2] : a in A *};
end intrinsic;

intrinsic TorsionDegree (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The minimal degree of an extension over which E has a rational point of order n. }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    E := WeierstrassModel(MinimalModel(E));  f := HyperellipticPolynomials(E);
    A := Factorization(PrimitiveDivisionPolynomial(E,n));
    // if n is odd and the n-division polynomial is irreducible, then the mod-n image must contain -I
    if #A eq 1 and A[1][2] eq 1 and IsOdd(n) then return 2*Degree(A[1][1]); end if;
    d := Min([Degree(a[1]):a in A]);
    d := Min([(IsSquare(quo<PolynomialRing(BaseRing(E))|a[1]>!f) select 1 else 2)*Degree(a[1]) : a in A | Degree(a[1]) lt 2*d]);
    return d;
end intrinsic;

intrinsic FullTorsionDegree (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The degree of the n-torsion field of E (this can be extremely expensive, use with caution). }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    E := WeierstrassModel(MinimalModel(E));  f := HyperellipticPolynomials(E);
    R<X,Y> := PolynomialRing(BaseRing(f),2);
    g := PrimitiveDivisionPolynomial(E,n);             // roots of g are all x-coords of points of order n
    if IsOdd(n) and IsIrreducible(g) then
        return 2*#GaloisGroup(PrimitiveDivisionPolynomial(E,n));
    end if;
    h := Resultant(Y^2-Evaluate(f,X),Evaluate(g,X),X); // roots of h are all y-coords of points of order n
    return #GaloisGroup(Evaluate(h,[0,Parent(g).1])*g);
end intrinsic;

intrinsic TorsionGaloisGroup (E::CrvEll, n::RngIntElt) -> RngIntElt
{ Galois group of the n-torsion field of E (this can be extremely expensive, use with caution). }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    E := WeierstrassModel(MinimalModel(E));  f := HyperellipticPolynomials(E);
    R<X,Y> := PolynomialRing(BaseRing(f),2);
    g := PrimitiveDivisionPolynomial(E,n);             // roots of g are all x-coords of points of order n
    h := Resultant(Y^2-Evaluate(f,X),Evaluate(g,X),X); // roots of h are all y-coords of points of order n
    return GaloisGroup(Evaluate(h,[0,Parent(g).1])*g);
end intrinsic;

intrinsic TracesToLPolynomial (t::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of Frobenius traces of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    require IsPrimePower(q): "q must be a prime power.";
    R<T> := PolynomialRing(Integers());
    if #t eq 0 then return R!1; end if;
    g := #t;
    // use Newton identities to compute compute elementary symmetric functions from power sums
    e := [t[1]];  for k:=2 to g do e[k] := ExactQuotient((-1)^(k-1)*t[k]+&+[(-1)^(i-1)*e[k-i]*t[i]:i in [1..k-1]],k); end for;
    return R!([1] cat [(-1)^i*e[i]:i in [1..g]] cat [(-1)^i*q^i*e[g-i]:i in [1..g-1]] cat [q^g]);
end intrinsic;

intrinsic PointCountsToLPolynomial (n::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of point counts of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    return TracesToLPolynomial([q^i+1-n[i] : i in [1..#n]], q);
end intrinsic;

intrinsic LPolynomialToTraces (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of Frobenius traces for a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    require Degree(L) gt 0 and IsEven(Degree(L)): "Lpolynomial must have positive even degree 2g";
    g := ExactQuotient(Degree(L),2);
    b,p,e := IsPrimePower(Integers()!LeadingCoefficient(L));
    require b: "Not a valid L-polynomial, leading coefficient is not a prime power";
    require IsDivisibleBy(e,g): "Not a valid L-polynomial, leading coefficient is not a prime power with an integral gth root.";
    q := p^ExactQuotient(e,g);
    L := Reverse(L);
    if d eq 0 then d:=g; end if;
    e := [Integers()|(-1)^i*Coefficient(L,2*g-i):i in [1..d]];
    // use Newton identities to compute compute power sums from elementary symmetric functions;
    t := [e[1]]; for k:=2 to d do t[k] := (-1)^(k-1)*k*e[k] + &+[(-1)^(k-1+i)*e[k-i]*t[i] : i in [1..k-1]]; end for;
    return t, q;
end intrinsic;

intrinsic LPolynomialToPointCounts (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of point counrs of a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    t, q := LPolynomialToTraces(L:d:=d);
    if d eq 0 then d := #t; end if;
    return [q^i+1-t[i] : i in [1..d]];
end intrinsic;

intrinsic ConreyGenerator (p::RngIntElt) -> RngIntElt
{ For an odd prime p, the least positive integer a that generates (Z/p^eZ)^times for all e. }
    require IsOdd(p) and IsPrime(p): "p must be an odd prime";
    return PrimitiveRoot(p^2);
end intrinsic;

function plog(p,e,a,b) // returns nonnegative integer x such that a^x = b or -1, assuming a has order p^e
    if e eq 0 then return a eq 1 and b eq 1 select 0 else -1; end if;
    if p^e le 256 then return Index([a^n:n in [0..p^e-1]],b)-1; end if;
    if e eq 1 then
        // BSGS base case
        aa := Parent(a)!1;
        r := Floor(Sqrt(p)); s := Ceiling(p/r);
        babys := AssociativeArray(); for x:=0 to r-1 do babys[aa] := x; aa *:= a; end for;
        bb := b;
        x := 0; while x lt s do if IsDefined(babys,bb) then return (babys[bb]-r*x) mod p; end if; bb *:= aa; x +:=1; end while;
        return -1;
    end if;
    e1 := e div 2; e0 := e-e1;
    x0 := $$(p,e0,a^(p^e1),b^(p^e1)); if x0 lt 0 then return -1; end if;
    x1 := $$(p,e1,a^(p^e0),b*a^(-x0)); if x1 lt 0 then return -1; end if;
    return (x0 + p^e0*x1);
end function;

intrinsic ConreyLogModEvenPrimePower (e::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ Given an exponent e > 2 and an odd integer n returns unique integers a,s such that n = s*5^a mod 2^e with s in [-1,1] and a in [0..e-1]. }
    require e gt 2 and IsOdd(n): "e must be at least 3 and n must be an odd integers";
    R := Integers(2^e);
    s := n mod 4 eq 1 select 1 else -1;
    x := R!s*n;
    a := plog(2,e-2,R!5,x); assert a ge 0;
    return a,s;
end intrinsic;

intrinsic ConreyLogModOddPrimePower (p::RngIntElt,e::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ Given n coprime to the odd prime p returns the integer x in [0..phi(p^e)-1] for which n = r^x mod p^e, where r is the Conrey generator for p. }
    require IsOdd(p) and GCD(p,n) eq 1: "p must be an odd prime and n must not be divisible by p";
    r := ConreyGenerator(p);
    if e eq 1 then return Log(GF(p)!r,GF(p)!n); end if;
    R := Integers(p^e);  pp := p^(e-1);
    x1 := plog(p,e-1,(R!r)^(p-1),(R!n)^(p-1)); assert x1 ge 0;
    x2 := Log(GF(p)!(R!r)^pp,GF(p)!(R!n)^pp); assert x2 ge 0;
    return CRT([x1,x2],[pp,p-1]);
end intrinsic;

intrinsic ConreyCharacterValue (q::RngIntElt,n::RngIntElt,m::RngIntElt) -> FldCycElt
{ The value chi_q(n,m) of the Dirichlet character with Conry label q.n at the integer m. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if GCD(q,m) ne 1 then return 0; end if;
    if q eq 1 or n mod q eq 1 or m mod q eq 1 then return 1; end if;
    F := CyclotomicField(Order(Integers(q)!n));
    b,p,e:= IsPrimePower(q);
    if not b then return F!&*[$$(a[1]^a[2],n,m):a in Factorization(q)]; end if;
    if p gt 2 then
        a := ConreyLogModOddPrimePower(p,e,n);  b := ConreyLogModOddPrimePower(p,e,m); d := (p-1)*p^(e-1);
        return F!(RootOfUnity(d)^(a*b));
    else
        if e eq 2 then assert n mod q eq 3 and m mod q eq 3; return -1; end if; assert e gt 2;
        a,ea := ConreyLogModEvenPrimePower(e,n);  b,eb := ConreyLogModEvenPrimePower(e,m); d:= 2^(e-2);
        return F!(RootOfUnity(8)^((1-ea)*(1-eb)) * RootOfUnity(d)^(a*b));
    end if;
end intrinsic;

intrinsic ConreyCharacterValue (q::RngIntElt,n::RngIntResElt,m::RngIntResElt) -> FldCycElt
{ The value chi_q(n,m) of the Dirichlet character with Conry label q.n at the integer m. }
    return ConreyCharacterValue(q,Integers()!n,Integers()!m);
end intrinsic;

intrinsic GL1Characters(H::GrpMat) -> SeqEnum[RngIntElt]
{ Sorted list of Conrey indexes i of the Conrey characters N.i of modulus N whose kernels contain the specififed subgroup H of GL(1,Integers(N)). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return [1]; end if;
    require Type(R) eq RngIntRes and Degree(H) eq 1: "H must be a sugroup of GL(1,Z/NZ) for some positive integer N.";
    return Sort([Integers()|n[1][1] : n in GL(1,R) | &and[ConreyCharacterValue(N,n[1][1],m[1][1]) eq 1 : m in H]]) where N:=#R;
end intrinsic;

intrinsic GLIndex(H::GrpMat) -> RngIntElt
{ The index of H in its parent. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    return Index(GL(Degree(H),R),H);
end intrinsic;

intrinsic GL1Index(H::GrpMat) -> RngIntElt
{ The index of H in its parent. }
    return GLIndex(H);
end intrinsic;

intrinsic GLPermutationCharacter(H::GrpMat) -> UserProgram
{ The permutation character given by the GL_n-action on the right coset space [H\\GL_n] for a subgroup H of GL_n. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return func<A|1>; end if;
    require IsFinite(R): "H must be defined over a finite ring";
    pi := CosetAction(GL(Degree(H),BaseRing(H)),H);
    return func<g|#Fix(pi(g))>;
end intrinsic;

intrinsic GL2PermutationCharacter(H::GrpMat) -> UserProgram
{ The permutation character given by the GL2-action on the right coset space [H\\GL2]. }
    return GLPermutationCharacter(H);
end intrinsic;

intrinsic GL1Level(H::GrpMat) -> RngIntElt
{ The least integer N such that H is the full inverse image of its reduction modulo N. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1,sub<GL(1,Integers())|>; end if;
    require Degree(H) eq 1 and Type(R) eq RngIntRes: "H must be a sugroup of GL(1,Z/NZ) for some positive integer N.";
    N := #R;
    cH := #H; cGL1 := EulerPhi(N);
    if cH eq cGL1 then return 1,sub<GL(1,Integers())|>; end if;
    if IsPrime(N) then return N,H; end if;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cGL1*#ChangeRing(H,Integers(N div p)) eq EulerPhi(N div p)*cH do N div:= p; end while;
    end for;
    return N,ChangeRing(H,Integers(N));
end intrinsic;

intrinsic GLLift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(n,Z/MZ) of H in GL(n,Z/NZ) for a multiple M of N. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GL(Degree(H),Integers(M)); end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    N := #R;
    require IsDivisibleBy(M,N): "M must be divisible by N for H in GL(n,Z/NZ)";
    GLn:=GL(Degree(H),Integers(M));
    _,pi:=ChangeRing(GLn,R);
    return sub<GLn|Kernel(pi),Inverse(pi)(H)>;
end intrinsic;

intrinsic GL1Lift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(1,Z/MZ) of H in GL(1,Z/NZ) for a multiple M of N. }
    return GLLift(H,M);
end intrinsic;

intrinsic GL2Lift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(2,Z/MZ) of H in GL(2,Z/NZ) for a multiple M of N. }
    return GLLift(H,M);
end intrinsic;

intrinsic GLProject(H::GrpMat,M::RngIntElt) -> GrpMat
{ The projection of the preimage of H in GL(n,Zhat) to GL(n,Z/MZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GL(Degree(H),Integers(M)); end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    N := #R; if N eq M then return H; end if;
    if IsDivisibleBy(N,M) then return ChangeRing(H,Integers(M)); end if;
    return ChangeRing(GLLift(H,LCM(M,N)),Integers(M));
end intrinsic;

intrinsic GL1Project(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(1,Z/MZ) of H in GL(1,Z/NZ) for a multiple M of N. }
    return GLProject(H,M);
end intrinsic;

intrinsic GL2Project(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(2,Z/MZ) of H in GL(2,Z/NZ) for a multiple M of N. }
    return GLProject(H,M);
end intrinsic;

intrinsic GL2FromGenerators(N::RngIntElt,gens::SeqEnum) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle N=1). }
    require N gt 0: "N must be a positive integer";
    return N eq 1 select sub<GL(2,Integers())|> else sub<GL(2,Integers(N))|gens>;
end intrinsic;

intrinsic GL2Generators(H::GrpMat) -> SeqEnum
{ Returns a list of generators of H as a list of 4-tuples of integers. }
    return [Universe([[1]])|[Integers()|a:a in Eltseq(g)]:g in Generators(H)]; 
end intrinsic;

intrinsic GL1Label(H::GrpMat) -> MonStgElt
{ The label N.i.n of the subgroup H of GL(1,Zhat). }
    N := GL1Level(H);
    if N eq 1 then return "1.1.1"; end if;
    H := ChangeRing(H,Integers(N));
    G := GL(1,Integers(N));
    i := Index(G,H);
    S := Sort([GL1Characters(K`subgroup): K in Subgroups(G:IndexEqual:=i) | GL1Level(K`subgroup) eq N]);
    return Sprintf("%o.%o.%o", N, i, Index(S,GL1Characters(H)));
end intrinsic;

intrinsic GL1SubgroupFromLabel(s::MonStgElt) -> GrpMat
{ The subgroup of GL(1,Zhat) with the specified label. }
    if s eq "1.1.1" then return sub<GL(1,Integers())|>; end if;
    r := Split(s,".");
    require #r eq 3: "Invalid label format, expected N.i.n";
    N := StringToInteger(r[1]); i := StringToInteger(r[2]); n := StringToInteger(r[3]);
    G := GL(1,Integers(N));
    S := [H`subgroup : H in Subgroups(G:IndexEqual:=i) | GL1Level(H`subgroup) eq N];
    require n ge 1 and n le #S: "Invalid label N.i.n, the component n exceeds the number of subgroups of level N and index i";
    T := Sort([<GL1Characters(S[i]),i>: i in [1..#S]]);
    return S[T[n][2]];
end intrinsic;

intrinsic GL1Labels(N::RngIntElt) -> SeqEnum[MonStgElt]
{ Sorted list of labels N.i.n of subgroups of GL(1,Z/NZ). }
    if N eq 1 then return ["1.1.1"]; end if;
    G := GL(1,Integers(N));
    X := index([H`subgroup:H in Subgroups(G)],func<H|<GL1Level(H),Index(G,H)>>);
    K := Sort([k:k in Keys(X)]);
    return &cat[[Sprintf("%o.%o.%o",k[1],k[2],n):n in [1..#X[k]]]:k in K];
end intrinsic;

intrinsic GL1CompareLabels(a::MonStgElt,b::MonStgElt) -> RngIntElt
{ Lexicographically compares subgroup labels of GL(1,Zhat) the form N.i.n (N=level, i=index, n=ordinal) as lists of integers.  Returns -1,0,1. }
    if a eq b then return 0; end if; if a eq "?" then return 1; end if; if b eq "?" then return -1; end if;
    r := [StringToInteger(x):x in Split(a,".")]; s := [StringToInteger(x):x in Split(b,".")];
    require #r eq 3: "Invalid GL1-subgroup label";
    return r lt s select -1 else 1;
end intrinsic;

intrinsic GL1SortLabels(L::SeqEnum[MonStgElt]) -> SeqEnum[MonStgElt]
{ Sorts the specified list of labels of subgroups of GL(1,Zhat). }
    L := Sort(L,func<a,b|GL1CompareLabels(a,b)>);
    return L;
end intrinsic;

intrinsic GL2Transpose(H::GrpMat) -> GrpMat
{ Given a subgroup H of GL(n,R) for some ring R returns the transposed subgroup. }
    return sub<GL(Degree(H),BaseRing(H))|[Transpose(g):g in Generators(H)]>;
end intrinsic;

intrinsic SL2Size(N::RngIntElt) -> RngIntElt    // This is much faster than #SL(2,Integers(N))
{ The cardinality of SL(2,Z/NZ). }
    if N eq 1 then return 1; end if;
    P := PrimeDivisors(N);
    return N*(N div &*P)^2*&*[p^2-1:p in P];
end intrinsic;

intrinsic GL2Size(N::RngIntElt) -> RngIntElt
{ The cardinality of GL(2,Z/NZ). }
    return EulerPhi(N)*SL2Size(N);
end intrinsic;

// Note that to deal with the fact that Magma won't let us define GL(2,Integers(1)),
// We represent this group as the trivial subgroup of GL(2,Z) and check for this in the functions below.

intrinsic SL2Index(H::GrpMat) -> RngIntElt
{ Index of H cap SL(2,Z/NZ) in SL(2,Z/NZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    SL2 := SL(2,R);
    if not H subset SL2 then H := H meet SL2; end if;
    return SL2Size(#R) div #H;
end intrinsic;

intrinsic GL2Index(H::GrpMat) -> RngIntElt
{ The index of H in GL(2,Z/NZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    return Index(GL(2,R),H);
end intrinsic;

intrinsic GL2DeterminantImage(H::GrpMat) -> GrpMat
{ det(H) as a subgroup of GL1. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return sub<GL(1,Integers())|>; end if;
    return sub<GL(1,BaseRing(H))|[[Determinant(h)]:h in Generators(H)]>;
end intrinsic;

intrinsic GL2DeterminantIndex(H::GrpMat) -> RngIntElt
{ The index of det(H) in GL1. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    return Index(GL(1,BaseRing(H)),GL2DeterminantImage(H));
end intrinsic;

intrinsic GL2DeterminantLabel(H::GrpMat) -> MonStgElt
{ The label of det(H) as a subgroup of GL(1,Zhat). }
    return GL1Label(GL2DeterminantImage(H));
end intrinsic;

intrinsic GL2DeterminantLabelIndex(H::GrpMat) -> RngIntElt
{ The index of the label of det(H) in the ordered list of labels of subgroups of GL(1,N). }
    s := GL2DeterminantLabel(H);  if s eq "1.1.1" then return 1; end if;
    return Index(GL1Labels(#BaseRing(H)),s);
end intrinsic;

intrinsic GL2ScalarImage(H::GrpMat) -> GrpMat
{ Returns the subgroup of GL1 isomorphic to the scalar subgroup of H. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return sub<GL(1,Integers())|>; end if;
    require Degree(H) eq 2: "H must be a subgroup of GL(2,R) for some ring R.";
    Z1 := GL(1,BaseRing(H));
    Z := H meet sub<GL(2,R)|[[g[1][1],0,0,g[1][1]]:g in Generators(Z1)]>;
    return sub<Z1|[[g[1][1]]:g in Generators(Z)]>;
end intrinsic;

intrinsic GL2ScalarIndex(H::GrpMat) -> RngIntElt
{ The index of (H meet scalars) in H, where H is a subgroup of GL(2,R). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    return Index(GL(1,BaseRing(H)),GL2ScalarImage(H));
end intrinsic;

intrinsic GL2ScalarLabel(H::GrpMat) -> MonStgElt
{ The label of det(H) as a subgroup of GL(1,Zhat). }
    return GL1Label(GL2ScalarImage(H));
end intrinsic;

intrinsic GL2ScalarLabelIndex(H::GrpMat) -> RngIntElt
{ The index of the label of det(H) in the ordered list of labels of subgroups of GL(1,N). }
    s := GL2ScalarLabel(H);  if s eq "1.1.1" then return 1; end if;
    return Index(GL1Labels(#BaseRing(H)),s);
end intrinsic;

// Given a subgroup H of GL(2,Z/nZ), returns true if H contains an element corresponding to complex conjugation
intrinsic GL2ContainsComplexConjugation(H::GrpMat) -> BoolElt
{ True if H contains an element corresponding to complex conjugation (any GL_2-conjugate of [1,0,0,-1] or [1,1,0,-1]). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    cc := [[1,0,0,-1],[-1,0,0,1],[1,-1,0,-1],[1,1,0,-1],[-1,0,1,1],[-1,1,0,1],[-1,0,-1,1],[1,0,1,-1],[-1,-1,0,1],[1,0,-1,-1],[0,-1,-1,0],[0,1,1,0]];
    GL2 := GL(2,R);
    if &or[GL2!c in H:c in cc] then return true; end if;
    if #R ne 2 and not IsEven(#GL(1,R) div GL2DeterminantIndex(H)) then return false; end if;
    Z := Conjugates(GL2,GL2![1,0,0,-1]);
    for z in Z do if z in H then return true; end if; end for;
    if IsOdd(#R) then return false; end if;
    Z := Conjugates(GL2,GL2![1,1,0,-1]);
    for z in Z do if z in H then return true; end if; end for;
    return false;
end intrinsic;

intrinsic GL2ContainsCC(H::GrpMat) -> BoolElt
{ True if H contains an element corresponding to complex conjugation (any GL_2-conjugate of [1,0,0,-1] or [1,1,0,-1]). }
    return GL2ContainsComplexConjugation(H);
end intrinsic;

intrinsic GL2ContainsNegativeOne(H::GrpMat) -> BoolElt
{ True if -I is in H. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return true; end if;
    return -Identity(H) in H;
end intrinsic;

intrinsic GL2Level(H::GrpMat) -> RngIntElt, GrpMat
{ The least integer N such that H is the full inverse image of its reduction modulo N. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1,sub<GL(2,Integers())|>; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    N := #R;
    cH := #H; cGL2 := GL2Size(N);
    if cH eq cGL2 then return 1,sub<GL(2,Integers())|>; end if;
    if IsPrime(N) then return N,H; end if;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cGL2*#ChangeRing(H,Integers(N div p)) eq GL2Size(N div p)*cH do N div:= p; end while;
    end for;
    return N,ChangeRing(H,Integers(N));
end intrinsic;

intrinsic SL2Level(H::GrpMat) -> RngIntElt, GrpMat
{ The least integer N such that H cap SL2 is the full inverse image of its reduction modulo N, along with corresponding subgroup of SL2. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1,sub<SL(2,Integers())|>; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    N := #R;
    SL2 := SL(2,R);
    if not H subset SL2 then
        // Computing the intersection with SL2 is costly enough to make it worth checking the GL2Level first
        N,H := GL2Level(H);  if N eq 1 then return 1,sub<SL(2,Integers())|>; end if;
        if N ne #R then R:=Integers(N); SL2 := SL(2,R); end if;
        H := SL2 meet H;
    end if;
    cH := #H; cSL2 := SL2Size(N);
    if cH eq cSL2 then return 1,_; end if;
    if IsPrime(N) then return N,H; end if;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cSL2*#ChangeRing(H,Integers(N div p)) eq SL2Size(N div p)*cH do N div:= p; end while;
    end for;
    return N,ChangeRing(H,Integers(N));
end intrinsic;

intrinsic GL2CuspCount(H::GrpMat) -> RngIntElt
{ The number of cusps of X_H over C. }
    N,H := SL2Level(H);
    if N eq 1 then return 1; end if;
    SL2 := SL(2,Integers(N));
    H := sub<SL2|H,[-1,0,0,-1]>;
    pi := CosetAction(SL2,H);
    T:=sub<SL2|[1,1,0,1]>;
    return #Orbits(pi(T));
end intrinsic;

intrinsic GL2RationalCuspCount(H::GrpMat) -> RngIntElt
{ The number of Q-rational cusps of X_H. }
    N,H := GL2Level(H);
    if N eq 1 then return 1; end if;
    GL2 := GL(2,Integers(N));
    if not -Identity(H) in H then H := sub<GL2|H,[-1,0,0,-1]>; end if;
    pi := CosetAction(GL2,H);
    O := Orbits(pi(sub<GL2|[1,1,0,1]>));
    GL1 := GL(1,Integers(N));
    B := pi(sub<GL2|[[g[1][1],0,0,1]:g in Generators(GL1)]>);
    return #{o:o in O|o^B eq {o}};
end intrinsic;

intrinsic GL2RationalCuspCount(H::GrpMat, q::RngIntElt) -> RngIntElt
{ The number of Fq-rational cusps of the reduction of X_H to the finite field F_q (where q is coprime to the level of H). }
    N,H := GL2Level(H);
    if N eq 1 then return 1; end if;
    require GCD(q,N) eq 1: "q must be coprime to the level of H.";
    GL2 := GL(2,Integers(N));
    if not -Identity(H) in H then H := sub<GL2|H,[-1,0,0,-1]>; end if;
    pi := CosetAction(GL2,H);
    O := Orbits(pi(sub<GL2|[1,1,0,1]>));
    B := pi(sub<GL2|[q,0,0,1]>);
    return #{o:o in O|o^B eq {o}};
end intrinsic;

intrinsic GL2RationalCuspCounts(H::GrpMat) -> SeqEnum[RngIntElt]
{ Returns an array integers whose (q mod N)th entry is the number of cusps of X_H mod q for q coprime to N=level(H) and -1 otherwise. }
    N,H := GL2Level(H);
    GL2 := GL(2,Integers(N));
    if not -Identity(H) in H then H := sub<GL2|H,[-1,0,0,-1]>; end if;
    pi := CosetAction(GL2,H);
    O := Orbits(pi(sub<GL2|[1,1,0,1]>));
    C := [-1:q in [1..N]];
    for q in [1..N] do
        if C[q] lt 0 and GCD(q,N) eq 1 then
            B := sub<GL2|[q,0,0,1]>;
            c := #{o:o in O|o^pi(B) eq {o}};
            for b in B do if Order(b[1][1]) eq #B then C[Integers()!b[1][1]] := c; end if; end for;
        end if;
    end for;
    return C;
end intrinsic;

intrinsic GL2Genus(H::GrpMat) -> RngIntElt
{ The genus of the modular curve X_H for H in GL(2,Z/NZ). }
    N,H := SL2Level(H);
    if N le 5 then return 0; end if;
    SL2 := SL(2,Integers(N));
    if not -Identity(H) in H then H := sub<SL2|H,-Identity(H)>; end if;
    pi := CosetAction(SL2,H);
    n2 := #Fix(pi(SL2![0,1,-1,0]));
    n3 := #Fix(pi(SL2![0,1,-1,-1]));
    c := #Orbits(pi(sub<SL2|[1,1,0,1]>));
    return Integers()!(1 + Index(SL2,H)/12 - n2/4  - n3/3 - c/2);
end intrinsic;

intrinsic GL2SplitCartan(R::Rng) -> GrpMat
{ The standard split Cartan subgroup of GL(2,R), equivalently, the subgroup of diagonal matrices in GL(2,R). }
    GL1 := GL(1,R);
    gens := [g[1][1] : g in GL1];
    return sub<GL(2,R) | [[g,0,0,1] : g in gens] cat [[1,0,0,g] : g in gens]>;
end intrinsic;

intrinsic GL2SplitCartan(N::RngIntElt) -> GrpMat
{ The standard split Cartan subgroup of GL(2,Z/NZ), equivalently, the subgroup of diagonal matrices in GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2SplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2NormalizerSplitCartan(R::Rng) -> GrpMat
{ The normalizer of the standard split Cartan subgroup of GL(2,R). }
    return Normalizer(GL(2,R),GL2SplitCartan(R));
end intrinsic;

intrinsic GL2NormalizerSplitCartan(N::RngIntElt) -> GrpMat
{ The normalizer of the standard split Cartan subgroup of GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2NormalizerSplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

// Non-split Cartan -- isomorphic to (OK/N*OK)* where OK is a quadratic order of discriminant prime to N with every p|N inert in OK
// See Baran https://core.ac.uk/download/pdf/82651427.pdf for details
// This implementation uses brute force subgroup enumeration, it will be very slow if N is large
intrinsic GL2NonsplitCartan(R::RngIntRes) -> GrpMat
{ A non-split Cartan subgroup of GL(2,Z/NZ) (isomorphic to OK/N*OK where OK is a quadratic order of discriminant prime to N with every p|N inert in OK). }
    N := #R;  P := PrimeDivisors(N);  M := (N div &*P)^2*&*[p^2-1:p in P];
    S := [H`subgroup : H in Subgroups(GL(2,R):IsAbelian:=true,OrderEqual:=M)];
    if M eq 1 then return S[1]; end if;    // this already handles prime powers and odd N up to 151
    // Construct a suitable Z/NZ algebra using a quadratic order R of discriminant prime to N in which ever p|N is inert
    D := -163;  while not &and[KroneckerSymbol(D,p) eq -1 : p in P] do N -:= 4; end while;
    OK := RingOfIntegers(QuadraticField(D));
    I := Invariants(UnitGroup(quo<OK|N*OK>));
    S := [H : H in S | Invariants(H) eq I];
    assert #S eq 1;
    return S[1];
end intrinsic;

intrinsic GL2NonsplitCartan(N::RngIntElt) -> GrpMat
{ A non-split Cartan subgroup of GL(2,Z/NZ) (isomorphic to OK/N*OK where OK is a quadratic order of discriminant prime to N with every p|N inert in OK). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2NonsplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2NormalizerNonsplitCartan(R::RngIntRes) -> GrpMat
{ The normalizer of a non-split Cartan subgroup of GL(2,Z/NZ). }
    return Normalizer(GL(2,R),GL2NonsplitCartan(R));
end intrinsic;

intrinsic GL2NormalizerNonsplitCartan(N::RngIntElt) -> GrpMat
{ The normalizer of a non-split Cartan subgroup of GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2NormalizerNonsplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

// Borel group -- upper triangular matrices in GL(2,Z/nZ) -- E admits a rational n-isogeny if and only if \im\rho_{E,n} is conjugate to a subgroup of  the Borel
intrinsic GL2Borel(R::Rng) -> GrpMat
{ The standard Borel subgroup of GL(2,R), equivalently, the subgroup of upper triangular matrices in GL(2,R). }
    return sub<GL(2,R) | [1,1,0,1], GL2SplitCartan(R)>;
end intrinsic;

intrinsic GL2Borel(N::RngIntElt) -> GrpMat
{ The standard Borel subgroup of GL(2,Z/NZ), equivalently, the subgroup of upper triangular matrices in GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2Borel(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2Borel1(R::Rng) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,R) that a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    GL1 := GL(1,R);
    return sub<GL(2,R) | [1,1,0,1], [[1,0,0,g[1][1]] : g in Generators(GL1)]>;
end intrinsic;

intrinsic GL2Borel1(N::RngIntElt) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,Z/NZ) that a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2Borel1(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2ProjectiveImage(H::GrpMat) -> GrpPerm
{ The image of the subgroup H of GL(2,Z/NZ) in PGL(2,Z/NZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return SymmetricGroup(1); end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    _,pi:=quo<GL(2,R)|Center(GL(2,R))>;
    return pi(H);
end intrinsic;

// Given a subgroup G of GL(2,p^2) that is conjugate to a subgroup H of GL(2,p), returns such an H, using the algorithm in Glasby and Howlett (Writing representations over minimal fields, Comm. Alg. 25 (1997), 1703-1711).
function ConjugateToRationalSubgroup(G)
    local F,p,r,x,C,mu,R,v,X,A,H;
    F:=BaseRing(G);  assert IsFinite(F) and IsField(F);
    if Degree(F) eq 1 then return G; end if;
    assert Degree(F) eq 2;
    p:=Characteristic(F);
    MatFrob := func<A|Parent(A)![A[1][1]^p,A[1][2]^p,A[2][1]^p,A[2][2]^p]>;
    r := [];
    for g in Generators(G) do
        r:=Append(r,[g[1][1]-g[1][1]^p,-g[2][1]^p,g[1][2],0]);
        r:=Append(r,[-g[1][2]^p,g[1][1]-g[2][2]^p,0,g[1][2]]);
        r:=Append(r,[g[2][1],0,g[2][2]-g[1][1]^p,-g[2][1]^p]);
        r:=Append(r,[0,g[2][1],-g[1][2]^p,g[2][2]-g[2][2]^p]);
    end for;
    while true do
        x:=Random(NullspaceOfTranspose(Matrix(r)));
        C:=MatrixRing(F,2)![x[i]:i in [1..Degree(x)]];
        if IsInvertible(C) then C:=GL(2,F)!C; break; end if;
    end while;
    for g in Generators(G) do if C^-1*g*C ne MatFrob(g) then print C, g; assert false; end if; end for;
    mu := C*MatFrob(C);
    assert mu[1][1] eq mu[2][2] and mu[1][2] eq 0 and mu[2][1] eq 0;
    mu := GF(p)!mu[1][1];
    b,v:=NormEquation(F,mu);
    C:=GL(2,F)![1/v,0,0,1/v]*C;
    assert C*MatFrob(C) eq Identity(G);
    while true do
        X:=Random(MatrixRing(F,2));
        A:=X+C*MatFrob(X);
        if not IsInvertible(A) then continue; end if;
        A:=GL(2,F)!A;
        H:=Conjugate(G,A);
        for h in Generators(H) do assert MatFrob(h) eq h; end for;
        return sub<GL(2,p)|Generators(H)>;
    end while;
end function;

// Based on Thm 5.5 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalA4(p::RngIntElt) -> GrpMat[RngIntRes]
{ The largest subgroup of GL(2,Z/pZ) with projective image A4 (it will necessarily have determinant index 2). }
    require IsPrime(p) and p ge 5: "p must be a prime greater than 3.";
    F := p mod 4 eq 1 select GF(p) else GF(p^2);  G:=GL(2,F);
    w:=RootOfUnity(4,F); z:=F!PrimitiveRoot(p);
    H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[w,0,0,-w],[z,0,0,z]>);
    return ChangeRing(H,Integers(p));
end intrinsic;

// Based on Thm 5.8 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalS4(p::RngIntElt) -> GrpMat[RngIntRes]
{ The largest subgroup of GL(2,Z/pZ) with projective image S4 (it will necessarily have determinant index 2 for p=1,7 mod 8). }
    require IsPrime(p) and p ge 5: "p must be a prime greater than 3.";
    a := (p mod 8 in [1,7]) select 1 else 2;
    F:=GF(p^2);  G:=GL(2,F);
    w:=RootOfUnity(4,F);  c:=Sqrt(F!2); t:=G![(1+w)/c,0,0,(1-w)/c];  z:=F!PrimitiveRoot(p);
    if a eq 1 then
        H:=ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[(1+w)/c,0,0,(1-w)/c],[z,0,0,z]>);
    elif p mod 8 eq 1 then
        H:=ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[z*(1+w)/c,0,0,z*(1-w)/c],[z^2,0,0,z^2]>);
    else
        H:=ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[u*(1+w)/c,0,0,u*(1-w)/c],[z,0,0,z]>) where u:=Sqrt(z);
    end if;
    return ChangeRing(H,Integers(p));
end intrinsic;

// Based on Thm 5.11 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalA5(p::RngIntElt) -> GrpMat[RngIntRes]
{ For a prime p = +/-1 mod 5, the largest subgroup of GL(2,Z/pZ) with projective image A5 (it will necessarily have determinant index 2). }
    require IsPrime(p) and p mod 5 in [1,4]: "p must be a prime congruent to +/-1 mod 5.";
    F:=GF(p^2);  G:=GL(2,F);
    w:=RootOfUnity(4,F); b := Sqrt(F!5); z:=F!PrimitiveRoot(p);
    H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[w,0,0,-w],[w/2,(1-b)/4-w*(1+b)/4,(-1+b)/4-w*(1+b)/4,-w/2],[z,0,0,z]>);
    return ChangeRing(H,Integers(p));
end intrinsic;

intrinsic GL2MinimizeGenerators(G::Grp) -> Grp
{ Attempts to minimize the number of generators of a finite group by sampling random elements.  Result is not guaranteed to be optimal unless G is abelian (but it very likely will be optimal or very close to it, see https://doi.org/10.1016/S0021-8693(02)00528-8). }
    require IsFinite(G): "G must be a finite group";
    n := #G;
    if IsAbelian(G) then Gab,pi := AbelianGroup(G); B := AbelianBasis(Gab); return sub<G|[Inverse(pi)(b):b in B]>; end if;
    r := 2;
    while true do
        for i:=1 to 100 do H := sub<G|[Random(G):i in [1..r]]>; if #H eq n then return H; end if; end for;
        r +:= 1;
    end while;
end intrinsic;

intrinsic GL2Standardize(H::GrpMat) -> GrpMat
{ Given a subgroup of GL(2,Z/NZ) attempts to conjugate to a nice form (e.g. diagonal or upper triangular).  Ths can be very slow, use with caution. }
    require Degree(H) eq 2: "H should be a subgroup of GL(2,R) for some finite ring R.";
    function IsDiagonal(A) return A[1][2] eq 0 and A[2][1] eq 0; end function;
    function IsDiagonalOrAntiDiagonal(A) return (A[1][2] eq 0 and A[2][1] eq 0) or (A[1][1] eq 0 and A[2][2] eq 0); end function;
    function IsUpperTriangular(A) return A[2][1] eq 0; end function;
    function IsZDiagonal(A) return A[1][1] eq A[2][2]; end function;
    function IsZDiagonalorNZDiagonal(A) return A[1][1] eq A[2][2] or A[1][1] eq -A[2][2]; end function;
    C := [K:K in Conjugates(GL(2,BaseRing(H)),H)];
    for K in C do if &and[IsDiagonal(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsUpperTriangular(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsDiagonalOrAntiDiagonal(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsZDiagonal(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsZDiagonalorNZDiagonal(h):h in Generators(K)] then return K; end if; end for;
    return Sort(C,func<a,b|&+[#[c:c in Eltseq(g)|c eq 0]:g in Generators(b)] - &+[#[c:c in Eltseq(g)|c eq 0]:g in Generators(a)]>)[1];
end intrinsic;

// Magma wants matrices to act on row vectors from the right, so when computing orbits we transpose
// to remain consistent with our convention that matrices act on column vectors from the left.

intrinsic GL2OrbitSignature(H::GrpMat:N:=0) -> SeqEnum[SeqEnum[RngIntElt]]
{ The orbit signature of H (the ordered list of triples [e,s,m] where m is the number of non-trivial left H-orbits of (Z/NZ)^2 of size s and exponent e). }
    if N eq 0 then N,H := GL2Level(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return [Universe([[1]])|]; end if;
    H := GL2Transpose(H);
    D := Divisors(N);
    function ord(v) return Min([n:n in D|n*v eq 0*v]); end function;
    return lmset({*[ord(o[1]),#o]:o in Orbits(H)|o ne {RSpace(H)!0}*});
end intrinsic;

intrinsic GL2KummerSignature(H::GrpMat:N:=0) -> SeqEnum[SeqEnum[RngIntElt]]
{ The divpoly signature of H (the ordered list of triples [e,s,m] where m is the number of left H-orbits of (Z/NZ)^2/<-1> of size s and exponent e, giving the factorization pattern of the N-division polynomial.). }
    if N eq 0 then N,H := GL2Level(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return [Universe([[1]])|]; end if;
    H := GL2Transpose(sub<GL(2,BaseRing(H))|H,-Identity(H)>);
    D := Divisors(N);
    function ord(v) return Min([n:n in D|n*v eq 0*v]); end function;
    return lmset({*[ord(o[1]),ExactQuotient(#o,#{o[1],-o[1]})]:o in Orbits(H)|o ne {RSpace(H)!0}*});
end intrinsic;

intrinsic GL2TorsionDegree (H::GrpMat:N:=0) -> RngIntElt
{ The minimal size of a left H-orbit of (Z/NZ)^2 of exponent N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational point of order N). }
    if N eq 0 then N,H := GL2Level(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return 1; end if;
    O := GL2OrbitSignature(H:N:=N);  d := Min([r[2]:r in O|r[1] eq N]); return d;
end intrinsic;

intrinsic GL2IsogenySignature(H::GrpMat:N:=0) -> SeqEnum[SeqEnum[RngIntElt]]
{ The isogeny signature of the subgroup H of GL(2,Z/NZ) (the ordered list of triples [e,s,m] where m is the number of left H-orbits of cyclic submodules of (Z/NZ)^2 of size s and degree e). }
    if N eq 0 then N,H := GL2Level(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return []; end if;
    H := GL2Transpose(H);
    S := {sub<RSpace(H)|[i,j]>:i in Divisors(N),j in [0..N-1]};
    X := {* [#v,#(v^H)] : v in S*};
    return Sort([r cat [ExactQuotient(Multiplicity(X,r),r[2])]: r in Set(X) | r[1] ne 1]);
end intrinsic;

intrinsic GL2IsogenyDegree (H::GrpMat:N:=0) -> RngIntElt
{ The minimal size of a left H-orbit of a cyclic submodule of (Z/NZ)^2 of degree N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational cyclic isogeny of degree N). }
    if N eq 0 then N,H := GL2Level(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return 1; end if;
    O := GL2IsogenySignature(H:N:=N);  d := Min([r[2]:r in O|r[1] eq N]);  return d;
end intrinsic;

intrinsic M2SimilarityInvariant(M::AlgMatElt[RngIntRes]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Given a 2-by-2 matrix over Z/NZ returns a list of lists of integers the uniquely identifies the similarity class of M. }
    require NumberOfRows(M) eq 2 and Type(BaseRing(M)) eq RngIntRes: "M must be a 2x2 matrix over Z/NZ for some N > 1";
    N := #BaseRing(M);
    Z := Integers();
    scalar := func<M|M[1][1] eq M[2][2] and M[1][2] eq 0 and M[2][1] eq 0>;
    S := [];
    for a in Factorization(N) do
        p := a[1]; e := a[2];
        A := ChangeRing(M,Integers(p^e));
        j := Max([j:j in [0..e] | j eq 0 or scalar(ChangeRing(A,Integers(p^j)))]);
        if j eq 0 then S cat:= [[Integers()|p^e,Determinant(A),Trace(A),0,0,0,0]]; continue; end if;
        if j eq e then S cat:= [[Integers()|p^e,Determinant(A),Trace(A),e,A[1][1],0,0]]; continue; end if;
        q := p^j; M := MatrixRing(Integers(p^(e-j)),2);
        d := (Z!A[1][1]) mod q;
        B := M![(Z!A[1][1]-d) div q, Z!A[1][2] div q, Z!A[2][1] div q, (Z!A[2][2]-d) div q];
        S cat:= [[Integers()|p^e,Determinant(A),Trace(A),j,d,Determinant(B),Trace(B)]];
    end for;
    return S;
end intrinsic;

intrinsic GL2SimilarityInvariant(M::GrpMatElt[RngIntRes]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Given a matrix in GL(2,Z/NZ) returns a list of lists of integers the uniquely identifies its similarity/conjugacy class. }
    return M2SimilarityInvariant(MatrixRing(BaseRing(M),Degree(M))!M);
end intrinsic;

intrinsic GL2SimilaritySet(H::GrpMat) -> SeqEnum[Tup]
{ Set of similarity invariants arising in H. }
    if Type(BaseRing(H)) ne RngIntRes then return {[]}; end if;
    return { GL2SimilarityInvariant(c[3]): c in ConjugacyClasses(H) };
end intrinsic;

intrinsic GL2SimilarityMultiset(H::GrpMat) -> SeqEnum[Tup]
{ Set of similarity invariants arising in H. }
    return {* GL2SimilarityInvariant(c[3])^^c[2]: c in ConjugacyClasses(H) *};
end intrinsic;

intrinsic GL2ClassSignature(H::GrpMat:N:=0) -> SeqEnum[Tup]
{ The class signature of H (the ordered list of 5-tuples (o,d,t,s,m) where m is the number of conjugacy classes of elements of H of size s, order o, determinant d, trace t. }
    if N eq 0 then N,H := GL2Level(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return []; end if;
    function csig(c) return [c[1],Integers()!Determinant(c[3]),Integers()!Trace(c[3]),c[2]]; end function;
    C := ConjugacyClasses(H);
    S := {* csig(c) : c in C *};
    return Sort([r cat [Multiplicity(S,r)]:r in S]);
end intrinsic;

intrinsic GL2GassmannSignature(H::GrpMat:N:=0) -> SeqEnum[Tup]
{ Sorted list of pairs <r,m> where r is a similarity invariant of GL_2(N) and m > 0 is its multiplicity in H; this uniquely identifies the Gassmann equivalence class of H as a subgroup of GL_2(N). }
    if N eq 0 then N,H := GL2Level(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return []; end if;
    S := {* GL2SimilarityInvariant(c[3])^^c[2] : c in ConjugacyClasses(H) *};
    return Sort([<r,Multiplicity(S,r)>:r in Set(S)]);
end intrinsic;

intrinsic GL2QuadraticTwists(H::GrpMat:IncludeSelf:=false) -> SeqEnum[GrpMat]
{ Given a subgroup H of GL(2,Z/NZ), returns the list of subgroups K of GL(2,Z/NZ) for which <H,-I> = <K,-I> (H is not included unless IncludeSelf is set to true). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return IncludeSelf select [H] else []; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    I := Identity(H);  nI := -I;
    if I eq nI then return [H]; end if;
    G := nI in H select H else sub<GL(2,R)|H,nI>;
    S := [K`subgroup:K in Subgroups(H:IndexEqual:=2)|not nI in K`subgroup];
    if G ne H and not IncludeSelf then S := [K:K in S| not IsConjugate(G,H,K)]; end if;
    if #S gt 1 then
        GL2 := GL(2,R);
        X := index(S,func<H|GL2OrbitSignature(H)>);
        for k in Keys(X) do X[k] := [X[k][i]:i in [1..#X[k]]|&and[not IsConjugate(GL2,X[k][i],X[k][j]):j in [1..i-1]]]; end for;
        S := &cat[X[k]:k in Keys(X)];
    end if;
    S := ((IncludeSelf or G ne H) select [G] else []) cat S;
    return S;
end intrinsic;

intrinsic GL2GenericQuadraticTwist(H::GrpMat) -> GrpMat
{ Returns the group <H,-I>. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return H; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    return sub<GL(2,BaseRing(H))|H,-Identity(H)>;
end intrinsic;

intrinsic GL2MinimalConjugate(H::GrpMat) -> GrpMat
{ The lexicographically minimal conjugate of H in GL(2,Z/NZ), where N is the level of H.  This is expensive to compute, use sparingly! }
    N := GL2Level(H);
    if N eq 1 then return sub<GL(2,Integers())|>; end if;
    R := Integers(N);
    H := ChangeRing(H,R);
    GL2 := GL(2,R);
    S := Conjugates(GL2,H);
    h := GL2![0,1,1,0];
    T := [H:H in S|h in H];
    if #T gt 0 then S := T; else h := GL2![0,1,1,1]; T := [H:H in S|h in H]; if #T gt 0 then S := T; end if; end if;
    if #S eq 1 then return Sort([Eltseq(h):h in S[1]]); end if;
    return Min([Sort([Eltseq(h):h in K]):K in S]);
end intrinsic;

// This section consists of point-counting helper functions which are not part of the external interface

// returns a table whose (-D)th entry is h(-D), using cached data xgclassnumbers.dat if present (will create if not)
function ClassNumberTable(N)
    try
        fp := Open("xgclassnumbers.dat","r");
        htab := ReadObject(fp);
    catch e
        htab := [];
    end try;
    N := Abs(N);
    if #htab lt N then 
        htab := [d mod 4 in [0,3] select ClassNumber(-d) else 0 : d in [1..N]];
        fp := Open("xgclassnumbers.dat","w");
        WriteObject(fp,htab);
        delete fp;
    end if;
    fp := Open("xgclassnumbers.dat","r");
    htab := ReadObject(fp);
    return htab[1..N];    
end function;

function GetClassNumber(htab,D) return -D le #htab select htab[-D] else ClassNumber(D); end function;

// Use Cornacchia's algorithm to solve x^2 + dy^2 = m for (x,y) with x,y > 0
function norm_equation(d,m)
    if not IsSquare(m) then
        c,a,b := NormEquation(d,m);
        if not c then return false,_,_; else return c,a,b;  end if;
    end if;
    t,r1 := IsSquare(Integers(m)!-d);
    if not t then return false,_,_; end if;
    r1 := Integers()!r1;
    if 2*r1 gt m then r1 := m-r1; end if;
    r0 := m;
    while r1^2 ge m do s := r0 mod r1; r0:= r1;  r1:= s; end while;
    t,s := IsSquare((m-r1^2) div d);
    if not t then return false,_,_; end if;
    return t,r1,s;
end function;

// Apply Theorem 2.1 of Duke and Toth, given a,b,D satisfying that 4q=a^2-b^2D, where a is the trace of the Frobenius endomorphism pi,
// D is the discriminant of Rpi := End(E) cap Q[pi], and b is the index of Z[pi] in Rpi unless Z[pi]=Z in which case D=1 and b=0
// see https://arxiv.org/abs/math/0103151
// returns a list of integers representing an element of GL_2(Z) with trace a and determinant q representing action of Frob (up to conj)
function FrobMat(a,b,D)
    // assert (b gt 0 and D lt 0 and IsDiscriminant(D)) or (b eq 0 an dD eq 1);
    return [(a+b*d) div 2, b, b*(D-d) div 4, (a-b*d) div 2] where d := D mod 2;
end function;

function IsHCPRoot(D,j)  // returns true if j is a root of H_D(x), attempts to use Weber polys when possible
    if D mod 8 eq 5 then return Evaluate(HilbertClassPolynomial(D),j) eq 0; end if;
    F := Parent(j);
    H,f := WeberClassPolynomial(D);
    return Degree(GCD(ChangeRing(Denominator(f),F)*j - ChangeRing(Numerator(f),F), ChangeRing(H,F))) gt 0;
end function;

/* The function below is a test harness for GL2FrobeniusMatrix, use Test(q,func<x|GL2FrobeniusMatrix(E)>) to test it on every elliptic curve E/Fq
function Test(q,f)
    sts := true;
    for j in GF(q) do
        E := EllipticCurveFromjInvariant(j);
        for e in Twists(E) do
            A:=f(e);
            if Trace(A) ne Trace(e) then printf "Trace mismatch %o != %o for elliptic curve E=%o over F_%o with j(E)=%o\n", Trace(A), Trace(e), Coefficients(e), q, jInvariant(e); sts:= false; end if;
            if Determinant(A) ne q then printf "Determinant mismatch %o != %o for elliptic curve E=%o over F_%o with j(E)=%o\n", Determinant(A), q, Coefficients(e), q, jInvariant(e); sts:= false; end if;
            D := A[1][2] eq 0 select 1 else (4*A[2][1]+A[1][1]-A[2][2]) div A[1][2];
            if D eq 1 then
                assert Trace(A)^2 eq 4*q;
            else
                if not IsHCPRoot(D,j) then printf "Endomorphism ring mismatch D=%o is incorrect for elliptic curve E=%o over F_%o with j(E)=%o and trace t=%o\n", D, Coefficients(e), q, jInvariant(e), TraceOfFrobenius(e); sts:= false; end if;
            end if;
        end for;
    end for;
    return sts;
end function;
*/

/* From Section 4.1 of Kohel's thesis, complexity is O(M(ell^2*log(q))*log(q)) but slower in the range of interest than using Atkin modular polynomials
function OnFloorSlow(E,t,v,D0,ell)
    if v mod ell ne 0 then return true; end if;
    if ell eq 2 then return #TwoTorsionSubgroup(E) lt 4; end if;
    a := D0 mod 4 eq 1 select (t+v) div 2 else t div 2;
    a := a mod ell;
    assert a ne 0;
    psi := DivisionPolynomial(E,ell);
    R<x> := quo<PolynomialRing(BaseRing(E))|psi>;
    if IsEven(a) then a := ell-a; end if; // for convenience
    psia := R!DivisionPolynomial(E,a);
    phia := (x*psia^2 - (R!f1)*(R!f2)*R!F) where _,f1,F := DivisionPolynomial(E,a-1) where _,f2 := DivisionPolynomial(E,a+1);
    q := #BaseRing(E);
    return (x^q*psia^2-phia) ne 0;
end function;
*/

function OnFloor(E,ell)
    if ell eq 2 then return #TwoTorsionSubgroup(E) lt 4; end if;
    return &+[r[2]:r in Roots(Evaluate(AtkinModularPolynomial(ell),[PolynomialRing(BaseRing(E)).1,jInvariant(E)]))] le ell;
end function;

function HeightAboveFloor(E,t,v,D0,ell,h)
    // assumes j(E) != 0,1728 and E is ordinary
    if h eq 0 then return 0; end if;
    s := OnFloor(E,ell) select 0 else 1;
    if h le 1 or s eq 0 then return s; end if;
    j := jInvariant(E);
    R<x> := PolynomialRing(Parent(j));
    R2<X,Y> := PolynomialRing(Parent(j),2);
    phi := Evaluate(ClassicalModularPolynomial(ell),[X,Y]);
    j1 := Roots(Evaluate(phi,[j,x]));
    if #j1 ne ell+1 then return h; end if; // double roots can only happen at the surface
    if #j1 lt 3 then return 0; end if;
    j0 := [j,j,j]; j1 := [j1[i][1]:i in [1..3]];
    h := 1;
    while true do
        for i:=1 to 3 do
            r := Roots(ExactQuotient(Evaluate(phi,[j1[i],x]),x-j0[i]));
            if #r eq 0 then return h; end if;
            j0[i] := j1[i];  j1[i] := r[1][1];
        end for;
        h +:= 1;
    end while;
end function;

// returns j0, d where j0 is j-invariant on surface above j and d is the distance from j to j0
function ClimbToSurface(j,ell,h)
    if h eq 0 then return j, 0; end if;
    if j eq 0 or j eq 1728 then return j,0; end if;
    R<x> := PolynomialRing(Parent(j));
    R2<X,Y> := PolynomialRing(Parent(j),2);
    phi := Evaluate(ClassicalModularPolynomial(ell),[X,Y]);
    jj := Roots(Evaluate(phi,[j,x]));
    if &or[r[2] gt 1 : r in jj] or j in {r[1]:r in jj} then return j, 0; end if; // double roots can only happen at the surface
    if h eq 1 then if #jj eq 1 then return jj[1][1], 1; else return j, 0; end if; end if;
    jj := [r[1] : r in jj]; j0 := [j : r in jj]; j1 := jj;
    e := 0; i := 1;
    while #j1 gt 1 do
        e +:= 1;
        j2 := [[r[1] : r in Roots(ExactQuotient(Evaluate(phi,[j1[i],x]),x-j0[i]))] : i in [1..ell+1]];
        if [] in j2 then
            ii := [n : n in [1..#j2] | j2[n] ne []];
            if #ii eq 0 then return j, 0; end if; // if we hit the floor simultaneously on every path we must have started on the surface
            i := ii[1]; break;
        end if;
        j0 := j1; j1 := [r[1] : r in j2];
    end while;
    if e eq h then return j, 0; end if;
    xj := j; j := jj[i]; d := 1; e +:= 1; // e is height of j above floor
    function walk(phi,nj,xj,n)
        for i:=1 to n do r := Roots(ExactQuotient(Evaluate(phi,[nj,x]),x-xj)); if #r eq 0 then return false; end if; xj:=nj; nj:=r[1][1]; end for;
        return true;
    end function;
    while e lt h do
        assert j ne 0 and j ne 1728;
        nj := [r[1]:r in Roots(ExactQuotient(Evaluate(phi,[j,x]),x-xj))];  assert #nj eq ell;
        i := 1; while i le ell and not walk(phi,nj[i],j,e+1) do i +:= 1; end while;
        xj := j; j := nj[i]; d +:= 1; e +:= 1;
    end while;
    return j,d;
end function;

intrinsic EndomorphismRingData(E::CrvEll[FldFin]) -> RngIntElt, RngIntElt
{ Given an elliptic curve E/Fq returns integers t, D, where t is the trace of the Frobenius endomorphism pi, D is the discriminant of the ring End(E) cap Q(pi). }
    q := #BaseRing(E);  _,p,e := IsPrimePower(q);
    t := TraceOfFrobenius(E);
    j := jInvariant(E);
    if j eq 0 and p ne 2 then
        return t, [-4*p,-4,t^2 eq 4*q select 1 else -3,0,0,1][#AutomorphismGroup(E) div 2];
    elif j eq 1728 then
        return t, [#TwoTorsionSubgroup(E) eq 4 select -p else -4*p,t^2 eq 4*q select 1 else -4,-3,0,0,0,0,0,0,0,0,1][#AutomorphismGroup(E) div 2];
    elif t mod p eq 0 then
        return t, t^2 eq 4*q select 1 else (#TwoTorsionSubgroup(E) eq 4 select -p else -4*p);
    end if;
    // If we get here E is ordinary and j(E) != 0,1728 
    D := t^2 - 4*q;  D0 := FundamentalDiscriminant(D); _,v := IsSquare(D div D0);
    if v eq 1 then return t, D; end if;
    if IsPrime(v) then return t, v gt 400 or 16*v gt Abs(D0) select (IsHCPRoot(D0,j) select D0 else D) else (OnFloor(E,v) select D else D0); end if;
    L := Factorization(v);
    if &and[ell[2] le 1 : ell in L | ell[1] gt 60] and L[#L][1] le 400 then
        return t, D div (b*b) where b := &*[ell[1]^HeightAboveFloor(E,t,v,D0,ell[1],ell[2]) : ell in L];
    end if;
    u := 1; w := v;
    for ell in L do if ell[1] lt 60 then j,d := ClimbToSurface(j,ell[1],ell[2]); u *:= ell[1]^d; w div:=ell[1]^ell[2]; end if; end for;
    for uu in Prune(Divisors(w)) do if IsHCPRoot(uu^2*D0,j) then return t, uu^2*u^2*D0; end if; end for;
    return t, u^2*w^2*D0;
end intrinsic;

intrinsic GL2FrobeniusMatrix(E::CrvEll[FldFin]) -> AlgMatElt[RngInt]
{ Given an elliptic curve E/Fq returns a 2-by-2 integer matrix whose reduction modulo any integer N coprime to q gives the action of Frobenius on E[N] with respect to some basis. }
    a, D := EndomorphismRingData(E);
    M := MatrixRing(Integers(),2);
    if D eq 1 then return M!FrobMat(a,0,1); end if;
    return M!FrobMat(a,b,D) where _,b := IsSquare((a^2-4*#BaseRing(E)) div D);
end intrinsic;

intrinsic FrobeniusMatrix(E::CrvEll[FldFin]) -> AlgMatElt[RngInt]
{ Given an elliptic curve E/Fq returns a 2-by-2 integer matrix whose reduction modulo any integer N coprime to q gives the action of Frobenius on E[N] with respect to some basis. }
    return GL2FrobeniusMatrix(E);
end intrinsic;

intrinsic GL2FrobeniusMatrix(E::CrvEll[FldRat], p::RngIntElt) -> AlgMatElt[RngInt]
{ Given an elliptic curve E/Q and a prime p returns a 2-by-2 integer matrix whose reduction modulo any integer N coprime to p gives the action of Frobenius on (E mod p)[N] with respect to some basis. }
    return GL2FrobeniusMatrix(ChangeRing(E,GF(p)));
end intrinsic;

intrinsic GL2FrobeniusMatrices(E::CrvEll[FldRat], B::RngIntElt:B0:=1) -> AlgMatElt[RngInt]
{ Given an elliptic curve E/Q and a bound B returns a list of 2-by-2 integer matrices A of determinant p (for primes p <= B of good reduction) whose reduction modulo any integer N coprime to det(A) gives the action of Frobenius on (E mod p)[N] with respect to some basis. }
    E := MinimalModel(E); D := Integers()!Discriminant(E);
    return [GL2FrobeniusMatrix(ChangeRing(E,GF(p))) : p in PrimesInInterval(B0,B) | D mod p ne 0];
end intrinsic;

intrinsic GL2nTorsionFrobenius(E::CrvEll[FldFin], n::RngIntElt) -> AlgMatElt[RngIntRes]
{Given an elliptic curve E over a finite field and an integer n, it returns the matrix describing the actin of Frobenius in ZZ/nZZ.}
    require n gt 1 and GCD(#BaseRing(E),n) eq 1: "n must be an integer greater than one that is coprime to the characteristic";
    return GL(2,Integers(n))!GL2FrobeniusMatrix(E);
end intrinsic;

intrinsic nTorsionFrobenius(E::CrvEll[FldFin], n::RngIntElt) -> AlgMatElt[RngIntRes]
{Given an elliptic curve E over a finite field and an integer n, it returns the matrix describing the actin of Frobenius in ZZ/nZZ.}
    return GL2nTorsionFrobenius(E,n);
end intrinsic;

intrinsic GL2nTorsionFrobenius(E::CrvEll[FldRat], p::RngIntElt, n::RngIntElt) -> AlgMatElt[RngIntRes]
{Given an elliptic curve E over a finite field and an integer n, it returns the matrix describing the actin of Frobenius in ZZ/nZZ.}
    require n gt 1 and GCD(p,n) eq 1: "n must be an integer greater than one that is coprime to the characteristic";
    return GL(2,Integers(n))!GL2FrobeniusMatrix(E,p);
end intrinsic;

forward j1728FM;

// The function j0FM and j1728FM below each return a list of pairs <A,w> where A ia Frobenius matrix and w is a rational weight
// The rational points in the fiber of X_H -> X(1) above j=0 can then be computed as the weighted sum of fixpoints of the A's
// See Schoof Theorem 4.2 in https://pdf.sciencedirectassets.com/272565/1-s2.0-S0097316500X00921/1-s2.0-0097316587900033/main.pdf
// Waterhouse Theorem 4.1 in http://www.numdam.org/article/ASENS_1969_4_2_4_521_0.pdf
function j0FM(q)
    _,p,e := IsPrimePower(q);
    if p eq 2 then return j1728FM(q); end if;
    if p mod 3 eq 2 then
        if IsOdd(e) then
            return [<FrobMat(0,p^((e-1) div 2),-4*p),1>];
        else
            return [<FrobMat(p^(e div 2),p^(e div 2),-3),2/3>,<FrobMat(2*p^(e div 2),0,1),1/3>];
        end if;
    elif p eq 3 then
        if IsOdd(e) then
            return [<FrobMat(0,3^((e-1) div 2),-12),1/2>, <FrobMat(0,2*3^((e-1) div 2),-3),1/6>, <FrobMat(3^((e+1) div 2),3^((e-1) div 2),-3),1/3>];
        else
            return [<FrobMat(0,3^(e div 2),-4),1/2>, <FrobMat(3^(e div 2),3^(e div 2),-3),1/3>, <FrobMat(2*3^(e div 2),0,1),1/6>];
        end if;
    end if;
    c,a,b := norm_equation(3,4*q);  assert c and a gt 0 and b gt 0;
    if IsOdd(a) then
        if IsEven((a+3*b) div 2) then u := Abs(a+3*b) div 2; v := Abs(a-b) div 2; else u := Abs(a-3*b) div 2; v := Abs(a+b) div 2; end if;
    else
        u := Abs(a);v := Abs(b);
    end if;
    assert u gt 0 and v gt 0 and IsEven(u) and IsEven(v) and 4*q eq u^2+3*v^2;;
    return [<FrobMat(u,v,-3),1/3>, <FrobMat((u+3*v) div 2,(u-v) div 2,-3),1/3>, <FrobMat((u-3*v) div 2,(u+v) div 2,-3),1/3>];
end function;

function j0PointCount(N,f,q) GL2 := GL(2,Integers(N)); return Integers()! &+[f(GL2!A[1])*A[2]:A in j0FM(q)]; end function;

function j1728FM(q)
    _,p,e := IsPrimePower(q);
    if p eq 3 then return j0FM(q); end if;
    if p mod 4 eq 3 then
        if e mod 2 eq 1 then
            return [<FrobMat(0,p^((e-1) div 2),-4*p),1/2>,<FrobMat(0,2*p^((e-1) div 2),-p),1/2>];
        else
            return [<FrobMat(0,p^(e div 2),-4),1/2>,<FrobMat(2*p^(e div 2),0,1),1/2>];
        end if;
    elif p eq 2 then
        if IsOdd(e) then
            return [<FrobMat(0,2^((e-1) div 2),-8),1/2>,<FrobMat(2^((e+1) div 2),2^((e-1) div 2),-4),1/2>];
        else
            return [<FrobMat(0,2^(e div 2),-4),1/4>,<FrobMat(2^(e div 2),2^(e div 2),-3),2/3>,<FrobMat(2*2^(e div 2),0,1),1/12>];
        end if;
    end if;
    c,a,b := norm_equation(4,4*q);  assert c and a gt 0 and b gt 0;
    if IsOdd(b) then u := Abs(2*b); v := Abs(a div 2); else u := Abs(a); v := Abs(b); end if;
    assert u gt 0 and v gt 0 and IsEven(u) and IsEven(v) and 4*q eq u^2+4*v^2;
    return [<FrobMat(a,b,b eq 0 select 1 else -4),1/2>,<FrobMat(2*b,a div 2,-4),1/2>];
end function;

function j1728PointCount(N,f,q) GL2 := GL(2,Integers(N)); return Integers()! &+[f(GL2!A[1])*A[2]:A in j1728FM(q)]; end function;

// Given level N, permutation character f table C indexed by conjugacy class, class map f, class number table htab for -D <= 4q, prime power q coprime to {N
// returns the number of points on X_H(Fq) above non-cuspidal j!=0,1728
function jNormalPointCount(N,f,htab,q)
    t,p,e := IsPrimePower(q); assert(t);
    GL2 := GL(2,Integers(N));
    assert GCD(q,N) eq 1;
    // To count j-invariants we only consider nonnegative traces a and divide by 2 for a=0
    // We exclude j=0 and j=1278 by skipping discriminants -3 and -4 and adjusting the supersingular counts appropriately
    cnt := 0;
    for a in [1..Floor(2*Sqrt(q))] do  // iterate over positive traces not divisible by p
        if a mod p eq 0 then continue; end if; // supersingular cases handled below
        D1 := a^2-4*q; // discriminant of Z[pi] for trace a
        D0 := FundamentalDiscriminant(D1);
        _,v:=IsSquare (D1 div D0); // 4*q = a^2 - v^2*D0 with D0 fundamental
        for u in Divisors(v) do
            D := D0*u^2;  if D ge -4 then continue; end if;   // skip j=0,1728
            cnt +:= f(GL2!FrobMat(a,v div u,D))*GetClassNumber(htab,D);
        end for;
    end for;
    if p le 3 then return cnt; end if; // for p <= 3 the supersingular j-invariants are all 0=1728
    // For p > 3 the only nonnegative traces divisible by p we need to consider are 0 (when e is odd) and 2*p^(e/2) (when e is even)
    s0 := p mod 3 eq 2 select 1 else 0; s1728 := p mod 4 eq 3 select 1 else 0;
    if e mod 2 eq 1 then
        if s1728 eq 1 then
            // There are 2 Fq-isomorphism classes per j-invariant with trace 0, including j=1728 which is the unique
            // j-invariant where the endomorphism rings are different (one has disc -p the other disc -4p)
            cnt +:= f(GL2!FrobMat(0,2*p^((e-1) div 2),-p))*ExactQuotient(GetClassNumber(htab,-p)-1,2);         // -1 for j=1728, -0 for j=0
            cnt +:= f(GL2!FrobMat(0,p^((e-1) div 2),-4*p))*ExactQuotient(GetClassNumber(htab,-4*p)-1-2*s0,2);  // -1 for j=1728, -2*s0 for j=0
        else
            cnt +:= f(GL2!FrobMat(0,p^((e-1) div 2),-4*p))*ExactQuotient(GetClassNumber(htab,-4*p)-2*s0,2);    // -0 for j=1728, -2*s0 for j=0
        end if;
    else
        // There are (p+6-4*kron(-3,p)-3*kron(-4,p))/12 j-invariants of curves with trace 2*sqrt(q)
        // of which (1-kron(-3,p))/2 have j-invariant 0 and (1-kron(-4,p))/2 have j-invariant 1728
        cnt +:= f(GL2!FrobMat(2*p^(e div 2),0,1)) * ExactQuotient(p-6+2*KroneckerSymbol(-3,p)+3*KroneckerSymbol(-4,p),12);
    end if;
    return cnt;
end function;

intrinsic GL2jCounts(H::GrpMat,q::RngIntElt:chi:=0) -> SetEnum[FldFinElt]
{ A list of counts of the number of Fq-points above each points of Y(1), ordered as GF(q) is ordered. }
    N,H := GL2Level(H);
    require IsPrimePower(q) and GCD(q,N) eq 1: "q must be a prime power that is coprime to the level of H";
    if N eq 1 then return [1:j in GF(q)]; end if;
    G := GL(2,Integers(N));
    f := Type(chi) eq RngIntElt select GL2PermutationCharacter(sub<G|H,-Identity(G)>) else chi;
    J := [];
    for j in GF(q) do
        if j eq 0 then Append(~J,j0PointCount(N,f,q)); continue; end if;
        if j eq 1728 then Append(~J,j1728PointCount(N,f,q)); continue; end if;
        Append(~J,f(G!GL2FrobeniusMatrix(EllipticCurveFromjInvariant(j))));
    end for;
    return J;
end intrinsic;

intrinsic GL2jCounts(H::GrpMat,Q::SeqEnum) -> SeqEnum[FldFinElt]
{ A list of lists of  counts of the number of Fq-points above each points of Y(1), ordered as GF(q) is ordered for q in Q. }
    N,H := GL2Level(H);
    if N eq 1 then return [[1:j in GF(q)]:q in Q]; end if;
    G := GL(2,Integers(N));
    chi := GL2PermutationCharacter(sub<G|H,-Identity(G)>);
    return [ GL2jCounts(H,q:chi:=chi) : q in Q ];
end intrinsic;

intrinsic GL2jInvariants(H::GrpMat,q::RngIntElt:chi:=0) -> SetEnum[FldFinElt]
{ A list of the affine points in the set j(X_H(Fq)). }
    J := GL2jCounts(H,q:chi:=chi);
    Fq := [j:j in GF(q)];
    return [Fq[i]:i in [1..q]|J[i] gt 0];
end intrinsic;

intrinsic GL2jInvariants(H::GrpMat,Q::SeqEnum) -> SeqEnum[FldFinElt]
{ A list of lists of the affine points in the set j(X_H(Fq)) for q in Q. }
    N,H := GL2Level(H);
    if N eq 1 then return [*[j:j in GF(q)]:q in Q*]; end if;
    G := GL(2,Integers(N));
    chi := GL2PermutationCharacter(sub<G|H,-Identity(G)>);
    return [* GL2jInvariants(H,q:chi:=chi) : q in Q *];
end intrinsic;

// htab:=ClassNumbers(4*p), f:=GL2PermutationCharacter(H cup -H), C:=GL2RationalCuspCounts(H)
function XHPointCount(N,htab,f,C,q)
    j := jNormalPointCount(N,f,htab,q); j0 := j0PointCount(N,f,q); j1728 := GCD(q,6) eq 1 select j1728PointCount(N,f,q) else 0;
    return j+j0+j1728+C[q mod N];
end function;

intrinsic GL2PointCounts(H::GrpMat,Q::SeqEnum) -> SeqEnum
{ Sequence of Fq-rational points on X_H for q in Q (which must be prime powers or lists of prime powers coprime to the level of H). }
    if #Q eq 0 then return []; end if;
    lists := Type(Q[1]) eq SeqEnum;
    N,H := GL2Level(H);  if N eq 1 then return lists select [[q+1:q in r]:r in Q] else [q+1:q in Q]; end if;
    GL1 := GL(1,Integers(N));
    D := GL2DeterminantImage(H);  dindex := Index(GL1,D);
    G := GL(2,Integers(N));
    if dindex gt 1 then G:=sub<G|[G|g:g in Generators(SL(2,Integers(N)))] cat [G|[d[1][1],0,0,1]:d in Generators(D)]>; end if;
    m := lists select Max([Max(r):r in Q]) else Max(Q);
    htab := #Q le 100 select ClassNumberTable(4096) else ClassNumberTable(4*m);
    C := (#Q eq 1 and not lists) select [Q[1] mod N eq i select GL2RationalCuspCount(H,Q[1]) else 0:i in [1..N]] else GL2RationalCuspCounts(H);
    f := GL2PermutationCharacter(sub<G|H,-Identity(G)>);
    pts := dindex gt 1 select func<q|GL1![q] in D select XHPointCount(N,htab,f,C,q) else 0> else func<q|XHPointCount(N,htab,f,C,q)>;
    return lists select [[pts(q):q in r]:r in Q] else [pts(q):q in Q];
end intrinsic;

intrinsic GL2Traces(H::GrpMat,Q::SeqEnum) -> SeqEnum
{ The Frobenius traces of X_H/Fq for q in Q (which must be prime powers or lists of prime powers coprime to the level of H). }
    if #Q eq 0 then return []; end if;
    lists := Type(Q[1]) eq SeqEnum;
    N,H := GL2Level(H);  if N eq 1 then return lists select [[q+1:q in r]:r in Q] else [q+1:q in Q]; end if;
    GL1 := GL(1,Integers(N));
    D := GL2DeterminantImage(H);  dindex := Index(GL1,D);
    cnts := GL2PointCounts(H,Q);
    tr := dindex gt 1 select func<q,n|GL1![q] in D select dindex*(q+1)-n else 0> else func<q,n|q+1-n>;
    return Type(Q[1]) eq SeqEnum select [[tr(Q[i][j],cnts[i][j]):j in [1..#cnts[i]]]:i in [1..#cnts]] else [tr(Q[i],cnts[i]):i in [1..#cnts]];
end intrinsic;

intrinsic GL2PointCount(H::GrpMat,q::RngIntElt) -> RngIntElt
{ The number of Fq-rational points on X_H. }
    N,H := GL2Level(H);  if N eq 1 then return q+1; end if;
    require IsPrimePower(q) and GCD(q,N) eq 1: "q must be a prime power that is coprime to the level of H";
    return GL2PointCounts(H,[q])[1];
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,B::RngIntElt:B0:=1,PrimePowers:=false) -> SeqEnum
{ Sequence of Fp-point counts on X_H/Fp for p >= B0 not dividing N up to B.  If PrimePowers is set each entry is a list of integers giving point counts over Fq for q=p,p^2,...<= B.}
    N,H := GL2Level(H);
    Q := [p : p in PrimesInInterval(B0,B) | N mod p ne 0];
    if PrimePowers then Q := [[p^i: i in [1..Floor(Log(p,B))]] : p in Q]; end if;
    return GL2PointCounts(H,Q);
end intrinsic;

intrinsic GL2Traces(H::GrpMat,B::RngIntElt:B0:=1,PrimePowers:=false) -> SeqEnum[RngIntElt]
{ Frobenius traces of X_H at p not dividing N up to B (and p >= B0 if specified). }
    N,H := GL2Level(H);
    Q := [p : p in PrimesInInterval(B0,B) | N mod p ne 0];
    if PrimePowers then Q := [[p^i: i in [1..Floor(Log(p,B))]] : p in Q]; end if;
    return GL2Traces(H,Q);
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,p::RngIntElt,r::RngIntElt) -> SeqEnum[RngIntElt]
{ The sequence of Fq-point counts on X_H/Fq for q=p,p^2,...,p^r for a prime power p. }
    return GL2PointCounts(H,[p^i:i in [1..r]]);
end intrinsic;

intrinsic GL2Traces(H::GrpMat,p::RngIntElt,r::RngIntElt) -> SeqEnum[RngIntElt]
{ The sequence of Frobenius traces of X_H/Fq for q=p,p^2,...,p^r. }
    return GL2Traces(H,[p^i:i in [1..r]]);
end intrinsic;

intrinsic GL2LPolynomial(H::GrpMat,q::RngIntElt) -> RngUPolElt
{ The L-polynomial of X_H/Fq for a prime power q coprime to the level of H. }
    g := GL2Genus(H);
    R<T>:=PolynomialRing(Integers());
    if g eq 0 then return R!1; end if;
    return PointCountsToLPolynomial(GL2PointCounts(H,q,g),q);
end intrinsic;

intrinsic GL2IsogenyClass(H::GrpMat) -> MonStgElt, RngIntElt
{ The Cremona label of the isogeny class of a genus 1 curve X_H, along with its rank.  Will fail if the level is out of range of the Cremona DB. }
    N,H := GL2Level(H);
    require N gt 1:  "H must be have genus 1.";
    require GL2DeterminantIndex(H) eq 1 and GL2Genus(H) eq 1: "H must have determinant index 1 and genus 1";

    P := PrimeDivisors(N);
    badi := {#PrimesUpTo(p):p in P};

    // Computes an integer M so that the conductor of any elliptic curve E/Q with good reduction outside P divides M.
    M := &*[p^2:p in P];
    if 2 in P then M *:= 2^6; end if;
    if 3 in P then M *:= 3^3; end if;

    D:=EllipticCurveDatabase();
    assert M lt LargestConductor(D);  // Ensures that J is isomorphic to a curve in the current database

    EE:= &cat[[EllipticCurve(D,N,i,1) : i in [1.. NumberOfIsogenyClasses(D,N)]] : N in Divisors(M)];   
    // The Jacobian of X_G is isogenous to precisely one of the curves in EE.

    function GoodTracesOfFrobenius(E,B) // Return traces up to B with traces at bad p set to p+2
        T := TracesOfFrobenius(E,B);
        return [T[i] : i in [1..#T] | not i in badi];
    end function;
  
    B := 20;  // this is already enough to distinguish all isogeny classes of prime power level <= 400000
    while #EE gt 1 do
        T := GL2Traces(H,B);
        EE:= [E: E in EE | GoodTracesOfFrobenius(E,B) eq T];
        B *:= 2;
   end while;
   assert #EE eq 1;

   // return the isogeny class label of our representative curve, along with its rank
   _,c:=Regexp("[0-9]+[a-z]+",CremonaReference(EE[1]));
   return c, Rank(EE[1]);
end intrinsic;

intrinsic GL2QAdmissible(H::GrpMat:MustContainNegativeOne:=false) -> BoolElt
{ True if the specified subgroup of GL2(Z/NZ) has determinant index one and contains an element corresponding to complex conjugation (these are preconditions to having Q-rational points). }
    if not IsFinite(BaseRing(H)) and #H eq 1 then return true; end if;
    return (not MustContainNegativeOne or -Identity(H) in H) and (GL2DeterminantIndex(H) eq 1) and GL2ContainsComplexConjugation(H);
end intrinsic;

intrinsic GL2QInfinite(H::GrpMat:MustContainNegativeOne:=false) -> BoolElt
{ True if the j(X_H(Q)) is infinite. }
    if not IsFinite(BaseRing(H)) and #H eq 1 then return true; end if;
    if not GL2QAdmissible(H) then return false; end if;
    g := GL2Genus(H);
    if g eq 0 then return true; end if;
    if g gt 1 then return false; end if;
    _,r := GL2IsogenyClass(H);
    return r gt 0;
end intrinsic;

intrinsic GL2QObstructions(H::GrpMat:B:=0) -> SeqEnum[RngIntElt]
{ List of good places p where X_H has no Qp-points (p=0 is used for the real place). }
    require GL2DeterminantIndex(H) eq 1: "H must have determinant index 1 (otherwise it is obstructed at infinitely many places).";
    N,H := GL2Level(H);
    if N eq 1 then return [Integers()|]; end if;
    if GL2RationalCuspCount(H) gt 0 then return [Integers()|]; end if;
    X := GL2ContainsComplexConjugation(H) select [Integers()|] else [Integers()|0];
    g := GL2Genus(H);  if g eq 0 then return X; end if;
    maxp := B gt 0 select B else 4*g^2;
    badp := Set(PrimeDivisors(N));
    P := [p:p in PrimesInInterval(1,maxp)| not p in badp];
    cnts := GL2PointCounts(H,maxp);
    return X cat [P[i] : i in [1..#P] | cnts[i] eq 0];
end intrinsic;

intrinsic GL2QInfinite(N::RngIntElt) -> SeqEnum[GrpMat]
{ List of subgroups of GL(2,Z/NZ) for which j(X_H(Q)) is infinite (not all of which will have level N). }
    require N gt 0: "N must be a positive integer.";
    if N eq 1 then return [sub<GL(2,Integers())|>]; end if;
    Xkey := func<r|<r[1],r[2],r[3],r[4],r[5]>>;
    // Qinf will only be applied to Q-admissible subgroups, in which case g(H)=0 => X_H(Q) is infinite
    Qinf := func<genus,H|genus eq 0 or (genus eq 1 and rank gt 0 where _,rank:=GL2IsogenyClass(H))>;
    GL2:=GL(2,Integers(N));
    r := <1,1,0,[[1,1,1]],1,GL2>; S := [r];
    X := AssociativeArray(); X[Xkey(r)] := S;
    n := 1;
    while n le #S do
        L := [H`subgroup: H in MaximalSubgroups(S[n][6]) | GL2QAdmissible(H`subgroup:MustContainNegativeOne)];
        genus := [GL2Genus(H) : H in L];
        I := [i: i in [1..#L]|genus[i] le 1];
        L := [<level,GL2Index(H),genus[i],GL2OrbitSignature(H:N:=level),GL2ScalarIndex(H),L[i]> where level,H:=GL2Level(L[i]):i in I];
        // Reduce to conjugacy class reps
        Z := index(L,Xkey);
        L := [];
        for k in Keys(Z) do
            if #Z[k] gt 1 then Z[k] := [Z[k][i]:i in [1..#Z[k]] | &and[not IsConjugate(GL2,Z[k][i][6],Z[k][j][6]):j in [1..i-1]]]; end if;
            L cat:= Z[k];
        end for;
        // Only keep groups we haven't already seen that have X_H(Q) infinite
        L := [r : r in L | (not IsDefined(X,k) or &and[not IsConjugate(GL2,r[6],s[6]):s in X[k]] where k:=Xkey(r)) and Qinf(r[3],r[6])];
        S := S cat L;
        for r in L do k:=Xkey(r); if IsDefined(X,k) then Append(~X[k],r); else X[k] := [r]; end if; end for;
        n +:= 1;
    end while;
    return &cat[&cat[[H : H in GL2QuadraticTwists(r[6]:IncludeSelf) | Qinf(r[3],r[6])] : r in X[k]]:k in Keys(X)];
end intrinsic;

intrinsic GL2ArithmeticallyMaximalBounds(p::RngIntElt) -> RngIntElt, RngIntElt
{ A pair of integers N(p), I(p) such tthat every Q-admissible arithmetically maximal subgroup of GL(2,Zp) has level at most N(p) and index at most I(p). }
    require IsPrime(p): "p must be prime";
    if p gt 13 then
        G:=GL(2,Integers(p));
        m := Max([#G div H`order : H in MaximalSubgroups(G) | GL2QAdmissible(H`subgroup)]);
        return p,m;
    end if;
    e :=  [5,3,2,1,1,1][#PrimesInInterval(1,p)]; // from SZ17, see Lemma 3.2
    S := GL2QInfinite(p^e);  GL2 := GL(2,Integers(p^(e+1)));
    m := Max([Max([0] cat [#GL2 div H`order : H in MaximalSubgroups(G) | GL2QAdmissible(H`subgroup)]) where G:=GL2Lift(H0,p^(e+1)):H0 in S]);
    return p^(e+1),m;
end intrinsic;

intrinsic GL2CompareLabels(a::MonStgElt,b::MonStgElt) -> RngIntElt
{ Lexicographically compares subgroup labels of the form N.i.g.n or N.i.g.d.n (N=level, i=index, g=genus, d=determinant index, n=ordinal) as lists of integers.  Returns -1,0,1. }
    if a eq b then return 0; end if; if a eq "?" then return 1; end if; if b eq "?" then return -1; end if;
    if "-" in a or "-" in b then
        aa := "-" in a select Split(a,"-") else ["1.1.1",a];  bb := "-" in b select Split(b,"-") else ["1.1.1",b];
        if aa[1] ne bb[1] then return GL1CompareLabels(aa[1],bb[1]); end if;
        a := aa[2]; b := bb[2];
    end if;
    r := [StringToInteger(x):x in Split(a,".")]; s := [StringToInteger(x):x in Split(b,".")];
    require #r eq 4 and #s eq 4: "Invalid subgroup label";
    return r lt s select -1 else 1;
end intrinsic;

intrinsic GL2SortLabels(L::SeqEnum[MonStgElt]) -> SeqEnum[MonStgElt]
{ Sorts the specified list of labels of subgroups of GL(2,Zhat). }
    L := Sort(L,func<a,b|GL2CompareLabels(a,b)>);
    return L;
end intrinsic;

intrinsic GL2CompareLabelLists(a::SeqEnum[MonStgElt],b::SeqEnum[MonStgElt]) -> RngIntElt
{ Lexicographically compares two lists of subgroup labels. }
    if a eq b then return 0; end if;
    for i in [1..#a] do
        if i gt #b then return 1; end if;
        if a[i] ne b[i] then return GL2CompareLabels(a[i],b[i]); end if;
    end for;
    return #a lt #b select -1 else 0;
end intrinsic;

gl2node := recformat<
    label:MonStgElt,
    level:RngIntElt,
    index:RngIntElt,
    genus:RngIntElt,
    dlabel:MonStgElt,
    zlabel:MonStgElt,
    orbits:SeqEnum,
    children:SeqEnum,
    parents:SeqEnum,
    subgroup:GrpMat>;

intrinsic GL2Lattice(N::RngIntElt, IndexLimit::RngIntElt : DeterminantLabel:="1.1.1", Verbose:=false, IndexDivides:=false, GenusLimit:=-1) -> Assoc
{ Lattice of subgroups of GL(2,Z/NZ) of index bounded by IndexLimit with specified determinant image.  Returns a list of records with attributes level, index, genus, orbits, dlabel, zlabel, children, parents, subgroup, where children and parents are indices into this list that identify maximal subgroups and minimal supergroups. }
    require N gt 0 and IndexLimit gt 0: "Level and index limit must be positive integers";
    if N eq 1 then
        require DeterminantLabel eq "1.1.1": "Invalid determinant label index for specified modulus N";
        return [rec<gl2node|level:=1,index:=1,genus:=0,orbits:=[[1,1,1]],dlabel:="1.1.1",zlabel:="1.1.1",childen:=[Integers()|],parents:=[Integers()|],subgroup:=sub<GL(2,Integers())|>>];
    end if;
    if DeterminantLabel ne "1.1.1" then
        require DeterminantLabel in GL1Labels(N): "Invalid determinant label index for specified  modulus N";
        D := GL1Lift(GL1SubgroupFromLabel(DeterminantLabel),N);
    else
        D := GL(1,Integers(N));
    end if;
    dindex := GL1Index(D);
    filter := GenusLimit lt 0 select func<H|GL2DeterminantImage(H) eq D> else func<H|GL2DeterminantImage(H) eq D and GL2Genus(H) le GenusLimit>;
    if Verbose then printf "Enumerating determinant %o subgroups of GL(2,Z/%oZ) of index %o %o%o...", DeterminantLabel, N, IndexDivides select "dividing" else "at most", IndexLimit, GenusLimit ge 0 select Sprintf(" and genus at most %o",GenusLimit) else ""; s := Cputime(); end if;
    O := IndexDivides select ExactQuotient(GL2Size(N),IndexLimit) else 1;
    S := [H`subgroup: H in Subgroups(GL(2,Integers(N)) : IndexLimit:=IndexLimit, OrderMultipleOf:=O) | filter (H`subgroup)];
    if Verbose then
        printf "found %o subgroups in %.3os\n", #S, Cputime()-s;
        printf "Computing index, level, genus, orbit signature, scalar index for %o groups...", #S; s := Cputime();
    end if;
    T := [<level,GL2Index(H),GL2Genus(H),GL2OrbitSignature(H:N:=level),GL2ScalarLabel(H)> where level,H:=GL2Level(K) : K in S];
    X := index([1..#T],func<i|<T[i][1],T[i][2],T[i][4],T[i][5]>>);
    if Verbose then printf "%.3os\nComputing lattice edges for %o groups...", Cputime()-s, #T; s:=Cputime(); end if;
    M := {};
    for i:= 1 to #T do
        if 2*T[i][2] gt IndexLimit then continue; end if;
        m := [H`subgroup:H in MaximalSubgroups(S[i] : IndexLimit:=IndexLimit div T[i][2], OrderMultipleOf:=O) | filter(H`subgroup)];
        for H in m do
            level,K := GL2Level(H);
            J := X[<level,GL2Index(K),GL2OrbitSignature(K:N:=level),GL2ScalarLabel(K)>]; j := 1;
            if #J gt 1 then
                GL2:=GL(2,Integers(level));
                while j lt #J do if IsConjugate(GL2,ChangeRing(S[J[j]],Integers(level)),K) then break; end if; j+:=1; end while;
            end if;
            Include(~M,<i,J[j]>);
        end for;
    end for;
    if Verbose then printf "found %o edges in %.3os\n", #M, Cputime()-s; end if;
    for i:=1 to #S do if T[i][1] gt 1 and T[i][1] lt N then S[i] := ChangeRing(S[i],Integers(T[i][1])); end if; end for;
    Xsubs := index(M,func<r|r[1]>:Project:=func<r|r[2]>); subs := func<i|IsDefined(Xsubs,i) select Xsubs[i] else []>;
    Xsups := index(M,func<r|r[2]>:Project:=func<r|r[1]>); sups := func<i|IsDefined(Xsups,i) select Xsups[i] else []>;
    X := index([1..#T],func<i|<T[i][1],T[i][2],T[i][3]>>);
    L := ["" : i in [1..#T]];
    Lsups := [[] : i in [1..#T]];
    if Verbose then printf "Labeling %o subgroups...", #S; s := Cputime(); end if;
    cmpkeys := function(a,b)
        n := GL2CompareLabelLists(a[1],b[1]); if n ne 0 then return n; end if;
        if a[2] lt b[2] then return -1; elif a[2] gt b[2] then return 1; end if;
        if a[3] lt b[3] then return -1; elif a[3] gt b[3] then return 1; end if;
        return 0;
    end function;
    if DeterminantLabel eq "1.1.1" then
        label := func<N,i,g,n|Sprintf("%o.%o.%o.%o",N,i,g,n)>;
    else
        label := func<N,i,g,n|Sprintf("%o-%o.%o.%o.%o",DeterminantLabel,N,i div dindex,g,n)>;
    end if;
    for k in Sort([k:k in Keys(X)]) do
        // all parents of nodes in X[k] correspond to smaller keys and have already been labeled
        for i in X[k] do Lsups[i] := Sort([L[j]:j in sups(i)],func<a,b|GL2CompareLabels(a,b)>); end for;
        n := 1;
        if #X[k] eq 1 then i:=X[k][1]; L[i] := label(k[1],k[2],k[3],n); continue; end if;
        Y := index(X[k],func<i|<Lsups[i],T[i][4],GL2ClassSignature(S[i]:N:=k[1])>>);
        Z := Sort([r:r in Keys(Y)],cmpkeys);
        for r in Z do
            if #Y[r] gt 1 then Y[r] := [a[2]:a in A] where A := Sort([<GL2MinimalConjugate(S[i]),i>:i in Y[r]]); end if;
            for i in Y[r] do L[i] := label(k[1],k[2],k[3],n); n +:= 1; end for;
        end for;
    end for;
    Lsubs := [GL2SortLabels([L[j]:j in subs(i)]): i in [1..#S]];
    if Verbose then printf "%.3os\nMinimizing generators for %o groups...", Cputime()-s, #L; s:=Cputime(); end if;
    X := AssociativeArray();
    for i:=1 to #L do
        H := T[i][1] eq 1 select sub<GL(2,Integers())|> else GL2MinimizeGenerators(S[i]);
        X[L[i]]:= rec<gl2node|label:=L[i],level:=T[i][1],index:=T[i][2],genus:=T[i][3],dlabel:=DeterminantLabel,
                              zlabel:=T[i][5],orbits:=T[i][4],children:=Lsubs[i],parents:=Lsups[i],subgroup:=H>;
    end for;
    if Verbose then printf "%.3os\n", Cputime()-s; end if;
    return X;
end intrinsic;

intrinsic GL2Label(H::GrpMat: Verbose:=false) -> MonStgElt
{ The label of H (this requires computing the sublattice up to the level/index/genus of H -- an expensive way to get a single label). }
    N := GL2Level(H); if N eq 1 then return "1.1.1"; end if;
    i := GL2Index(H); g := GL2Genus(H); 
    X := GL2Lattice(N, i : GenusLimit:=g,DeterminantLabel:=GL2DeterminantLabel(H),Verbose:=Verbose,IndexDivides);
    o := GL2OrbitSignature(H); z:=GL2ScalarLabel(H);
    K := [k:k in Keys(X)|X[k]`level eq N and X[k]`index eq i and X[k]`genus eq g and X[k]`orbits eq o and X[k]`zlabel eq z];
    if #K eq 1 then return K[1]; end if;
    G := GL(2,Integers(N));
    for k in K do if IsConjugate(G,H,X[k]`subgroup) then return k; end if; end for;
    return false;
end intrinsic;

intrinsic GL2LookupLabel(X::Assoc, H::GrpMat : g:=-1, NotFound:="?") -> MonStgElt
{ The label of the specified subgroup of GL(2,Z/NZ) if it is present in the specified subgroup lattice (up to conjugacy). }
    if Type(BaseRing(H)) eq FldFin and IsPrime(#BaseRing(H)) then H := ChangeRing(H,Integers(#BaseRing(H))); end if;
    N,H := GL2Level(H);
    if N eq 1 then return "1.1.0.1"; end if;
    i := GL2Index(H);  g := g lt 0 select GL2Genus(H) else g;  d := GL2DeterminantLabelIndex(H);
    prefix := d eq 1 select Sprintf("%o.%o.%o",N,i,g) else Sprintf("%o.%o.%o.%o",N,i,g,d);
    if not IsDefined(X,prefix cat ".1") then return NotFound; end if;
    o := GL2OrbitSignature(H:N:=N); z := GL2ScalarLabel(H);
    S := []; n:=1;
    while true do
        k := prefix cat Sprintf(".%o",n); if not IsDefined(X,k) then break; end if;
        if X[k]`orbits eq o and X[k]`zlabel eq z then Append(~S,k); end if;
        n +:= 1;
    end while;
    assert #S ne 0; // we assume X is complete, so if H has level,index,genus matching any element of X it must be in X
    if #S eq 1 then return S[1]; end if;
    csig := GL2ClassSignature(H:N:=N);
    S:=[k:k in S|csig eq GL2ClassSignature(X[k]`subgroup)]; assert #S ne 0;
    if #S eq 1 then return S[1]; end if;
    G := GL(2,Integers(N));
    for k in S do if IsConjugate(G,H,X[k]`subgroup) then return k; end if; end for;
    assert false;
end intrinsic;

intrinsic GL2Subgroups(k::MonStgElt,X::Assoc) -> SeqEnum[MonStgElt]
{ Returns a sorted list of labels of groups in X that are conjugate to a subgroup of the group with label k (which will necessarily be the first entry in the list). }
    require IsDefined(X,k): "k must be the label of a group in X";
    S := {k}; more := S;
    repeat more := Set(&cat[X[k]`children : k in more]); S join:= more; until #more eq 0;
    return GL2SortLabels([k:k in S]);
end intrinsic;

intrinsic GL2Supergroups(k::MonStgElt,X::Assoc) -> SeqEnum[MonStgElt]
{ Returns a sorted list of labels of groups in X that contain a subgroup conjugate to the group with label k (which will necessarily be the last entry in the list). }
    S := {k}; more := S;
    repeat more := Set(&cat[X[k]`parents : k in more]); S join:= more; until #more eq 0;
    return GL2SortLabels([k:k in S]);
end intrinsic;

intrinsic GL2QInfinite(r::Rec:MustContainNegativeOne:=false) -> BoolElt
{ True if j(X_H(Q)) is infinite, where H = r`subgroup. }
    posrank := func<r|"rank" in Names(r) select r`rank gt 0 else (rank gt 0 where _,rank:=GL2IsogenyClass(r`subgroup))>;
    return r`genus le 1 and GL2QAdmissible(r`subgroup:MustContainNegativeOne:=MustContainNegativeOne) and (r`genus eq 0 or posrank(r));
end intrinsic;

intrinsic GL2QInfinite(X::Assoc:MustContainNegativeOne:=false) -> SeqEnum[MonStgElt]
{ Sorted list of labels in the specified subgroup lattice for which X_H(Q) is infinite. }
    S := Sort([k : k in Keys(X) |GL2QInfinite(X[k]:MustContainNegativeOne:=MustContainNegativeOne)],func<a,b|GL2CompareLabels(a,b)>);
    return S;
end intrinsic;

intrinsic GL2ArithmeticallyMaximal(X) -> SeqEnum[MonStgElt]
{ Sorted list of labels of arithmetically maximal subgroups in the specified subgroup lattice (these are Q-admissible groups with finitely many Q-points whose parents all have infinitely many Q-points). }
    Q := Set(GL2QInfinite(X));
    S := Sort([k:k in Keys(X)|not k in Q and Set(X[k]`parents) subset Q and GL2QAdmissible(X[k]`subgroup)],func<a,b|GL2CompareLabels(a,b)>);
    return S;
end intrinsic;

/*
  The precomputed lists Xn below contain sets of similarity-invariants of elements of GL(2,Integers(n)) that do not appear in maximal subgroups with det-index 1
  Computed using:
    G := GL(2,Integers(n)); S := GL2SimilaritySet(G);
    X := [S diff GL2SimilaritySet(H`subgroup) : H in MaximalSubgroups(G) | GL2DeterminantIndex(H`subgroup) eq 1];
*/
X8 := [{[[8,7,6,0,0,0,0]],[[8,1,2,1,1,2,0]],[[8,5,2,1,1,1,0]],[[8,5,2,1,1,3,0]],[[8,1,6,1,1,1,2]],[[8,1,2,0,0,0,0]],[[8,3,6,0,0,0,0]],[[8,1,6,0,0,0,0]],[[8,7,2,0,0,0,0]],[[8,1,2,1,1,0,0]],[[8,3,2,0,0,0,0]],[[8,7,0,1,1,0,3]],[[8,3,4,1,1,2,1]],[[8,5,2,0,0,0,0]],[[8,3,4,1,1,0,1]],[[8,7,0,1,1,2,3]],[[8,1,6,1,1,3,2]],[[8,5,6,1,1,2,2]],[[8,5,6,1,1,0,2]],[[8,5,6,0,0,0,0]]},{[[8,7,5,0,0,0,0]],[[8,1,1,0,0,0,0]],[[8,7,3,0,0,0,0]],[[8,7,7,0,0,0,0]],[[8,7,1,0,0,0,0]],[[8,5,3,0,0,0,0]],[[8,5,7,0,0,0,0]],[[8,3,3,0,0,0,0]],[[8,5,5,0,0,0,0]],[[8,3,5,0,0,0,0]],[[8,1,7,0,0,0,0]],[[8,3,7,0,0,0,0]],[[8,1,3,0,0,0,0]],[[8,5,1,0,0,0,0]],[[8,1,5,0,0,0,0]],[[8,3,1,0,0,0,0]]},{[[8,7,1,0,0,0,0]],[[8,1,4,0,0,0,0]],[[8,1,0,0,0,0,0]],[[8,3,4,1,1,2,1]],[[8,5,2,0,0,0,0]],[[8,7,0,1,1,2,3]],[[8,3,4,1,1,0,1]],[[8,3,3,0,0,0,0]],[[8,3,7,0,0,0,0]],[[8,3,1,0,0,0,0]],[[8,3,0,1,1,1,3]],[[8,1,6,0,0,0,0]],[[8,7,5,0,0,0,0]],[[8,3,0,1,1,3,3]],[[8,5,4,0,0,0,0]],[[8,3,5,0,0,0,0]],[[8,7,0,1,1,0,3]],[[8,7,7,0,0,0,0]],[[8,7,4,1,1,1,1]],[[8,5,0,0,0,0,0]],[[8,5,6,0,0,0,0]],[[8,7,4,1,1,3,1]],[[8,7,3,0,0,0,0]],[[8,1,2,0,0,0,0]]},{[[8,3,4,0,0,0,0]],[[8,7,6,0,0,0,0]],[[8,7,4,0,0,0,0]],[[8,3,0,0,0,0,0]],[[8,1,2,0,0,0,0]],[[8,5,0,0,0,0,0]],[[8,3,6,0,0,0,0]],[[8,1,6,0,0,0,0]],[[8,7,2,0,0,0,0]],[[8,1,0,0,0,0,0]],[[8,5,4,0,0,0,0]],[[8,3,2,0,0,0,0]],[[8,1,4,0,0,0,0]],[[8,5,2,0,0,0,0]],[[8,7,0,0,0,0,0]],[[8,5,6,0,0,0,0]]},{[[8,7,1,0,0,0,0]],[[8,5,2,2,3,0,1]],[[8,3,6,0,0,0,0]],[[8,5,6,1,1,2,2]],[[8,1,4,0,0,0,0]],[[8,1,0,0,0,0,0]],[[8,3,0,0,0,0,0]],[[8,5,1,0,0,0,0]],[[8,5,2,1,1,3,0]],[[8,7,0,1,1,2,3]],[[8,5,2,2,3,1,1]],[[8,5,6,1,1,0,2]],[[8,5,3,0,0,0,0]],[[8,3,2,0,0,0,0]],[[8,1,6,0,0,0,0]],[[8,7,5,0,0,0,0]],[[8,7,0,1,1,0,3]],[[8,3,4,0,0,0,0]],[[8,7,7,0,0,0,0]],[[8,5,2,1,1,1,0]],[[8,7,4,1,1,1,1]],[[8,5,5,0,0,0,0]],[[8,7,4,1,1,3,1]],[[8,5,6,2,1,1,1]],[[8,7,3,0,0,0,0]],[[8,5,7,0,0,0,0]],[[8,1,2,0,0,0,0]],[[8,5,6,2,1,0,1]]},{[[8,5,2,2,3,0,1]],[[8,5,6,1,1,2,2]],[[8,1,4,0,0,0,0]],[[8,1,0,0,0,0,0]],[[8,7,6,0,0,0,0]],[[8,3,4,1,1,2,1]],[[8,5,1,0,0,0,0]],[[8,5,2,1,1,3,0]],[[8,7,2,0,0,0,0]],[[8,3,4,1,1,0,1]],[[8,3,3,0,0,0,0]],[[8,3,7,0,0,0,0]],[[8,5,2,2,3,1,1]],[[8,5,6,1,1,0,2]],[[8,3,1,0,0,0,0]],[[8,3,0,1,1,1,3]],[[8,5,3,0,0,0,0]],[[8,1,6,0,0,0,0]],[[8,3,0,1,1,3,3]],[[8,3,5,0,0,0,0]],[[8,5,2,1,1,1,0]],[[8,7,0,0,0,0,0]],[[8,5,5,0,0,0,0]],[[8,5,6,2,1,1,1]],[[8,5,7,0,0,0,0]],[[8,1,2,0,0,0,0]],[[8,7,4,0,0,0,0]],[[8,5,6,2,1,0,1]]}];
X9 := [{[[9,7,2,0,0,0,0]],[[9,8,2,0,0,0,0]],[[9,5,5,0,0,0,0]],[[9,1,7,0,0,0,0]],[[9,8,3,0,0,0,0]],[[9,4,5,1,1,0,1]],[[9,1,5,0,0,0,0]],[[9,1,2,1,1,1,0]],[[9,5,7,0,0,0,0]],[[9,5,4,0,0,0,0]],[[9,8,1,0,0,0,0]],[[9,4,4,1,2,0,0]],[[9,4,8,0,0,0,0]],[[9,1,7,1,2,2,1]],[[9,8,7,0,0,0,0]],[[9,4,5,1,1,2,1]],[[9,1,2,0,0,0,0]],[[9,1,6,0,0,0,0]],[[9,4,4,1,2,2,0]],[[9,7,1,1,2,2,2]],[[9,4,5,0,0,0,0]],[[9,1,7,1,2,1,1]],[[9,8,6,0,0,0,0]],[[9,2,3,0,0,0,0]],[[9,2,1,0,0,0,0]],[[9,4,1,0,0,0,0]],[[9,4,6,0,0,0,0]],[[9,7,1,1,2,1,2]],[[9,2,8,0,0,0,0]],[[9,5,6,0,0,0,0]],[[9,7,1,0,0,0,0]],[[9,1,7,1,2,0,1]],[[9,7,6,0,0,0,0]],[[9,7,8,1,1,1,2]],[[9,2,4,0,0,0,0]],[[9,4,3,0,0,0,0]],[[9,2,6,0,0,0,0]],[[9,1,2,1,1,0,0]],[[9,2,5,0,0,0,0]],[[9,1,3,0,0,0,0]],[[9,7,8,1,1,2,2]],[[9,4,4,0,0,0,0]],[[9,4,5,1,1,1,1]],[[9,7,3,0,0,0,0]],[[9,7,1,1,2,0,2]],[[9,5,2,0,0,0,0]],[[9,1,2,1,1,2,0]],[[9,5,3,0,0,0,0]],[[9,1,4,0,0,0,0]],[[9,7,7,0,0,0,0]],[[9,4,4,1,2,1,0]],[[9,7,8,0,0,0,0]],[[9,8,8,0,0,0,0]],[[9,7,8,1,1,0,2]]},{[[9,8,7,0,0,0,0]],[[9,2,5,0,0,0,0]],[[9,5,4,0,0,0,0]],[[9,2,4,0,0,0,0]],[[9,5,5,0,0,0,0]],[[9,1,6,0,0,0,0]],[[9,8,4,0,0,0,0]],[[9,1,0,0,0,0,0]],[[9,7,6,0,0,0,0]],[[9,1,3,0,0,0,0]],[[9,5,2,0,0,0,0]],[[9,8,2,0,0,0,0]],[[9,4,3,0,0,0,0]],[[9,2,1,0,0,0,0]],[[9,5,8,0,0,0,0]],[[9,2,7,0,0,0,0]],[[9,2,8,0,0,0,0]],[[9,2,2,0,0,0,0]],[[9,4,0,0,0,0,0]],[[9,8,8,0,0,0,0]],[[9,4,6,0,0,0,0]],[[9,8,5,0,0,0,0]],[[9,7,3,0,0,0,0]],[[9,8,1,0,0,0,0]],[[9,7,0,0,0,0,0]],[[9,5,7,0,0,0,0]],[[9,5,1,0,0,0,0]]},{[[9,1,7,0,0,0,0]],[[9,1,8,0,0,0,0]],[[9,1,5,0,0,0,0]],[[9,1,1,0,0,0,0]],[[9,7,5,0,0,0,0]],[[9,4,1,0,0,0,0]],[[9,1,4,0,0,0,0]],[[9,4,2,0,0,0,0]],[[9,7,2,0,0,0,0]],[[9,7,1,0,0,0,0]],[[9,1,2,0,0,0,0]],[[9,7,7,0,0,0,0]],[[9,7,8,0,0,0,0]],[[9,7,4,0,0,0,0]],[[9,4,5,0,0,0,0]],[[9,4,4,0,0,0,0]],[[9,4,8,0,0,0,0]],[[9,4,7,0,0,0,0]]}];
X5 := [{[[5,1,2,0,0,0,0]],[[5,4,4,0,0,0,0]],[[5,2,2,0,0,0,0]],[[5,1,3,0,0,0,0]],[[5,4,1,0,0,0,0]],[[5,2,3,0,0,0,0]],[[5,3,1,0,0,0,0]],[[5,3,4,0,0,0,0]]},{[[5,1,1,0,0,0,0]],[[5,4,2,0,0,0,0]],[[5,2,4,0,0,0,0]],[[5,1,4,0,0,0,0]],[[5,3,0,0,0,0,0]],[[5,2,1,0,0,0,0]],[[5,4,3,0,0,0,0]],[[5,3,2,0,0,0,0]],[[5,3,3,0,0,0,0]],[[5,2,0,0,0,0,0]]},{[[5,1,2,0,0,0,0]],[[5,2,1,0,0,0,0]],[[5,4,4,0,0,0,0]],[[5,1,3,0,0,0,0]],[[5,4,1,0,0,0,0]],[[5,2,4,0,0,0,0]],[[5,3,2,0,0,0,0]],[[5,3,3,0,0,0,0]]}];
X7 := [{[[7,4,3,0,0,0,0]],[[7,6,1,0,0,0,0]],[[7,3,1,0,0,0,0]],[[7,1,4,0,0,0,0]],[[7,4,6,0,0,0,0]],[[7,3,6,0,0,0,0]],[[7,2,6,0,0,0,0]],[[7,2,2,0,0,0,0]],[[7,6,6,0,0,0,0]],[[7,2,5,0,0,0,0]],[[7,6,3,0,0,0,0]],[[7,4,1,0,0,0,0]],[[7,6,4,0,0,0,0]],[[7,3,5,0,0,0,0]],[[7,5,2,0,0,0,0]],[[7,1,5,0,0,0,0]],[[7,5,3,0,0,0,0]],[[7,4,4,0,0,0,0]],[[7,3,2,0,0,0,0]],[[7,2,1,0,0,0,0]],[[7,1,3,0,0,0,0]],[[7,5,4,0,0,0,0]],[[7,1,2,0,0,0,0]],[[7,5,5,0,0,0,0]]},{[[7,2,2,0,0,0,0]],[[7,1,0,0,0,0,0]],[[7,3,6,0,0,0,0]],[[7,3,2,0,0,0,0]],[[7,6,3,0,0,0,0]],[[7,1,3,0,0,0,0]],[[7,5,4,0,0,0,0]],[[7,3,1,0,0,0,0]],[[7,5,5,0,0,0,0]],[[7,2,5,0,0,0,0]],[[7,5,2,0,0,0,0]],[[7,4,0,0,0,0,0]],[[7,6,4,0,0,0,0]],[[7,6,6,0,0,0,0]],[[7,5,3,0,0,0,0]],[[7,6,1,0,0,0,0]],[[7,1,4,0,0,0,0]],[[7,4,1,0,0,0,0]],[[7,4,6,0,0,0,0]],[[7,3,5,0,0,0,0]],[[7,2,0,0,0,0,0]]},{[[7,3,3,0,0,0,0]],[[7,4,3,0,0,0,0]],[[7,1,5,0,0,0,0]],[[7,3,4,0,0,0,0]],[[7,2,6,0,0,0,0]],[[7,1,6,0,0,0,0]],[[7,5,1,0,0,0,0]],[[7,5,6,0,0,0,0]],[[7,4,5,0,0,0,0]],[[7,6,5,0,0,0,0]],[[7,6,2,0,0,0,0]],[[7,1,1,0,0,0,0]],[[7,1,2,0,0,0,0]],[[7,4,2,0,0,0,0]],[[7,4,4,0,0,0,0]],[[7,2,3,0,0,0,0]],[[7,2,1,0,0,0,0]],[[7,2,4,0,0,0,0]]}];
X13 := [{[[13,2,2,0,0,0,0]],[[13,2,10,0,0,0,0]],[[13,9,1,0,0,0,0]],[[13,1,9,0,0,0,0]],[[13,7,9,0,0,0,0]],[[13,7,4,0,0,0,0]],[[13,10,1,0,0,0,0]],[[13,8,7,0,0,0,0]],[[13,12,3,0,0,0,0]],[[13,11,10,0,0,0,0]],[[13,3,9,0,0,0,0]],[[13,1,2,0,0,0,0]],[[13,12,5,0,0,0,0]],[[13,5,2,0,0,0,0]],[[13,1,4,0,0,0,0]],[[13,7,12,0,0,0,0]],[[13,1,12,0,0,0,0]],[[13,10,11,0,0,0,0]],[[13,12,10,0,0,0,0]],[[13,2,3,0,0,0,0]],[[13,9,10,0,0,0,0]],[[13,10,12,0,0,0,0]],[[13,4,9,0,0,0,0]],[[13,7,8,0,0,0,0]],[[13,12,6,0,0,0,0]],[[13,3,10,0,0,0,0]],[[13,5,4,0,0,0,0]],[[13,4,2,0,0,0,0]],[[13,5,9,0,0,0,0]],[[13,9,3,0,0,0,0]],[[13,11,1,0,0,0,0]],[[13,5,7,0,0,0,0]],[[13,1,11,0,0,0,0]],[[13,10,2,0,0,0,0]],[[13,9,12,0,0,0,0]],[[13,3,5,0,0,0,0]],[[13,4,8,0,0,0,0]],[[13,10,7,0,0,0,0]],[[13,2,8,0,0,0,0]],[[13,8,4,0,0,0,0]],[[13,11,12,0,0,0,0]],[[13,9,7,0,0,0,0]],[[13,11,2,0,0,0,0]],[[13,10,6,0,0,0,0]],[[13,6,12,0,0,0,0]],[[13,6,6,0,0,0,0]],[[13,2,11,0,0,0,0]],[[13,12,7,0,0,0,0]],[[13,4,4,0,0,0,0]],[[13,6,1,0,0,0,0]],[[13,4,11,0,0,0,0]],[[13,3,8,0,0,0,0]],[[13,4,5,0,0,0,0]],[[13,5,6,0,0,0,0]],[[13,3,4,0,0,0,0]],[[13,8,3,0,0,0,0]],[[13,2,5,0,0,0,0]],[[13,11,11,0,0,0,0]],[[13,7,1,0,0,0,0]],[[13,12,8,0,0,0,0]],[[13,9,6,0,0,0,0]],[[13,1,1,0,0,0,0]],[[13,8,6,0,0,0,0]],[[13,7,5,0,0,0,0]],[[13,3,3,0,0,0,0]],[[13,6,5,0,0,0,0]],[[13,8,9,0,0,0,0]],[[13,5,11,0,0,0,0]],[[13,6,7,0,0,0,0]],[[13,11,3,0,0,0,0]],[[13,6,8,0,0,0,0]],[[13,8,10,0,0,0,0]]},{[[13,9,12,0,0,0,0]],[[13,12,4,0,0,0,0]],[[13,6,9,0,0,0,0]],[[13,11,4,0,0,0,0]],[[13,5,8,0,0,0,0]],[[13,5,3,0,0,0,0]],[[13,3,11,0,0,0,0]],[[13,8,11,0,0,0,0]],[[13,6,1,0,0,0,0]],[[13,9,7,0,0,0,0]],[[13,7,7,0,0,0,0]],[[13,1,11,0,0,0,0]],[[13,1,10,0,0,0,0]],[[13,6,4,0,0,0,0]],[[13,3,8,0,0,0,0]],[[13,9,4,0,0,0,0]],[[13,1,3,0,0,0,0]],[[13,6,7,0,0,0,0]],[[13,7,5,0,0,0,0]],[[13,9,1,0,0,0,0]],[[13,11,1,0,0,0,0]],[[13,9,2,0,0,0,0]],[[13,9,6,0,0,0,0]],[[13,4,9,0,0,0,0]],[[13,10,10,0,0,0,0]],[[13,5,1,0,0,0,0]],[[13,6,6,0,0,0,0]],[[13,4,8,0,0,0,0]],[[13,5,9,0,0,0,0]],[[13,2,6,0,0,0,0]],[[13,6,2,0,0,0,0]],[[13,2,7,0,0,0,0]],[[13,11,6,0,0,0,0]],[[13,5,2,0,0,0,0]],[[13,4,7,0,0,0,0]],[[13,2,4,0,0,0,0]],[[13,5,5,0,0,0,0]],[[13,5,12,0,0,0,0]],[[13,7,10,0,0,0,0]],[[13,11,11,0,0,0,0]],[[13,10,1,0,0,0,0]],[[13,4,5,0,0,0,0]],[[13,4,12,0,0,0,0]],[[13,11,9,0,0,0,0]],[[13,7,11,0,0,0,0]],[[13,4,10,0,0,0,0]],[[13,11,8,0,0,0,0]],[[13,2,9,0,0,0,0]],[[13,2,12,0,0,0,0]],[[13,4,3,0,0,0,0]],[[13,6,12,0,0,0,0]],[[13,10,8,0,0,0,0]],[[13,3,7,0,0,0,0]],[[13,1,9,0,0,0,0]],[[13,3,2,0,0,0,0]],[[13,9,11,0,0,0,0]],[[13,5,4,0,0,0,0]],[[13,10,5,0,0,0,0]],[[13,8,3,0,0,0,0]],[[13,7,2,0,0,0,0]],[[13,8,8,0,0,0,0]],[[13,8,6,0,0,0,0]],[[13,1,4,0,0,0,0]],[[13,6,11,0,0,0,0]],[[13,5,11,0,0,0,0]],[[13,12,12,0,0,0,0]],[[13,8,5,0,0,0,0]],[[13,11,12,0,0,0,0]],[[13,12,10,0,0,0,0]],[[13,6,10,0,0,0,0]],[[13,1,7,0,0,0,0]],[[13,8,2,0,0,0,0]],[[13,7,3,0,0,0,0]],[[13,2,5,0,0,0,0]],[[13,12,9,0,0,0,0]],[[13,12,7,0,0,0,0]],[[13,5,10,0,0,0,0]],[[13,11,2,0,0,0,0]],[[13,3,1,0,0,0,0]],[[13,2,1,0,0,0,0]],[[13,1,8,0,0,0,0]],[[13,1,6,0,0,0,0]],[[13,6,3,0,0,0,0]],[[13,10,11,0,0,0,0]],[[13,10,3,0,0,0,0]],[[13,4,6,0,0,0,0]],[[13,8,7,0,0,0,0]],[[13,7,4,0,0,0,0]],[[13,2,10,0,0,0,0]],[[13,11,5,0,0,0,0]],[[13,8,1,0,0,0,0]],[[13,3,5,0,0,0,0]],[[13,10,2,0,0,0,0]],[[13,8,12,0,0,0,0]],[[13,3,12,0,0,0,0]],[[13,11,7,0,0,0,0]],[[13,10,9,0,0,0,0]],[[13,4,4,0,0,0,0]],[[13,12,11,0,0,0,0]],[[13,3,3,0,0,0,0]],[[13,1,5,0,0,0,0]],[[13,9,9,0,0,0,0]],[[13,1,2,0,0,0,0]],[[13,2,3,0,0,0,0]],[[13,10,12,0,0,0,0]],[[13,7,6,0,0,0,0]],[[13,12,1,0,0,0,0]],[[13,12,3,0,0,0,0]],[[13,9,8,0,0,0,0]],[[13,9,5,0,0,0,0]],[[13,7,8,0,0,0,0]],[[13,3,6,0,0,0,0]],[[13,8,10,0,0,0,0]],[[13,2,8,0,0,0,0]],[[13,12,2,0,0,0,0]],[[13,4,1,0,0,0,0]],[[13,3,10,0,0,0,0]],[[13,10,4,0,0,0,0]],[[13,7,9,0,0,0,0]],[[13,12,6,0,0,0,0]]},{[[13,11,6,0,0,0,0]],[[13,5,1,0,0,0,0]],[[13,9,4,0,0,0,0]],[[13,6,3,0,0,0,0]],[[13,2,7,0,0,0,0]],[[13,9,7,0,0,0,0]],[[13,3,8,0,0,0,0]],[[13,7,10,0,0,0,0]],[[13,9,2,0,0,0,0]],[[13,10,4,0,0,0,0]],[[13,3,12,0,0,0,0]],[[13,8,5,0,0,0,0]],[[13,9,5,0,0,0,0]],[[13,3,5,0,0,0,0]],[[13,10,8,0,0,0,0]],[[13,12,4,0,0,0,0]],[[13,12,3,0,0,0,0]],[[13,5,3,0,0,0,0]],[[13,4,12,0,0,0,0]],[[13,6,10,0,0,0,0]],[[13,8,8,0,0,0,0]],[[13,7,7,0,0,0,0]],[[13,5,12,0,0,0,0]],[[13,4,4,0,0,0,0]],[[13,1,8,0,0,0,0]],[[13,4,9,0,0,0,0]],[[13,10,3,0,0,0,0]],[[13,12,9,0,0,0,0]],[[13,7,11,0,0,0,0]],[[13,12,10,0,0,0,0]],[[13,3,1,0,0,0,0]],[[13,4,3,0,0,0,0]],[[13,1,3,0,0,0,0]],[[13,4,7,0,0,0,0]],[[13,4,1,0,0,0,0]],[[13,5,8,0,0,0,0]],[[13,4,10,0,0,0,0]],[[13,2,6,0,0,0,0]],[[13,2,12,0,0,0,0]],[[13,5,10,0,0,0,0]],[[13,10,10,0,0,0,0]],[[13,7,3,0,0,0,0]],[[13,12,1,0,0,0,0]],[[13,2,9,0,0,0,0]],[[13,3,11,0,0,0,0]],[[13,12,11,0,0,0,0]],[[13,6,2,0,0,0,0]],[[13,3,7,0,0,0,0]],[[13,1,7,0,0,0,0]],[[13,9,9,0,0,0,0]],[[13,1,5,0,0,0,0]],[[13,5,5,0,0,0,0]],[[13,10,9,0,0,0,0]],[[13,7,2,0,0,0,0]],[[13,9,11,0,0,0,0]],[[13,2,1,0,0,0,0]],[[13,8,1,0,0,0,0]],[[13,11,8,0,0,0,0]],[[13,10,5,0,0,0,0]],[[13,3,2,0,0,0,0]],[[13,3,6,0,0,0,0]],[[13,9,6,0,0,0,0]],[[13,1,11,0,0,0,0]],[[13,6,11,0,0,0,0]],[[13,11,7,0,0,0,0]],[[13,7,6,0,0,0,0]],[[13,1,10,0,0,0,0]],[[13,6,9,0,0,0,0]],[[13,4,6,0,0,0,0]],[[13,8,2,0,0,0,0]],[[13,11,9,0,0,0,0]],[[13,2,4,0,0,0,0]],[[13,8,12,0,0,0,0]],[[13,12,12,0,0,0,0]],[[13,8,11,0,0,0,0]],[[13,11,5,0,0,0,0]],[[13,1,2,0,0,0,0]],[[13,9,8,0,0,0,0]],[[13,12,2,0,0,0,0]],[[13,10,1,0,0,0,0]],[[13,1,6,0,0,0,0]],[[13,10,12,0,0,0,0]],[[13,11,4,0,0,0,0]],[[13,6,4,0,0,0,0]]},{[[13,11,6,0,0,0,0]],[[13,5,1,0,0,0,0]],[[13,9,4,0,0,0,0]],[[13,6,3,0,0,0,0]],[[13,2,7,0,0,0,0]],[[13,7,10,0,0,0,0]],[[13,9,2,0,0,0,0]],[[13,10,4,0,0,0,0]],[[13,3,12,0,0,0,0]],[[13,8,5,0,0,0,0]],[[13,9,5,0,0,0,0]],[[13,11,0,0,0,0,0]],[[13,10,8,0,0,0,0]],[[13,12,4,0,0,0,0]],[[13,5,3,0,0,0,0]],[[13,4,12,0,0,0,0]],[[13,6,10,0,0,0,0]],[[13,8,8,0,0,0,0]],[[13,7,7,0,0,0,0]],[[13,5,12,0,0,0,0]],[[13,1,8,0,0,0,0]],[[13,10,3,0,0,0,0]],[[13,12,9,0,0,0,0]],[[13,7,11,0,0,0,0]],[[13,3,1,0,0,0,0]],[[13,1,3,0,0,0,0]],[[13,4,3,0,0,0,0]],[[13,4,7,0,0,0,0]],[[13,4,1,0,0,0,0]],[[13,5,0,0,0,0,0]],[[13,5,8,0,0,0,0]],[[13,2,0,0,0,0,0]],[[13,4,10,0,0,0,0]],[[13,2,6,0,0,0,0]],[[13,2,12,0,0,0,0]],[[13,5,10,0,0,0,0]],[[13,10,10,0,0,0,0]],[[13,7,3,0,0,0,0]],[[13,12,1,0,0,0,0]],[[13,2,9,0,0,0,0]],[[13,3,11,0,0,0,0]],[[13,12,11,0,0,0,0]],[[13,6,2,0,0,0,0]],[[13,3,7,0,0,0,0]],[[13,1,7,0,0,0,0]],[[13,9,9,0,0,0,0]],[[13,7,0,0,0,0,0]],[[13,1,5,0,0,0,0]],[[13,5,5,0,0,0,0]],[[13,10,9,0,0,0,0]],[[13,7,2,0,0,0,0]],[[13,9,11,0,0,0,0]],[[13,2,1,0,0,0,0]],[[13,8,1,0,0,0,0]],[[13,11,8,0,0,0,0]],[[13,10,5,0,0,0,0]],[[13,3,2,0,0,0,0]],[[13,3,6,0,0,0,0]],[[13,6,11,0,0,0,0]],[[13,8,0,0,0,0,0]],[[13,11,7,0,0,0,0]],[[13,7,6,0,0,0,0]],[[13,1,10,0,0,0,0]],[[13,6,9,0,0,0,0]],[[13,4,6,0,0,0,0]],[[13,8,2,0,0,0,0]],[[13,11,9,0,0,0,0]],[[13,2,4,0,0,0,0]],[[13,8,12,0,0,0,0]],[[13,12,12,0,0,0,0]],[[13,8,11,0,0,0,0]],[[13,11,5,0,0,0,0]],[[13,9,8,0,0,0,0]],[[13,6,0,0,0,0,0]],[[13,12,2,0,0,0,0]],[[13,1,6,0,0,0,0]],[[13,11,4,0,0,0,0]],[[13,6,4,0,0,0,0]]}];

// This function implements an augmented version of Zywina's ExceptionalPrimes algorithm in https://arxiv.org/abs/1508.07661
intrinsic NonSurjectivePrimes(E::CrvEll[FldRat]:A:=[]) -> SeqEnum
{ Given an elliptic curve E/Q, returns a list of primes ell for which the ell-adic representation attached to E could be non-surjective. This list provably contains all such primes and usually contains no others. }
    require BaseRing(E) eq Rationals()and not HasComplexMultiplication(E): "E must be a non-CM elliptic curve over Q";
    E := MinimalModel(E); D := Integers()!Discriminant(E);
    j := jInvariant(E); den := Denominator(j);
    S := {2,3,5,7,13};
    if j in {-11^2,-11*131^3} then Include(~S,11); end if;
    if j in {-297756989/2, -882216989/131072} then Include(~S,17); end if;
    if j in {-9317, -162677523113838677} then Include(~S,37); end if;
    if den ne 1 then
        ispow,b,e:=IsPower(den);
        if ispow then
            P := {p : p in PrimeDivisors(e) | p ge 11};
            if P ne {} then                
                S join:= { ell : ell in PrimeDivisors(g) | ell ge 11 } where g := GCD({&*P} join {p^2-1 : p in PrimeDivisors(b)});
            end if;
        end if;
    else
        Q := PrimeDivisors(GCD(Numerator(j-1728),Numerator(D)*Denominator(D)));
        Q := [q: q in Q | q ne 2 and IsOdd(Valuation(j-1728,q))];
        if Valuation(j,2) in {3,6,9} then Q cat:= [2]; end if;
        p:=2; alpha:=[]; beta:=[];
        repeat
            a:=0;
            while a eq 0 do
                p:=NextPrime(p); K:=KodairaSymbol(E,p);
                a := K eq KodairaSymbol("I0") select TraceOfFrobenius(E,p) else (K eq KodairaSymbol("I0*") select TraceOfFrobenius(QuadraticTwist(E,p),p) else 0);
            end while;
            S join:= { ell : ell in PrimeDivisors(a) | ell gt 13 };
            alpha cat:= [[(1-KroneckerSymbol(q,p)) div 2 : q in Q]];  beta cat:= [[(1-KroneckerSymbol(-1,p)) div 2]];
            M := Matrix(GF(2),alpha); b:=Matrix(GF(2),beta);
        until IsConsistent(Transpose(M),Transpose(b)) eq false;
    end if;
    if #A eq 0 then A := GL2FrobeniusMatrices(E,64); end if;
    n := #[s:s in X8|#(t meet s) eq 0] where t:={GL2SimilarityInvariant(GL(2,Integers(8))!a):a in A|Determinant(a) ne 2}; if n eq 0 then Exclude(~S,2); end if;
    n := #[s:s in X9|#(t meet s) eq 0] where t:={GL2SimilarityInvariant(GL(2,Integers(9))!a):a in A|Determinant(a) ne 3}; if n eq 0 then Exclude(~S,3); end if;
    n := #[s:s in X5|#(t meet s) eq 0] where t:={GL2SimilarityInvariant(GL(2,Integers(5))!a):a in A|Determinant(a) ne 5}; if n eq 0 then Exclude(~S,5); end if;
    n := #[s:s in X7|#(t meet s) eq 0] where t:={GL2SimilarityInvariant(GL(2,Integers(7))!a):a in A|Determinant(a) ne 7}; if n eq 0 then Exclude(~S,7); end if;
    n := #[s:s in X13|#(t meet s) eq 0] where t:={GL2SimilarityInvariant(GL(2,Integers(13))!a):a in A|Determinant(a) ne 13}; if n eq 0 then Exclude(~S,13); end if;
    S := Sort([p:p in S]);
    return S;
end intrinsic;

intrinsic GL2SimilaritySet(X::Assoc,k::MonStgElt) -> SetEnum
{ Returns the set of similarity invariants identifying the GL2-conjugacy classes in the group with label, using cached result if available. }
    if not "sset" in Names(X[k]) then GL2SimilaritySet(X[k]`subgroup); end if;
    return assigned X[k]`sset select X[k]`sset else GL2SimilaritySet(X[k]`subgroup);
end intrinsic;

intrinsic GL2HeuristicEllAdicImage(E::CrvEll,ell::RngIntElt,A::SeqEnum,X::Assoc:Fast:=false,Proof:=true,MaxTorsion:=9) -> SeqEnum[MonStgElt], BoolElt
{ Given a non-CM elliptic curve E/Q, a list of Frobenius matrices A for E, and a lattice of ell-adic subgroups X, returns a list of labels of groups in X that are most likely to be the ell-adic image of E.  If the second return value is true, the list includes all groups in X that could be the ell-adic image of E. }
    require BaseRing(E) eq Rationals() and not HasComplexMultiplication(E): "E should be a non-CM elliptic curve over Q.";
    require #A ge 3: "You need to provide at least 3 Frobenius matrices.";
    require IsDefined(X,"1.1.0.1"): "Subgroup lattice X needs to contain the trivial group.";
    E := WeierstrassModel(MinimalModel(E));  D := Integers()!Discriminant(E);
    L := [["1.1.0.1"]];
    if ell eq 2 then N := 32; elif ell eq 3 then N := 27; elif ell le 11 then N := ell^2; else N := ell; end if;
    Z := AssociativeArray();
    for n in Divisors(N) do if n gt 1 then G := GL(2,Integers(n)); Z[n] := {GL2SimilarityInvariant(G!a):a in A|GCD(Determinant(a),n) eq 1}; end if; end for;
    while true do
        LL := [k:k in {k : k in Set(&cat[X[k]`children:k in L[#L]]) | X[k]`dlabel eq "1.1.1" and N mod X[k]`level eq 0 and Z[X[k]`level] subset GL2SimilaritySet(X,k)}];
        if #LL eq 0 then break; end if;
        Append(~L,LL);
    end while;
    L := Sort([k:k in Set(&cat L)],func<a,b|GL2CompareLabels(a,b)>);
    if Fast or #L eq 1 then return L, true; end if;
    N := Max([X[k]`level:k in L]);

    iorb := func<k,n|[r:r in X[k]`level ge n select X[k]`iorbits else GL2IsogenySignature(GL2Lift(X[k]`subgroup,n):N:=n) | r[1] eq n]>;
    korb := func<k,n|[r:r in X[k]`level ge n select X[k]`korbits else GL2KummerSignature(GL2Lift(X[k]`subgroup,n):N:=n) | r[1] eq n]>;
    tdeg := func<k,n|Min([r[2]:r in X[k]`level ge n select X[k]`orbits else GL2OrbitSignature(GL2Lift(X[k]`subgroup,n):N:=n) | r[1] eq n])>;
    torb := func<k,n|[r:r in X[k]`level ge n select X[k]`orbits else GL2OrbitSignature(GL2Lift(X[k]`subgroup,n):N:=n) | r[1] eq n]>;
    igrp := func<k,n|pi(GL2Project(X[k]`subgroup,n)) where _,pi:=quo<G|Center(G)> where G:=GL(2,Integers(n))>;
    tgrp := func<k,n|GL2Project(X[k]`subgroup,n)>;

    R<x>:=PolynomialRing(Rationals());
    for n in Divisors(N) do
        if n eq 1 then continue; end if;
        I := [iorb(k,n):k in L];
        if #Set(I) gt 1 and n lt 60 then
            s := lmset({* [n,Degree(a[1])]^^a[2] : a in Factorization(Evaluate(ClassicalModularPolynomial(n),[x,jInvariant(E)])) *});
            L := [L[i]:i in [1..#I]|I[i] eq s];
            if #L eq 1 then return L, true; end if;
        end if;
        I := [korb(k,n):k in L];
        if #Set(I) gt 1 then
            s := lmset({* [n,Degree(a[1])]^^a[2] : a in Factorization(PrimitiveDivisionPolynomial(E,n)) *});
            L := [L[i]:i in [1..#I]|I[i] eq s];
            if #L eq 1 then return L, true; end if;
        end if;
        I := [tdeg(k,n):k in L];
        if #Set(I) gt 1 then
            d := TorsionDegree(E,n);
            L := [L[i]:i in [1..#I]|I[i] eq d];
            if #L eq 1 then return L, true; end if;
        end if;
        I := [torb(k,n):k in L];
        if #Set(I) gt 1 then
            s := lmset({* [n,d]^^Multiplicity(S,d) : d in Set(S) *}) where S:=TorsionOrbits(E,n);
            L := [L[i]:i in [1..#I]|I[i] eq s];
            if #L eq 1 then return L, true; end if;
        end if;
    end for;
    for n in Divisors(N) do
        if n eq 1 or n gt MaxTorsion then continue; end if;
        I := [igrp(k,n):k in L];
        if #{IdentifyGroup(H) : H in I} gt 1 then
            G := IsogenyGaloisGroup(E,n);
            L := [L[i]:i in [1..#I]|IsIsomorphic(I[i],G)];
            if #L eq 1 then return L, true; end if;
        end if;
        I := [tgrp(k,n):k in L];
        if #{IdentifyGroup(H) : H in I} gt 1 then
            G := TorsionGaloisGroup(E,n);
            L := [L[i]:i in [1..#I]|IsIsomorphic(I[i],G)];
            if #L eq 1 then return L, true; end if;
        end if;
    end for;
    B := Max([Determinant(a):a in A]);
    if B lt 4096 then
        N := Max([X[k]`level:k in L]);  G := GL(2,Integers(N));
        S := AssociativeArray(); for k in L do S[k] := GL2SimilaritySet(GL2Lift(X[k]`subgroup,N)); end for;
        if #Set([S[k]:k in Keys(S)]) eq 1 then return L, true; end if;
        A cat:= GL2FrobeniusMatrices(E,4096:B0:=B+1);
        Z := {GL2SimilarityInvariant(G!a):a in A|GCD(Determinant(a),N) eq 1};
        L := [k:k in L|Z subset S[k]];
        if #L eq 1 then return L, true; end if;
        if Proof then return L, true; end if;
        Z := &meet[S[k]:k in L];
        m := #L;
        L := [k:k in L|S[k] eq Z];
        return L, #L eq m;
    end if;
    return L,true;
end intrinsic;

/*
    The code below has been copied from the file https://math.mit.edu/~drew/galrep/subgroups.m associated to [Sut16] to provide the intrinsic GL2SLabel,
    which for subgroups of prime level computes the label under the system proposed in [Sut16] https://doi.org/10.1017/fms.2015.33.
*/ 

dets:=function(H) return IsTrivial(H) select 1 else LCM([Order(Determinant(h)):h in Generators(H)]); end function;
chi:=function(g) return KroneckerSymbol(Integers()!(Trace(g)^2-4*Determinant(g)),Characteristic(BaseRing(g))); end function;

// return array whose nth entry is the least positive integer with order n mod p (requires n|(p-1))
MinReps :=function(p)
    assert IsPrime(p);
    r := PrimitiveRoot(p);
    a:=Integers(p)!r;
    A:=[p:i in [1..p-1]];
    for i in [1..p-1] do
        o:=ExactQuotient(p-1,GCD(p-1,i));
        A[o]:=Min(A[o],Integers()!a);
        a:=r*a;
    end for;
    return A;
end function;

Scalars:=function(p)
    return Center(GL(2,p));
end function;
    
IsScalar := function(H)
    for g in Generators(H) do if g[1][2] ne 0 or g[2][1] ne 0 or g[1][1] ne g[2][2] then return false; end if; end for;
    return true;
end function;

SplitCartan:=function(p)
    local r;
    r:=PrimitiveRoot(p);
    return sub<GL(2,p)|[1,0,0,r],[r,0,0,1]>;
end function;

Borel:=function(p)
    return sub<GL(2,p)|SplitCartan(p),[1,1,0,1]>;
end function;

NonSplitCartan:=function(p)
    if p eq 2 then return sub<GL(2,p)|[1,1,1,0]>; end if;
    r:=PrimitiveRoot(p);
    G:=GL(2,p);
    while true do
        x:=Random(GF(p));  y:=Random(GF(p));
        if y eq 0 then continue; end if;
        H:=sub<G|[x,r*y,y,x]>;
        if #H eq p^2-1 then break; end if;
    end while;
    return H;
end function;

NormalizerSplitCartan:=function(p)
    return sub<GL(2,p)|SplitCartan(p),[0,1,1,0]>;
end function;

NormalizerNonSplitCartan:=function(p) 
    return sub<GL(2,p)|NonSplitCartan(p),[1,0,0,-1]>;
end function;

IsDiagonal:=function(a)
    return a[1][2] eq 0 and a[2][1] eq 0;
end function;

// given diagonalizable H, returns conjugate of H that is diagonal with minimal integers a and b such that H~<[a,0,0,1/a],[b,0,0,r/b]> where r is a minimal generator for det(H)
SplitCartanConjugate := function(H:M:=[])
    local p,H0,a,H1,h,g,b;
    assert IsAbelian(H);
    assert {chi(h):h in Generators(H)} subset {0,1};
    p:=Characteristic(BaseRing(H));
    if p eq 2 then assert #H eq 1; return H; end if;
    H0:=H meet SL(2,p);
    if #M ne p-1 then M:=MinReps(p); end if;
    a:= M[#H0];                                         // least a such that <[a,0,0,1/a]> is conjugate to H meet SL(2,p)
    r:=M[dets(H)];                                      // least r that generates det(H)
    H1,pi:=quo<H|H0>;
    h:=Inverse(pi)([h:h in H1|Order(h) eq #H1][1]);
    g:=[g:g in sub<H|h>|Determinant(g) eq r][1];
    b:= Min([Min([e[1]:e in Eigenvalues(h0*g)]):h0 in H0]);
    return sub<GL(2,p)|[a,0,0,1/a],[b,0,0,r/b]>,Integers()!a,Integers()!b;
end function;

// given diagonal H, returns minimal integers a and b such that H=<[a,0,0,1/a], [b,0,0,r/b]>, where r is minimal generator for det(H)
DiagonalSubgroupGenerators:=function(H:M:=[])
    for h in Generators(H) do assert IsDiagonal(h); end for;
    p:=#BaseRing(H);
    H0:=H meet SL(2,p);
    if #M ne p-1 then M:=MinReps(p); end if;
    a:= M[#H0];                                         // least a such that <[a,0,0,1/a]> is conjugate to H meet SL(2,p)
    r:=M[dets(H)];                                      // least r that generates det(H)
    H1,pi:=quo<H|H0>;
    h:=Inverse(pi)([h:h in H1|Order(h) eq #H1][1]);
    g:=[g:g in sub<H|h>|Determinant(g) eq r][1];
    b := Min([(h0*g)[1][1]:h0 in H0]);
    return sub<GL(2,p)|[a,0,0,1/a],[b,0,0,r/b]>,Integers()!a,Integers()!b;
end function;

// given H contained in some Borel subgroup, returns conjugate of H in upper-triangular Borel
BorelConjugate := function(H:M:=[])
    local p,s,n,a,b,G,H1;
    p:=#BaseRing(H);
    if not IsDivisibleBy(Order(H),p) then return SplitCartanConjugate(H:M:=M); end if;
    // Get an element of order p
    while true do h:=Random(H); n:=Order(h); if IsDivisibleBy(n,p) then h:=h^ExactQuotient(n,p); break; end if; end while;
    G:=GL(2,p);
    b,A:=IsConjugate(G,h,G![1,1,0,1]);
    assert b;
    BH:=Conjugate(H,A);
    D:=sub<G|[G![h[1][1],0,0,h[2][2]]:h in Generators(BH)]>;
    D,a,b:=DiagonalSubgroupGenerators(D:M:=M); 
    HH:=sub<G|D,G![1,1,0,1]>;
    assert BH eq HH;
    return HH,a,b;
end function;

// given H contained in a non-split Cartan returns conjugate subgroup of standard NonSplitCartan generated by [a,b*s,b,a] where s is the minimal primitive root mod p and (a,b) is lexicograpahically minimal
NonSplitCartanConjugate := function(H:M:=[])
    local p,n,F,u,m,r,a,s,d,b,G,GL2,ZL2;
    p:=#BaseRing(H);
    assert p gt 2;
    b,g:=IsCyclic(H);
    assert b and chi(g) le 0;
    GL2:=GL(2,p);
    ZL2:=Scalars(p);
    HZ:=sub<H|g^ExactQuotient(Order(g),GCD(Order(g),p-1))>;
    if #M ne p-1 then M:=MinReps(p); end if;
    if IsScalar(H) then
        z:=M[#HZ];
        G:=sub<H|[z,0,0,z]>;
        assert G eq H;
        return G,z,0;
    end if;
    n:=ExactQuotient(#H,#HZ);
    F:=GF(p^2);
    u:=Integers(p)!(2+Trace(RootOfUnity(n,F)));
    m:=dets(H);
    r:=Integers(p)!M[m];
    maxdets := [r^i: i in [1..m]|GCD(m,i) eq 1];
    s:=Integers(p)!M[p-1];
    if u eq 0 then
        a:=0;
        B:=[Sqrt(-d/s):d in maxdets];
        B:= B cat [-b:b in B];
        I:=[i:i in [1..#B]|sub<ZL2|(GL2![0,B[i]*s,B[i],0])^2> eq HZ];
        b:=Min([B[i]:i in I]);
    else
        A:=[Sqrt(d*u)/2:d in maxdets];
        A:=A cat [-a:a in A];
        B:=[Sqrt((a^2-4*a^2/u)/s):a in A];
        I:=[i:i in [1..#A]|sub<ZL2|(GL2![A[i],B[i]*s,B[i],A[i]])^n> eq HZ];
        a:=Min([A[i]:i in I]);
        b:=Sqrt((a^2-4*a^2/u)/s);
        b:=Min([b,-b]);
    end if;
    G:=sub<GL2|[a,b*s,b,a]>;
    assert IsConjugate(GL2,G,H);
    return G,Integers()!a,Integers()!b;
end function;
    
// Given H with dihedral projective image conjugate to a subgroup of the normalizer of a split Cartan, returns conjugate subgroup in the normalizer of the standard SplitCartan
// If H meet SL(2,p) is in the Cartan, returns minimal a and b such that H=<[a,0,0,1/a],[0,b,-r/b,0]> where r is minimal generator of det(H)
// Otherwise returns minimal a,b,c such that H=<[a,0,0,1/a],[0,b,-1/b,0],[0,c,-r/c,0]>
NormalizerSplitCartanConjugate := function(H:M:=[])
    local p,GL2,SL2,ZL2,G,G0,H1,B,S,a,b,c,d,e,g;
    p:=#BaseRing(H);
    GL2:=GL(2,p);
    SL2:=SL(2,p);
    HZ:=H meet Scalars(p);
    // pick an index 2 abelian subgroup of H; if there is more than one choice (as permittedy by Lemma 3.16 of [Sut16]), opt for the cyclic choice.
    S:=[G`subgroup:G in MaximalSubgroups(H:IsAbelian:=true,IndexEqual:=2)|{chi(g):g in Generators(G`subgroup)} subset {0,1}];
    assert #S gt 0;
    i:=0; for j in [1..#S] do if IsCyclic(S[j]) then i:=j; break; end if; end for;
    G0:= i ne 0 select S[i] else S[1];
    if #M ne p-1 then M:=MinReps(p); end if;
    G,a,b:=SplitCartanConjugate(G0:M:=M);
    B:=GL2![b,0,0,M[dets(G)]/b];
    // Use Corollary 3.17 of [Sut16] to distinguish the two subgroups of C^+ that intersect C in G, one will have det(G)=-det(H-G0) and the other will have det(G) and -det(H-G0) disjoint
    g:=GL2![0,1,1,0];
    repeat x:=Random(H); until not x in G0;
    if IsDivisibleBy(dets(G),Order(-Determinant(x)))  then
        e:=0; H1:=sub<GL2|G,g>;
    else
        d:=GL2![1,0,0,M[p-1]];  e:=ExactQuotient(p-1,#HZ);  g:=g*d^e; H1:=sub<GL2|G,g>;
    end if;
    r:=GF(p)!M[dets(H)];
    S:=[h:h in Generators(H1 meet SL2)|not h in G];
    g:=[B^i*g:i in [1..dets(G)]|Determinant(B^i*g) eq r][1];
    c:=Min([(h*g)[1][2]:h in sub<GL2|[a,0,0,1/a]>]);
    if #S eq 0 then
        G:=sub<GL2|[a,0,0,1/a],[0,c,-r/c,0]>;
        assert IsConjugate(GL2,G,H);
        return G,Integers()!a,Integers()!c,0;
    else
        b:=Min([(S[1]*h)[1][2]:h in sub<GL2|[a,0,0,1/a]>]);
        G:=sub<GL2|[a,0,0,1/a],[0,b,-1/b,0],[0,c,-r/c,0]>;
        assert IsConjugate(GL2,G,H);
        return G,Integers()!a,Integers()!b,Integers()!c;
    end if;
end function;
    
// Given H with dihedral projective image conjugate to a subgroup of the normalizer of a non-split Cartan, returns conjugate subgroup in the normalizer of the standard NonSplitCartan
// If H meet SL(2,p) is in the Cartan, returns minimal a and b such that H=<[a,b*s,b,a],[1,0,0,-1]*d^e> where s is minimal generator of det(H) and d is a generator for the NonSplitCartan
NormalizerNonSplitCartanConjugate := function(H:M:=[])
    local p,GL2,G0,G,a,b,c,d,e,g;
    p:=#BaseRing(H);
    GL2:=GL(2,p);
    G0:=[G`subgroup:G in MaximalSubgroups(H:IsAbelian:=true,IndexEqual:=2)|{chi(g):g in Generators(G`subgroup)} subset {0,-1}][1];   // take any maximal abelian index 2 subgroup
    if #M ne p-1 then M:=MinReps(p); end if;
    G,a,b:=NonSplitCartanConjugate(G0:M:=M);
    HZ:=G meet Scalars(p);
    // Use Corollary 3.17 of [Sut16] to distinguish the two subgroups of C^+ that intersect C in G, one will have det(G)=-det(H-G0) and the other will have det(G) and -det(H-G0) disjoint
    g:=GL2![1,0,0,-1];
    repeat x:=Random(H); until not x in G0;
    if IsDivisibleBy(dets(G),Order(-Determinant(x)))  then
        e:=0; H1:=sub<GL2|G,g>;
    else
        d:=NonSplitCartan(p).1;  e:=ExactQuotient(p-1,#HZ);  H1:=sub<GL2|G,g*d^e>;
    end if;
    return H1,Integers()!a,Integers()!b,Integers()!e;
end function;

GroupLetters:=["G","B","Cs","Cn","Ns","Nn","A4","S4","A5"];

// id format is [p,d,n,a,b,c] where p is characteristic, d is (p-1)/#det(G), n+1 is an index into GroupLetters, and a,b,c are nonnegative integers as defined in the paper

GroupLabelFromId:=function(id)
    assert #id ge 3;
    assert IsDivisibleBy(id[1]-1,id[2]);
    // special case for S4, needed for backward compatibiliy, suppress the .2 (which is the typical case and only case with full det)
    if id[3] eq 7 and id[4] eq 2 then
        if id[2] eq 1 then return Sprintf("%o%o",id[1],GroupLetters[8]); else return Sprintf("%o%o[%o]",id[1],GroupLetters[8],id[2]); end if;
    end if;
    if id[2] eq 1 then
        if #id eq 3 then return Sprintf ("%o%o",id[1],GroupLetters[id[3]+1]); end if;
        if #id eq 4 then return Sprintf ("%o%o.%o",id[1],GroupLetters[id[3]+1],id[4]); end if;
        if #id eq 5 then return Sprintf ("%o%o.%o.%o",id[1],GroupLetters[id[3]+1],id[4],id[5]); end if;
        if #id eq 6 then return Sprintf ("%o%o.%o.%o.%o",id[1],GroupLetters[id[3]+1],id[4],id[5],id[6]); end if;
    else
        if #id eq 3 then return Sprintf ("%o%o[%o]",id[1],GroupLetters[id[3]+1],id[2]); end if;
        if #id eq 4 then return Sprintf ("%o%o.%o[%o]",id[1],GroupLetters[id[3]+1],id[4],id[2]); end if;
        if #id eq 5 then return Sprintf ("%o%o.%o.%o[%o]",id[1],GroupLetters[id[3]+1],id[4],id[5],id[2]); end if;
        if #id eq 6 then return Sprintf ("%o%o.%o.%o.%o[%o]",id[1],GroupLetters[id[3]+1],id[4],id[5],id[6],id[2]); end if;
    end if;
    assert false;
end function;

GL2SubgroupID := function(H:PH:=[],M:=[])
    local p,GL2,SL2,ZL2,PG,pi,d,G,a,b;
    p := #BaseRing(H);
    if p eq 2 then
        if #H eq 1 then return [p,1,2]; end if;
        if #H eq 2 then return [p,1,1]; end if;
        if #H eq 3 then return [p,1,3]; end if;
        assert #H eq 6;
        return [p,1,0];
    end if;
    assert IsPrime(2);
    H:=ChangeRing(H,GF(p));
    GL2:=GL(2,p);
    SL2:=SL(2,p);
    d := ExactQuotient(p-1,ExactQuotient(#H, #(H meet SL2)));
    if SL2 subset H then return [p,d,0]; end if;
    HZ:=H meet Scalars(p);
    if #M ne p-1 then M:=MinReps(p); end if;
    if #H mod p eq 0 then
        if d*#H eq p*(p-1)^2 then return [p,d,1]; end if;
        G,a,b:=BorelConjugate(H);
        return [p,d,1,a,b];
    end if;
    if ExactQuotient(#H,#HZ) le 60 then
        PH:=quo<H|H meet HZ>;
        if IsIsomorphic(PH,AlternatingGroup(4)) then
            if dets(H) eq dets(HZ) then
                return [p,d,6,1];
            else
                assert 3*dets(HZ) eq dets(H);
                assert p mod 3 eq 1;
                return [p,d,6,3];
            end if;
        end if;
        if IsIsomorphic(PH,SymmetricGroup(4)) then
            if dets(H) eq 2*dets(HZ) then
                return [p,d,7,2];
            else
                assert d gt 1;
                assert dets(HZ) eq dets(H);
                return [p,d,7,1];
            end if;
        end if;
        if IsIsomorphic(PH,AlternatingGroup(5)) then
            assert p^2 mod 5 eq 1;
            assert dets(H) eq dets(HZ);
            return [p,d,8,1];
        end if;
    end if;
    if #PH eq 0 then PH:=quo<H|H meet HZ>; end if;
    if IsCyclic(PH) then
        if {chi(h):h in Generators(H)} subset {0,1} then
            if d*#H eq (p-1)^2 then return [p,d,2]; end if;
            G,a,b:=SplitCartanConjugate(H);
            return [p,d,2,a,b];
        else
            assert {chi(h): h in Generators(H)} subset {0,-1};
            if d*#H eq p^2-1 then return [p,d,3]; end if;
            H1,a,b:=NonSplitCartanConjugate(H);
            return [p,d,3,a,b];
        end if;
    end if;
    S:= [G`subgroup:G in MaximalSubgroups(H:IsAbelian:=true,IndexEqual:=2)|{chi(g):g in Generators(G`subgroup)}subset {0,1}];
    if #S ge 1 then
        H1,a,b,c:=NormalizerSplitCartanConjugate(H);
        if d*#H1 eq 2*(p-1)^2 then return [p,d,4]; end if;
        if c  gt 0 then return [p,d,4,a,b,c]; else return [p,d,4,a,b]; end if;
    end if;
    H1,a,b,c:=NormalizerNonSplitCartanConjugate(H);
    if d*#H1 eq 2*(p^2-1) then return [p,d,5]; end if;
    if c gt 0 then return [p,d,5,a,b,c]; else return [p,d,5,a,b]; end if;
end function;

intrinsic GL2SLabel(H::GrpMat,p::RngIntElt) -> MonStgElt
{ The label of H in GL(2,p) under the system defined by Sutherland in "Computing images of Galois representations attached to elliptic curves, Forum. Math. Sigma 4(2016) e4, https://doi.org/10.1017/fms.2015.33". }
    require IsPrime(p): "p must be prime.";
    return GroupLabelFromId(GL2SubgroupID(GL2Project(H,p)));
end intrinsic;
