/*
    This file implements the following functions:

        GL2Data(l) -- computes l-power level subgroup data that includes all arithmetically maximal subgroups.
                      Set the optional parameter "outfile" to write the results to a file
        GL2Load(l) -- loads subgroup data created by GL2Data, returning an associative array X indexed by label.
                      The input parameter can be either a prime l (indicating the file gl2_ladic.txt) or a filename.
                      Specify l=0 (indicating the file gl2_Qcheck.txt) to load data for all ell-adic images known to occur for non-CM E/Q
        GL2LoadExamples() -- loads a list of elliptic curves that realize each non-trivial ell-adic image known to occur for non-CM E/Q
        GL2LoadCMExamples() -- loads a list of elliptic curves that realize each non-trivial ell-adic image known to occur for CM E/Q
        GL2EllAdicImages(E,X) -- computes a list of the non-maximal ell-adic images for a given E/Q (for all primes ell),
                                 given the associative array X returned by GL2Load(0);

    Precomputed files available to GL2Load include gl2_*adic.txt for * in 2,3,5,7,...,37, gl2_big2adic.txt, and gl2_Qcheck.txt.

    Subgroups of GL_2(Zhat) with determinant index 1 are identified by labels of the form N.i.g.n,
    where N is the level, i is the index, g is the genus, and n is a (deterministic) tie-breaker.
    These labels are computed by GL2Data.  See gl2rec for details on the data available for each subgroup.

    The total time to compute GL2Data(p) for p in 3,5,7,11,...,37 is arouond an hour.
    GL2Data(2) takes aroound 6 hours, but only about 1 if you set Cheat:=true (this will make it use level=32, index=96 as bounds rather than level=64, index=192).

    This code relies on three external datafiles:

        cmfdata.txt -- newform data for prime power levels 2,..,37
        cpdata.txt -- Cummins-Pauli labels for subgroups of PSL(2,Z)
        rzbdata.txt -- Rouse-Zureick-Brown labels for 2-adic subgroups
*/


// this record format extends that of the record form gl2node defined in gl2.m (names need to be compatible!)
gl2rec := recformat<
    label:MonStgElt,        // label of the form N.i.g.n or N.i.g.d.n
    level:RngIntElt,        // level N
    index:RngIntElt,        // index i
    genus:RngIntElt,        // genus g
    dlabel:MonStgElt,       // label of det(H) as a subgroup of GL(1,Zhat)
    zlabel:MonStgElt,       // label of scalar subgroup of H as a subgroup of GL(1,Zhat)
    subgroup:GrpMat,        // subgroup of GL(2,N)
    children:SeqEnum,       // labels of maximal subgroups up to index bound
    missing:BoolElt,        // true if not every maximal subgroup with the same determinant is listed in children
    parents:SeqEnum,        // labels of groups of which this is a maximal subgroup
    reductions:SeqEnum,     // labels of reductions modulo proper divisors of N (in order)
    orbits:SeqEnum,         // orbit signature: sorted list of triples (e,s,m) where e=exponent, s=size, m=multiplicity of H-orbits of (Z/NZ)^2
    korbits:SeqEnum,        // Kummer orbit signature: sorted list of triples (e,s,m) of H-orbits of (Z/NZ)^2/<-I> (N-division polynomial factorization)
    iorbits:SeqEnum,        // isogeny orbit signature: sorted list of triples (e,s,m) of H-orbits of the cyclic submodules of (Z/NZ)^2
    qtwists:SeqEnum,        // list of labels of subgroups K for which <K,-I> = <H,-I>, corresponding to quadratic twists
    obstructions:SeqEnum,   // sorted list of places p for which X_H(Q_p) has no local points, with p=0 for R (only set for full determinant)
    cusps:RngIntElt,        // number of cusp orbits
    ratcusps:RngIntElt,     // number of Q-rational cusp orbits
    gclass:SeqEnum,         // list of labels of Gassmann equivalent subgroups K (those that induce isomorphic permutation modules)
    CPlabel:MonStgElt,      // Cummins-Pauli label of H cap SL_2(Z) (as defined in [CP03a,CP03b], available for g <= 24)
    Slabel:MonStgElt,       // Sutherland label of prime level H (as defined in [Sut16] and used in the LMFDB)
    SZlabel:MonStgElt,      // Sutherland-Zywina label for group containing -I that correspond to curves with infinitely many rational points
    RZBlabel:MonStgElt,     // Rouse and Zureick-Brown label of 2-adic H (as defined in [RZB15] and used in the LMFDB)
    newforms:SeqEnum,       // list of LMFDB labels of newform orbits [f] st J_H ~ prod_f A_f (each f may occur with multiplicity)
    dims:SeqEnum,           // list of dimension of the newform orbits [f] in newforms (in matching order)
    rank:RngIntElt,         // analytic rank of J_H
    model:MonStgElt,        // for genus one curves whose Jacobian has positive rank this is the Cremona label of an elliptic curve isomorphic to X_H
    jmap:RngElt,            // for H containing -I if X_H(Q) is infinite jmap:X_H->X(1) is an element of Q(t) (genus 0) or of Q(y)(x) (genus 1)
    Emap:SeqEnum,           // for genus zero H not containing -I with X_H(Q) infinite a pair [A(t),B(t)] defining the universal E:y^2=x^3+A(t)x+B(t).
    sset:Assoc              // set of similarity invariants identifying the conjugacy classes in H (only set when requested)
>;

/* parsing functions that are faster and safer than using eval */
function strip(s) return Join(Split(Join(Split(s," "),""),"\n"),""); end function;
function atoi(s) return StringToInteger(s); end function;
function atoii(s) return [Integers()|StringToInteger(n):n in Split(t[2..#t-1],",")] where t:=strip(s); end function;
function atoiii(s)
    return [[Integers()|StringToInteger(n):n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r] where r := Split(t[2..#t-1],"[") where t:= strip(s);
end function;
function labels(s) return Split(s[2..#s-1],","); end function;

function curly(s) 
    // Split omits the last field if it is empty even when IncludeEmpty is set (which makes no sense!), so we work around this by padding if needed
    t := Join(Split(Join(Split(s,"[":IncludeEmpty),"{"),"]":IncludeEmpty),"}");
    if #t lt #s and s[#s] eq "]" then t cat:="}";  end if; // don't check for trailing [, this shouldn't happen, and if it does assert below will fail
    assert #s eq #t;
    return t;
end function;

function sprint(X)
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end function;

function index(S,f:Project:=func<x|x>,Unique:=false)
    A := AssociativeArray();
    if Unique then
        for x in S do A[f(x)] := Project(x); end for;
    else
        for x in S do y := f(x); A[y] := IsDefined(A,y) select Append(A[y],Project(x)) else [Project(x)]; end for;
    end if;
    return A;
end function;

function GL2RecClean(r:blank:=false)
    empty := blank select "" else "-";    
    if r`CPlabel eq empty then delete r`CPlabel; end if;
    if r`SZlabel eq empty then delete r`SZlabel; end if;
    if r`model eq empty then delete r`model; delete r`jmap; end if;
    if r`Emap eq [] then delete r`Emap; end if;
    if r`RZBlabel eq empty then delete r`RZBlabel; end if;
    if r`genus eq 0 then delete r`rank; end if;
    return r;
end function;

function GL2RecFill(r:blank:=false)
    empty := blank select "" else "-";
    if r`genus gt 24 then r`CPlabel:=empty; else assert r`CPlabel ne ""; end if;
    if not GL2QInfinite(r:MustContainNegativeOne) then r`SZlabel := empty; r`model := empty; r`jmap:= 0; else assert r`SZlabel ne ""; end if;
    if not GL2QInfinite(r) or GL2ContainsNegativeOne(r`subgroup) then r`Emap := []; end if;
    if not assigned r`RZBlabel then r`RZBlabel := empty; end if;
    if r`RZBlabel eq "" or PrimeDivisors(r`level) ne [2] then r`RZBlabel := empty; end if;
    if r`genus eq 0 then r`rank:=-1; r`newforms:=[]; end if;
    return r;
end function;

function GL2RecToString(r)
    r := GL2RecFill(r);
    return Join([r`label,sprint(r`level),sprint(r`index),sprint(r`genus),r`dlabel,r`zlabel,sprint(GL2Generators(r`subgroup)),
                 sprint(r`children),r`missing select "1" else "0", sprint(r`parents),sprint(r`reductions),sprint(r`orbits),sprint(r`korbits),sprint(r`iorbits),
                 sprint(r`qtwists),sprint(r`obstructions),sprint(r`cusps),sprint(r`ratcusps),sprint(r`gclass),r`CPlabel,r`Slabel,r`SZlabel,r`RZBlabel,
                 sprint(r`newforms),sprint(r`dims),sprint(r`rank),r`model,sprint(r`jmap),sprint(r`Emap)],":");
end function;

function GL2RecFromString(s:sset:=false,slevel:=37)
    s := Split(s,":");
    N := atoi(s[2]); H := GL2FromGenerators(N,atoiii(s[7]));
    Ft<t> := FunctionField(Rationals());  Fx<x> := FunctionField(Rationals());  Fy<y> := FunctionField(Fx);
    r := rec<gl2rec|label:=s[1],level:=N,index:=atoi(s[3]),genus:=atoi(s[4]),dlabel:=s[5],zlabel:=s[6],subgroup:=H,children:=labels(s[8]),missing:=s[9] eq "1",
                    parents:=labels(s[10]),reductions:=labels(s[11]),orbits:=atoiii(s[12]),korbits:=atoiii(s[13]),iorbits:=atoiii(s[14]),qtwists:=labels(s[15]),
                    obstructions:=atoii(s[16]),cusps:=atoi(s[17]),ratcusps:=atoi(s[18]),gclass:=labels(s[19]),CPlabel:=s[20],Slabel:=s[21],
                    SZlabel:=s[22],RZBlabel:=s[23],newforms:=labels(s[24]),dims:=atoii(s[25]),rank:=atoi(s[26]),model:=s[27],jmap:=eval(s[28]),Emap:=eval(s[29])>;
    if r`genus eq 1 then r`jmap := Fy!r`jmap; end if;
    if sset and N gt 1 and PrimeDivisors(N)[1] le slevel then r`sset := AssociativeArray(); r`sset["cache"] := GL2SimilaritySet(r`subgroup); end if;
    return GL2RecClean(r);
end function;

procedure GL2LMFDBDump(filename,X)
    function strings(r) return sprint(["\"" cat k cat "\"":k in r]); end function;
    fp := Open(filename,"w");
    Puts(fp,"label:level:index:genus:determinant_label:scalar_label:generators:children:missing_children:parents:reductions:orbits:kummer_orbits:isogeny_orbits:quadratic_twists:obstructions:cusps:rational_cusps:gassmann_class:CPlabel:Slabel:SZlabel:RZBlabel:newforms:dims:rank:model:jmap:Emap");
    Puts(fp,"text:integer:integer:integer:text:text:integer[]:text[]:boolean:text[]:text[]:integer[]:integer[]:integer[]:text[]:integer[]:integer:integer:text[]:text:text:text:text:text[]:integer[]:integer:text:text:text[]");
    Puts(fp,"");
    F<t> := FunctionField(Rationals());
    for k in GL2SortLabels([k:k in Keys(X)]) do
        r := GL2RecFill(X[k]:blank:=true);
        s := curly(Join([r`label,sprint(r`level),sprint(r`index),sprint(r`genus),r`dlabel,r`zlabel,sprint(GL2Generators(r`subgroup)),
                 strings(r`children),r`missing select "1" else "0", strings(r`parents),strings(r`reductions),sprint(r`orbits),sprint(r`korbits),
                 sprint(r`iorbits),sprint(r`qtwists),sprint(r`obstructions),sprint(r`cusps),sprint(r`ratcusps),sprint(r`gclass),r`CPlabel,r`Slabel,
                 r`SZlabel,r`RZBlabel,strings(r`newforms),sprint(r`dims),sprint(r`rank),r`model,sprint(r`jmap),strings([sprint(c):c in r`Emap])],":"));
        Puts(fp,s);
    end for;
    Flush(fp);
end procedure;

cmfrec := recformat<
    label:MonStgElt,
    level:RngIntElt,
    cond:RngIntElt,
    dim:RngIntElt,
    rank:RngIntElt,
    hash:FldFinElt,
    traces:SeqEnum>;

function CMFLabelCompare(s,t)
    a := Split(s,".");  b := Split(t,".");
    if a[1] ne b[1] then return atoi(a[1]) - atoi(b[1]); end if;
    if a[2] ne b[2] then return atoi(a[2]) - atoi(b[2]); end if;
    if a[3] ne b[3] then return a[3] lt b[3] select -1 else 1; end if;
    if a[4] ne b[4] then return  a[4] lt b[4] select -1 else 1; end if;
    return 0;
end function;

// expected file format is label:level:cond:dim:rank:hash:traces
function CMFLoad(p,maxN:cmfdatafile:="cmfdata.txt")
    S := [Split(s,":"): s in Split(Read(cmfdatafile))];
    S := [r:r in S|IsPrimePower(N) and IsDivisibleBy(N,p) and N le maxN^2 where N:=atoi(r[2]) ];
    S := [rec<cmfrec|label:=r[1],level:=atoi(r[2]),cond:=atoi(r[3]),dim:=atoi(r[4]),rank:=atoi(r[5]),hash:=GF(2^61-1)!atoi(r[6]),traces:=eval(r[7])> : r in S];
    X := AssociativeArray();
    for r in S do X[r`label] := r; end for;
    return X;
end function;

// file format is CPlabel:level:gens
function CPLoad(p,maxN:cpdatafile:="cpdata.txt")
    S := [Split(s,":") : s in Split(Read(cpdatafile))];
    return [<r[1],GL2FromGenerators(atoi(r[2]),eval(r[3]))> : r in S | N le maxN and (N eq 1 or (IsPrimePower(N) and IsDivisibleBy(N,p))) where N:=atoi(r[2])];
end function;

// file format is RZBlabel:level:gens
function RZBLoad(p,maxN,maxI:rzbdatafile:="rzbdata.txt")
    if p ne 2 then return []; end if;
    S := [Split(s,":") : s in Split(Read(rzbdatafile))];
    S := [<r[1],GL2FromGenerators(atoi(r[2]),eval(r[3]))> : r in S | atoi(r[2]) le maxN];
    return [r : r in S|GL2Index(r[2]) le maxI];
end function;

// file format is SZlabel:level:gens:curve:map
function SZLoad(p:szdatafile:="szdata.txt")
    Ft<t> := FunctionField(Rationals());  Fx<x> := FunctionField(Rationals()); Fy<y> := FunctionField(Fx);
    S := [Split(s,":") : s in Split(Read(szdatafile))];
    X := AssociativeArray();
    for r in S do
        if p gt 0 and atoi(r[2]) ne 1 and atoi(r[2]) mod p ne 0 then continue; end if;
        X[r[1]]:= <GL2FromGenerators(atoi(r[2]),eval(r[3])),r[4],eval(r[5])>;
    end for;
    return X;
end function;

// file format is SZlabel:level:gens:curve:map
function FMLoad(p:fmdatafile:="fmdata.txt")
    S := [Split(s,":") : s in Split(Read(fmdatafile))];
    X := AssociativeArray();
    R := PolynomialRing(Rationals()); F<t> := FunctionField(Rationals());
    for r in S do
        if p gt 0 then N := atoi(Split(r[1],".")[1]); if N mod p ne 0 then continue; end if; end if;
        ab := eval(r[2]);
        X[r[1]]:= [F!R!ab[1],F!R!ab[2]];
    end for;
    return X;
end function;

function bound(X,N,g)
    Z := Sort([r:r in X|r`dim le g and r`level le N^2 and r`cond le N],func<a,b|a`dim ne b`dim select a`dim-b`dim else (a`traces le b`traces select -1 else 1)>);
    assert #Z gt 0;
    badp := Set(PrimeDivisors(N)); badi := {#PrimesUpTo(p):p in badp};
    maxi := #Z + #badi - 1;
    while true do
        A := Matrix([[r`dim] cat [r`traces[i]:i in [1..maxi]|not i in badi]:r in Z]);
        if Dimension(Nullspace(A)) eq 0 then break; end if;
        maxi := Ceiling(1.5*maxi);
    end while;
    if maxi eq 1 then return #Z, maxi, NthPrime(maxi); end if;
    while Dimension(Nullspace(A)) eq 0 do
        maxi -:= 1;
        assert maxi gt 0;
        A := Matrix([[r`dim] cat [r`traces[i]:i in [1..maxi]|not i in badi]:r in Z]);
    end while;
    maxi +:= 1;
    A := Matrix([[r`dim] cat [r`traces[i]:i in [1..maxi]|not i in badi]:r in Z]);
    print "";
    print ["\\mflabel{" cat r`label cat "}":r in Z];
    print Transpose(A);
    return #Z, maxi, NthPrime(maxi);
end function;

function GL2NewformDecomposition(X,H:g:=-1)
    dindex := GL2DeterminantIndex(H);
    N,H := GL2Level(H);
    if g eq -1 then g := GL2Genus(H); end if;
    if g eq 0 then return [], [], -1; end if;
    g *:= dindex;
    Z := [r:r in X|r`dim le g and r`level le N^2 and r`cond le N];
    m := Min([#r`traces:r in Z]);
    I := AssociativeArray(); P := [p : p in PrimesInInterval(1,NthPrime(m))];
    for i := 1 to #P do I[P[i]]:=i; end for;
    maxi := Ceiling(2*#Z+10);  B0:=1;
    t := [g]; P := [];
    while true do
        if maxi gt #I then maxi := #I; end if;
        maxp := NthPrime(maxi);
        Q := [p : p in PrimesInInterval(B0,maxp)|N mod p ne 0];  B0 := maxp+1;
        P cat:= Q; t cat:= GL2Traces(H,Q);
        b := Vector(t);
        A := Matrix([[r`dim] cat [r`traces[I[p]]:p in P]:r in Z]);
        try x,K := Solution(A,b); catch e; return [],[], -2; end try;
        // printf "Using %o columns, dimension %o\n", Degree(b), Dimension(K);
        if Dimension(K) eq 0 then
            forms := Sort([s:s in {* Z[i]`label^^x[i]:i in [1..Degree(x)] *}], CMFLabelCompare);
            dims := [X[f]`dim:f in forms];
            assert &+dims eq g;
            rank := &+[X[f]`rank:f in forms]; // note that cmfdata.txt stores the rank of the Galois orbit
            return forms, dims, rank;
        end if;
        if maxi eq #I then return [],[],-3; end if;
        maxi := Ceiling(1.5*maxi);
    end while;
end function;

CMIndexBounds := [<2,384>,<3,1944>,<5,30>,<7,84>,<11,165>,<13,273>,<17,153>,<19,360>,<23,759>,<29,1218>,<31,1488>,<37,703>];

// Output file format is label:gens:children:parents:orbits:iorbits:ccsig:sl2twists:qtwists:obstructions:cusps:ratcusps:iclass:rank:cplabel:forms:dims
// Currently we only fill in iclass:forms:dims:rank for genus 1
function GL2Data(p:cmfdatafile:="cmfdata.txt",cpdatafile:="cpdata.txt",rzbdatafile:="rzbdata.txt",szdatafile:="szdata.txt",fmdatafile:="fmdata.txt",outfile:="",Cheat:=false,CM:=false,DeterminantLabel:="1.1.1",maxN:=0,maxI:=0)
    assert IsPrime(p);
    t := Cputime(); s:=t;
    if maxN eq 0 or maxI eq 0 then
        if Cheat and p eq 2 then
            maxN := 32;  maxI := 96;
            printf "Cheating by using previously computed arithmetically maximal level bound %o and index bound %o\n", maxN, maxI;
        elif Cheat and p eq 3 then
            maxN := 27;  maxI := 729;
            printf "Cheating by using previously computed arithmetically maximal level bound %o and index bound %o\n", maxN, maxI;
        else
            if Cheat then print "Not cheating (there is no real advantage to doing so)."; end if;
            maxN,maxI := GL2ArithmeticallyMaximalBounds(p);
            printf "Computed arithmetically maximal level bound %o and index bound %o in %.3os\n", maxN, maxI, Cputime()-s; s:=Cputime();
        end if;
    end if;
    if CM then
        if p le 37 then
            I := [r[2]:r in CMIndexBounds|r[1] eq p][1];
        else
            I := Max([GL2Index(H):H in GL2CMTwists(p)]);
        end if;
        if I gt maxI then printf "Increasing index bound from %o to %o to handle CM cases\n", maxI, I; maxI := I; end if;
    end if;
    try cmfdata := CMFLoad(p,maxN:cmfdatafile:=cmfdatafile); catch e; cmfdata:=[]; printf "Unable to find/read file '%o', newform decompositions will not be computed (use cmfdatafile to specify an alternate location)\n", cmfdatafile; end try;
    try cpdata := CPLoad(p,maxN:cpdatafile:=cpdatafile); catch e; cpdata:=[]; printf "Unable to find/read file '%o', CP labels will not be set (use cpdatafile to specify an alternate location)\n", cpdatafile; end try;
    try rzbdata := RZBLoad(p,maxN,maxI:rzbdatafile:=rzbdatafile); catch e; rzbdata:=[]; printf "Unable to find/read file '%o', RZB labels will not be set (use rzbdatafile to specify an alternate location)\n", rzbdatafile; end try;
    try szdata := SZLoad(p:szdatafile:=szdatafile); catch e; szdata:=AssociativeArray(); printf "Unable to find/read file '%o', SZ labels and jmaps will not be set (use szdatafile to specify an alternate location)\n", szdatafile; end try;
    try fmdata := FMLoad(p:fmdatafile:=fmdatafile); catch e; fmdata:=AssociativeArray(); printf "Unable to find/read file '%o', fine maps will not be set (use fmdatafile to specify an alternate location)\n", fmdatafile; end try;
    X := GL2Lattice(maxN,maxI:DeterminantLabel:=DeterminantLabel,Verbose);
    L := GL2SortLabels([k:k in Keys(X)]);
    T := [X[k]:k in L];
    printf "Computed subgroup lattice and labels for %o groups in %.3os\n", #L, Cputime()-s; s:=Cputime();
    missing := [k eq "1.1.0.1" select false else #[H:H in MaximalSubgroups(X[k]`subgroup)|H`order * maxI lt GL2Size(X[k]`level)] gt 0 : k in L];
    printf "Computed maximal subgroups of %o groups in %.3os\n", #L, Cputime()-s; s:=Cputime();
    reductions := [GL2SortLabels([GL2LookupLabel(X,GL2RelativeProject(T[i]`subgroup,T[i]`level div p^e)) :e in [1..Valuation(T[i]`level,p)-1]]):i in [1..#T]];
    printf "Computed reduction labels for %o groups in %.3os\n", #T, Cputime()-s; s:=Cputime();
    for i:=1 to #T do if T[i]`level gt 1 then T[i]`subgroup := GL2Standardize(T[i]`subgroup); end if; end for;
    printf "Standardized generators for %o groups in %.3os\n", #T, Cputime()-s; s:=Cputime();
    qtwists := [GL2LookupLabel(X,GL2GenericQuadraticTwist(T[i]`subgroup):g:=T[i]`genus) : i in [1..#T]];
    Z := index([1..#L],func<i|qtwists[i]>);
    qtwists := [GL2SortLabels([L[j] : j in Z[qtwists[i]]]) : i in [1..#qtwists]];
    printf "Computed %o quadratic twists of %o subgroups in %.3os\n", &+[#r:r in qtwists], #T, Cputime()-s; s:=Cputime();
    cplabels := ["":i in [1..#T]];
    if #cpdata gt 0 then
        Z := index(cpdata,func<r|<SL2Level(r[2]),SL2Index(r[2]),GL2Genus(r[2]),GL2OrbitSignature(r[2])>>);
        function cplabel(H,genus)
            if genus gt 24 then return ""; end if;
            if SL2Index(H) eq 1 then return "1A0"; end if;
            N,H := SL2Level(sub<GL(2,BaseRing(H))|H,-Identity(H)>);
            k := <N,SL2Index(H),genus,GL2OrbitSignature(H)>;
            if not IsDefined(Z,k) then return "?"; end if;
            I := Z[k]; if #I eq 1 then return I[1][1]; end if;
            I := [r:r in I|IsConjugate(SL2,r[2],H)] where SL2 := SL(2,Integers(N));
            return #I eq 0 select "" else I[1][1];
        end function;
        cplabels := [cplabel(T[i]`subgroup,T[i]`genus):i in [1..#T]];
        printf "Computed %o CPlabels in %.3os\n", #[s:s in cplabels|s ne ""], Cputime()-s; s:=Cputime();
    end if;
    if #rzbdata gt 0 then
        Z := index(rzbdata,func<r|GL2LookupLabel(X,GL2Transpose(r[2]))>:Project:=func<r|r[1]>,Unique);
        rzblabels := [IsDefined(Z,k) select Z[k] else "" : k in L];
        printf "Computed %o RZBlabels in %.3os\n", #[x:x in rzblabels|x ne ""], Cputime()-s; s:=Cputime();
    end if;
    slabels := [GL2SLabel(X[k]`subgroup,p) : k in L];
    printf "Computed %o Slabels in %.3os\n", #[x:x in slabels|x ne ""], Cputime()-s; s:=Cputime();
    szlabels := ["": k in L];
    if #szdata gt 0 then
        Z := index([k:k in Keys(szdata)],func<k|GL2LookupLabel(X,szdata[k][1])>:Unique);
        szlabels := [IsDefined(Z,k) select Z[k] else "" : k in L];
        printf "Computed %o SZlabels in %.3os\n", #[x:x in szlabels|x ne ""], Cputime()-s; s:=Cputime();
    end if;
    cusps := [0:i in [1..#T]];
    for i in [1..#T] do cusps[i] := GL2CuspCount(T[i]`subgroup); end for;
    printf "Counted cusps in %.3os\n", Cputime()-s; s:=Cputime();
    ratcusps := [0:i in [1..#T]];
    for i in [1..#T] do ratcusps[i] := GL2RationalCuspCount(T[i]`subgroup); end for;
    printf "Counted rational cusps in %.3os\n", Cputime()-s; s:=Cputime();
    obs := [[]:i in [1..#T]];
    iclasses := ["":i in [1..#T]];  ranks := [-1:i in [1..#T]]; n:=0;
    // We know a posteriori that there are no arithmetic obstructions with p > 1000 among the groups summarized in Table 4
    // If we only care about arithmetically maximal groups we could use B=100, but this doesn't really save any time
    if DeterminantLabel eq "1.1.1" then
        for i in [1..#T] do if ratcusps[i] eq 0 then obs[i] := GL2QObstructions(T[i]`subgroup:B:=1000); end if; end for;
        printf "Identified local obstructions in %.3os\n", Cputime()-s; s:=Cputime();
        for i in [1..#T] do if T[i]`genus eq 1 then e,r := GL2IsogenyClass(T[i]`subgroup); iclasses[i]:= e; ranks[i]:=r; n+:=1; end if; end for;
    end if;
    printf "Computed isogeny class of %o genus 1 subgroups in %.3os\n", n, Cputime()-s; s:=Cputime();
    C := [GL2GassmannSignature(T[i]`subgroup):i in [1..#T]];
    gclasses := [Z[C[i]] : i in [1..#T]] where Z := index([1..#T],func<i|C[i]>:Project:=func<i|L[i]>);
    printf "Computed Gassmann equivalence classes in %.3os\n", Cputime()-s; s:=Cputime();
    iorbits := [[]:i in [1..#T]];  korbits := [[]:i in [1..#T]];
    for i in [1..#T] do iorbits[i] := GL2IsogenySignature(T[i]`subgroup); korbits[i] := GL2KummerSignature(T[i]`subgroup); end for;
    printf "Computed Kummer and isogeny orbits in %.3os\n", Cputime()-s; s:=Cputime();
    newforms := [[]:i in [1..#T]]; dims := [[]:i in [1..#T]];
    if #cmfdata gt 0 then
        for i in [1..#T] do
            if T[i]`genus gt 0 then
                f, d, r := GL2NewformDecomposition(cmfdata,T[i]`subgroup:g:=T[i]`genus);
                if T[i]`genus eq 1 and ranks[i] ge 0 then assert r eq ranks[i]; end if;
                newforms[i] := f; dims[i] := d; ranks[i] := r;
                if #newforms[i] eq 0 then
                    if r eq -2 then
                        printf "Missing newforms in decomposition of J_H for %o\n", L[i];
                    else
                        printf "Not enough traces to distinguish all newforms in the decomposition of J_H for %o\n", L[i];
                    end if;
                end if;
            end if;
        end for;
        printf "Computed newform decompositions in %.3os\n", Cputime()-s; s:=Cputime();
    else
        printf "Not computing newform decompositions or ranks (CMF data not available for %o)\n", p;
    end if;
    recs := Sort([GL2RecClean(rec<gl2rec|
        label:=L[i],level:=T[i]`level,index:=T[i]`index,genus:=T[i]`genus,dlabel:=T[i]`dlabel,zlabel:=T[i]`zlabel,subgroup:=T[i]`subgroup,
        children:=T[i]`children,parents:=T[i]`parents,missing:=missing[i],reductions:=reductions[i],orbits:=T[i]`orbits,
        korbits:=korbits[i],iorbits:=iorbits[i],qtwists:=qtwists[i],obstructions:=obs[i],cusps:=cusps[i],ratcusps:=ratcusps[i],
        gclass:=gclasses[i],CPlabel:=cplabels[i],Slabel:=slabels[i],SZlabel:=szlabels[i],
        RZBlabel:=p eq 2 select rzblabels[i] else "",newforms:=newforms[i],dims:=dims[i],rank:=ranks[i],
        model:=IsDefined(szdata,szlabels[i]) select szdata[szlabels[i]][2] else "",
        jmap:=IsDefined(szdata,szlabels[i]) select szdata[szlabels[i]][3] else 0,
        Emap:=IsDefined(fmdata,L[i]) select fmdata[L[i]] else []>):i in [1..#T]],func<a,b|GL2CompareLabels(a`label,b`label)>);
    if #outfile gt 0 then
        fp := Open(outfile, "w");
        for r in recs do Puts(fp,GL2RecToString(r)); end for;
        Flush(fp);
        printf "Output written to %o\n", outfile;
    end if;
    printf "Total time: %os\n", Cputime()-t;
    return index(recs,func<r|r`label>:Unique);
end function;

function checkfile(filename)
    if OpenTest(filename,"r") then return filename; end if;
    for s in ["groups/", "ell-adic-galois-images/groups/", "ell-adic-galois-images-main/groups/"] do
        u := "";
        for i:=0 to 9 do
            test := u cat s cat filename;
            if OpenTest(test,"r") then return test; end if;
            u cat:= "../";
        end for;
    end for;
    error "Unable to find file " cat filename;
end function;

function GL2Load(p)
    if Type(p) eq RngIntElt then
        if p eq 0 then filename := "gl2_Qcheck.txt"; sset := true; else assert IsPrime(p); filename := Sprintf("gl2_%oadic.txt",p); sset := false; end if;
    else
        filename:= p; sset := false;
    end if;
    filename := checkfile(filename);
    if sset then print "Performing precomputation for GL2EllAdicImages (this should take 10-20 secs)..."; end if;
    return index([GL2RecFromString(s:sset:=sset):s in Split(Read(filename))],func<r|r`label>:Unique);
end function;

function GL2LoadExamples(:filename:="examples.txt")
    function labels(s) return Split(s[2..#s-1],","); end function;
    filename := checkfile(filename);
    S := [Split(r,":"):r in Split(Read(filename))];
    E := AssociativeArray();
    for r in S do E[labels(r[1])] := EllipticCurve(atoii(r[2])); end for;
    return E;
end function;

function GL2LoadCMExamples(:filename:="cm_examples.txt")
    return GL2LoadExamples(:filename:=filename);
end function;

function ExceptionalGroup(E,p)
    exceptionaljs := [
    <2, -2^18*3*5^3*13^3*41^3*107^3/17^16, "16.64.2.1">,
    <2, -2^21*3^3*5^3*7*13^3*23^3*41^3*179^3*409^3/79^16, "16.64.2.1">,
    <2, 257^3/2^8, "16.96.3.335">,
    <2, 17^3*241^3/2^4, "16.96.3.343">,
    <2, 2^4*17^3, "16.96.3.346">,
    <2, 2^11, "16.96.3.338">,
    <2, -3^3*5^3*47^3*1217^3/(2^8*31^8), "32.96.3.230">,
    <2, 3^3*5^6*13^3*23^3*41^3/(2^16*31^4), "32.96.3.82">,
    <5, 2^4*3^2*5^7*23^3, "25.50.2.1">,
    <5, 2^12*3^3*5^7*29^3/7^5, "25.75.2.1">,
    <7, 3^3*5*7^5/2^7, "7.56.1.2">,
    <11, -11*131^3, "11.60.1.3">,
    <11, -11^2, "11.60.1.4">,
    <13, 2^4*5*13^4*17^3/3^13, "13.91.3.2">,
    <13, -2^12*5^3*11*13^4/3^13, "13.91.3.2">,
    <13, 2^18*3^3*13^4*127^3*139^3*157^3*283^3*929/(5^13*61^13), "13.91.3.2">,
    <17, -17*373^3/2^17, "17.72.1.2">,
    <17, -17^2*101^3/2, "17.72.1.4">,
    <37, -7*11^3, "37.114.4.1">,
    <37, -7*137^3*2083^3, "37.114.4.2">
    ];

    exceptionaltwists := [
    <7, 3^3*5*7^5/2^7, [1,-1,1,-2680, -50053], "7.112.1.2">,
    <7, 3^3*5*7^5/2^7, [1,-1,1,-131305,17430697], "7.112.1.2">,
    <11, -11^2, [1,1,1,-305,7888], "11.120.1.4">,
    <11, -11^2, [1,1,0,-2,-7], "11.120.1.9">,
    <11, -11*131^3, [1,1,0,-3632,82757], "11.120.1.3">,
    <11, -11*131^3, [1,1,1,-30,-76], "11.120.1.8">
    ];
    j := jInvariant(E);
    S := [r : r in exceptionaljs | r[1] eq p and r[2] eq j];
    if #S eq 0 then return ""; end if;
    assert #S eq 1;
    T := [r : r in exceptionaltwists | r[1] eq p and r[2] eq j and IsIsomorphic(E,EllipticCurve(r[3]))];
    if #T eq 0 then return S[1][3]; end if;
    assert #T eq 1;
    return T[1][4];
end function;

// jmap is an element of Q(t), j is an element of Q
function OnGenusZeroCurve(jmap,j)
    n := Numerator(jmap); d := Denominator(jmap);
    return #Roots(n-j*d) gt 0 or (Degree(n) le Degree(d) and Coefficient(n,Degree(d)) eq j*LeadingCoefficient(d));  // check j=jmap(infty)
end function;

// U=[Coeffs(A),Coeffs(B)] defines the universal elliptic curve y^2=x^3+A(t)*x+B(t), where A and B are polynomials
function OnGenusZeroCurveTwist(U,E)
    E := WeierstrassModel(E);  j := jInvariant(E);
    F<t> := FunctionField(Rationals());
    A := F!U[1]; B := F!U[2]; J := 1728*4*A^3 / (4*A^3+27*B^2); n := Numerator(J); d := Denominator(J);
    // Check point at infty
    if Degree(n) le Degree(d) and Coefficient(n,Degree(d)) eq LeadingCoefficient(d)*j then
        e := Max(Ceiling(Degree(A)/4),Ceiling(Degree(B)/6));
        a := 4*e gt Degree(A) select 0 else LeadingCoefficient(Numerator(A));
        b := 6*e gt Degree(B) select 0 else LeadingCoefficient(Numerator(B));
        if IsIsomorphic(E,EllipticCurve([a,b])) then return true; end if;
    end if;
    rr := Roots(n-j*d);
    return #[r:r in rr |IsIsomorphic(E,EllipticCurve([Evaluate(A,r[1]),Evaluate(B,r[1])]))] gt 0;
end function;

// X is an elliptic curve, map is an element of Q(y)(x) and j is an element of Q
function OnGenusOneCurve(X,map,j)
    // map should be an element of Q(y)(x)
    Rx := Universe(Coefficients(Numerator(map)));
    Rz<z> := PolynomialRing(Rx);
    f,h := HyperellipticPolynomials(X);
    g := z^2+h*z-f;
    if Degree(map) eq 0 then
        m := Evaluate(map,0);
        f := Numerator(m)-j*Denominator(m);
    else
        a := (Evaluate(Numerator(map),z)-j*Evaluate(Denominator(map),z)) mod g;
        r := Roots(a);
        if #r eq 0 then return false; end if; assert #r eq 1;
        f := Numerator(Evaluate(g,r[1][1]));
    end if;
    return #[r:r in Roots(f)|#[s:s in Roots(Rz![Evaluate(c,r[1]):c in Coefficients(g)]) | Evaluate(Evaluate(map,s[1]),r[1]) eq j] gt 0] gt 0;
end function;

function GL2EllAdicImages(E,X:Bmin:=64,Bmax:=1048576)
    assert BaseRing(E) eq Rationals();
    E := WeierstrassModel(MinimalModel(E));  D := Integers()!Discriminant(E);
    b,cmD := HasComplexMultiplication(E);
    if b then
        L := GL2CMEllAdicImages(E,GL2FrobeniusMatrices(E,256):cmD:=cmD);
        if jInvariant(E) eq 0 then
            // for j(E)=0 we can get non-maximal images of arbitrarily large level, so we compute the labels of these by hand.
            label := function(H)
                N := GL2Level(H);
                if N le 37 then return GL2LookupLabel(X,H); end if;
                assert IsPrime(N);
                g := N mod 3 eq 1 select GL2SplitCartanNormalizerGenus(N) else GL2NonsplitCartanNormalizerGenus(N);
                g := 3*g-3+(N-KroneckerSymbol(-1,N))/4+2;
                return Sprintf("%o.%o.%o.1", N, GL2Index(H), g);
            end function;
            return [label(H):H in L];
        else
            return [GL2LookupLabel(X,H):H in L];
        end if;
    end if;
    B := Bmin; A := GL2FrobeniusMatrices(E,B);
    P := PossiblyNonsurjectivePrimes(E:A:=A);
    while #P gt 0 and Max(P) gt 37 and B lt Bmax do
        A cat:= GL2FrobeniusMatrices(E,2*B:B0:=B+1); B *:= 2; 
        P := PossiblyNonsurjectivePrimes(E:A:=A);
    end while;
    if #P eq 0 then return []; end if;
    if Max(P) gt 37 then
        printf "Congratulations, you appear to have found a non-CM E/Q with non-surjective mod-ell image for a prime ell > 37!", E, P;
        assert false;
    end if;
    results := [];
    j := jInvariant(E);
    for p in P do
        L,b := GL2HeuristicEllAdicImage(E,p,A,X:Fast); assert b;
        if #L eq 1 then Append(~results,L[1]); continue; end if;
        s := ExceptionalGroup(E,p);
        if s ne "" then assert s in L; Append(~results,s); continue; end if;
        // At this point we should only be seeing groups that occur infinitely often
        while #L gt 1 and #[k:k in L|X[k]`genus gt 1 or X[k]`genus eq 1 and X[k]`rank eq 0] gt 0 and B lt Bmax do
            A := GL2FrobeniusMatrices(E,2*B:B0:=B+1); B *:= 2; L := GL2HeuristicEllAdicImage(E,p,A,X:Proof,MaxTorsion:=5);
        end while;
        if #L eq 1 then Append(~results,L[1]); continue; end if;
        if B eq Bmax then
            printf "Congratulations, you may have found a new exceptional j-invariant: %o, L = %o\n", jInvariant(E), L;
            assert #L eq 1;
            Append(~results,L[1]); continue;
        end if;
        while true do
            s := [k:k in L|X[k]`genus le 1 and GL2ContainsNegativeOne(X[k]`subgroup)];
            if #s le 1 then break; end if;
            k := s[#s];
            if (X[k]`genus eq 0 select OnGenusZeroCurve(X[k]`jmap,j) else OnGenusOneCurve(EllipticCurve(X[k]`model),X[k]`jmap,j)) then
                S := GL2Subgroups(k,X); // print "in", S;
                L := [t:t in L|t in S];
            else
                S := GL2Subgroups(k,X); // print "out", S;
                L := [t:t in L|not t in S];
            end if;
        end while;
        if #L eq 1 then Append(~results,L[1]); continue; end if;
        assert &and[X[k]`genus eq 0:k in L];
        // Note that we need to handle three 3-adic cases where there is more than one fine model (the other is a quadratic twist by -3)
        t := [k:k in L|not k in s and OnGenusZeroCurveTwist(X[k]`Emap,E)];
        if #t eq 0 then t := s; end if;
        assert #t eq 1;
        Append(~results,t[1]);
    end for;
    return [k:k in results|k ne "1.1.0.1"];
end function;


// The functions below were used to generate Tables 6-12 in the paper

function texcplabel(s)
    if #s eq 0 then return "none"; end if;
    i := [i:i in [1..#s]|s[i] ge "A" and s[i] le "Z"][1];
    l := s[1..i-1]; a := s[i];  g:=s[i+1..#s];
    return Sprintf("\\href{https://mathstats.uncg.edu/sites/pauli/congruence/csg%oM.html#level%o}{%o%o\\textsuperscript{%o}}", g,l,l,a,g);
end function;

function texdim(d,n)
    return n gt 1 select Sprintf("%o^{%o}",d,n) else Sprintf("%o",d);
end function;

function texmflabel(s,n)
    t := "\\mflabel{" cat s cat "}";
    if n gt 1 then t cat:= Sprintf("\\textsuperscript{%o}",n); end if;
    return t;
end function;

function texmflabels(newforms)
    cnts := [1:f in newforms];
    for i:=2 to #cnts do if newforms[i] eq newforms[i-1] then cnts[i] +:= cnts[i-1]; cnts[i-1] := 0; end if; end for;
    return Join([texmflabel(newforms[i],cnts[i]):i in [1..#newforms] | cnts[i] gt 0], ", ");
end function;

procedure textable(X)
    top := "\\begin{table}\n\\begin{center}\\small\n\\begin{tabular}{lllrrrrl}\nlabel & generators & CP & \\hspace{-12pt}$\\#X_H^\\infty(\\Qbar)$ & \\hspace{-4pt}$\\#X_H^\\infty(\\Q)$ & $r$ & $g$ & dimensions\\\\\\toprule";
    bottom := "\\end{tabular}\n\\end{center}\n\\end{table}";
    if #X ge 22 then print top; end if;
    for i:=1 to #X do
        r := X[i];
        s := Sprintf("\\gtarget{%o}",r`label);
        s cat:= " & $" cat Join([Sprintf("\\smallmat{%o}{%o}{%o}{%o}",g[1][1],g[1][2],g[2][1],g[2][2]):g in Generators(r`subgroup)],", ") cat "$";
        s cat:= " & " cat texcplabel(r`CPlabel);
        s cat:= Sprintf(" & %o & %o", r`cusps, r`ratcusps);
        s cat:= Sprintf(" & %o & %o", r`rank, r`genus);
        M := Multiset(r`dims);  D := Sort([d:d in Set(r`dims)]);
        s cat:= " & $" cat Join([texdim(d,Multiplicity(M,d)):d in D], ", ") cat "$";
        s cat:= "\\\\[2pt]\n& \\multicolumn{7}{l}{\\parbox[l]{12.5cm}{\\raggedright";
        s cat:= texmflabels(r`newforms);
        s cat:= "}}\\\\";
        if i lt #X then s cat:= "\\hline\\noalign{\\vskip 3pt}"; end if;
        print s;        
        if i mod 22 eq 0 then print bottom; print top; end if;
    end for;
    if #X ge 22 then print bottom; end if;
end procedure;

procedure texobstable(dir,P)
    X := AssociativeArray();
    for p in P do X[p] := GL2Load(Sprintf("%o/gl2_%oadic.txt",dir,p)); end for;
    for p in P do
        for k in GL2ArithmeticallyMaximal(X[p]) do
            if #X[p][k]`obstructions gt 0 then
                s := Sprintf("\\texttt{%o}",k);
                s cat:= Sprintf(" & $%o^%o$",p,Round(Log(p,X[p][k]`level)));
                s cat:= " & $" cat Join([Sprintf("\\smallmat{%o}{%o}{%o}{%o}",g[1][1],g[1][2],g[2][1],g[2][2]):g in Generators(X[p][k]`subgroup)],", ") cat "$";
                s cat:= " & $" cat Join([IntegerToString(q):q in X[p][k]`obstructions],",") cat "$";
                s cat:= Sprintf(" & %o", X[p][k]`rank);
                s cat:= Sprintf(" & %o\\\\", X[p][k]`genus);
                print s;
            end if;
        end for;
    end for;
end procedure;
