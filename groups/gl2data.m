/*
    This file implements the following functions:

        GL2Data(l) -- computes l-power level subgroup data that includes all arithmetically maximal subgroups.
                      Set the optional parameter "outfile" to write the results to a file
        GL2Load(l) -- loads subgroup data created by GL2Data, returning an associative array X indexed by label.
                      The input parameter can be either a prime l (indicating the file gl2_ladic.txt) or a filename.

    Precomputed files available to GL2Load include gl2_*adic.txt for * in 2,3,5,7,...,37, and also gl2_big2adic.txt.

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
    allchildren:BoolElt,    // true if all maximal subgroups are listed in children (those not listed have index greater than the index bound)
    parents:SeqEnum,        // labels of groups of which this is a maximal subgroup
    reductions:SeqEnum,     // labels of reductions modulo proper divisors of N (in order)
    orbits:SeqEnum,         // orbit signature: sorted list of triples (e,s,m) where e=exponent, s=size, m=multiplicity of H-orbits of (Z/NZ)^2
    korbits:SeqEnum,        // Kummer orbit signature: sorted list of triples (e,s,m) of H-orbits of (Z/NZ)^2/<-I> (N-division polynomial factorization)
    iorbits:SeqEnum,        // isogeny orbit signature: sorted list of triples (e,s,m) of H-orbits of the cyclic submodules of (Z/NZ)^2
    qtwists:SeqEnum,        // list of labels of subgroups K for which <K,-I> = <H,-I>, corresponding to quadratic twists
    obstructions:SeqEnum,   // sorted list of places p for which X_H(Q_p) has no local points, with p=0 for R (only set for full determinant)
    cusps:RngIntElt,        // number of cusp orbits
    ratcusps:RngIntElt,     // number of Q-rational cusp orbits
    iclass:MonStgElt,       // isogeny class of J_H, set to Cremona label for genus 1 groups with full determinant, currently left blank otherwise
    gclass:SeqEnum,         // list of labels of Gassmann equivalent subgroups K (those that induce isomorphic permutation modules)
    CPlabel:MonStgElt,      // Cummins-Pauli label of H cap SL_2(Z) (as defined in [CP03a,CP03b], available for g <= 24)
    Slabel:MonStgElt,       // Sutherland label of prime level H (as defined in [Sut16] and used in the LMFDB)
    RZBlabel:MonStgElt,     // Rouse and Zureick-Brown label of 2-adic H (as defined in [RZB15] and used in the LMFDB)
    newforms:SeqEnum,       // list of LMFDB labels of newform orbits [f] st J_H ~ prod_f A_f (each f may occur with multiplicity)
    dims:SeqEnum,           // list of dimension of the newform orbits [f] in newforms (in matching order)
    rank:RngIntElt          // analytic rank of J_H
>;

function atoi(s) return StringToInteger(s); end function;

function strip(s)
    return Join(Split(Join(Split(s," "),""),"\n"),"");
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

function GL2RecClean(r)
    if r`genus eq 0 then delete r`rank; end if;
    if r`genus gt 24 then delete r`CPlabel; end if;
    if r`RZBlabel eq "" or r`RZBlabel eq "-" then delete r`RZBlabel; end if;
    if r`genus ne 1 then delete r`iclass; end if;
    return r;
end function;

function GL2RecFill(r)
    if r`genus gt 24 then r`CPlabel:="-"; else assert r`CPlabel ne ""; end if;
    if not assigned r`RZBlabel then r`RZBlabel:="-"; end if;
    if r`RZBlabel eq "" or PrimeDivisors(r`level) ne [2] then r`RZBlabel:="-"; end if;
    if r`genus ne 1 then r`iclass:="-"; end if;
    if r`genus eq 0 then r`rank:=-1; end if;
    return r;
end function;

function GL2RecToString(r)
    r := GL2RecFill(r);
    return Join([r`label,sprint(r`level),sprint(r`index),sprint(r`genus),r`dlabel,r`zlabel,sprint(GL2Generators(r`subgroup)),
                 sprint(r`children),r`allchildren select "1" else "0", sprint(r`parents),sprint(r`reductions),sprint(r`orbits),sprint(r`korbits),sprint(r`iorbits),
                 sprint(r`qtwists),sprint(r`obstructions),sprint(r`cusps),sprint(r`ratcusps),r`iclass,sprint(r`gclass),r`CPlabel,r`Slabel,r`RZBlabel,
                 sprint(r`newforms),sprint(r`dims),sprint(r`rank)],":");
end function;

function GL2RecFromString(s)
    function labels(s) return Split(s[2..#s-1],","); end function;
    s := Split(s,":");
    N := atoi(s[2]); H := GL2FromGenerators(N,eval(s[7]));
    r := rec<gl2rec|label:=s[1],level:=N,index:=atoi(s[3]),genus:=atoi(s[4]),dlabel:=s[5],zlabel:=s[6],subgroup:=H,children:=labels(s[8]),allchildren:=s[9] eq "1",
                    parents:=labels(s[10]),reductions:=labels(s[11]),orbits:=eval(s[12]),korbits:=eval(s[13]),iorbits:=eval(s[14]),qtwists:=labels(s[15]),
                    obstructions:=eval(s[16]),cusps:=atoi(s[17]),ratcusps:=atoi(s[18]),iclass:=s[19],gclass:=labels(s[20]),CPlabel:=s[21],Slabel:=s[22],
                    RZBlabel:=s[23],newforms:=labels(s[24]),dims:=eval(s[25]),rank:=atoi(s[26])>;
    return GL2RecClean(r);
end function;

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

// file format is SZlabel:level:gens
function SZLoad(p,maxN,maxI:szdatafile:="szdata.txt")
    S := [Split(s,":") : s in Split(Read(szdatafile))];
    S := [<r[1],GL2FromGenerators(atoi(r[2]),eval(r[3]))> : r in S | atoi(r[2]) le maxN];
    return [r : r in S|GL2Index(r[2]) le maxI];
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
        maxp := NthPrime(maxi);
        Q := [p : p in PrimesInInterval(B0,maxp)|N mod p ne 0];  B0 := maxp+1;
        P cat:= Q; t cat:= GL2Traces(H,Q);
        b := Vector(t);
        A := Matrix([[r`dim] cat [r`traces[I[p]]:p in P]:r in Z]);
        try x,K := Solution(A,b); catch e; return [],[], -1; end try;
        // printf "Using %o columns, dimension %o\n", Degree(b), Dimension(K);
        if Dimension(K) eq 0 then
            forms := Sort([s:s in {* Z[i]`label^^x[i]:i in [1..Degree(x)] *}], CMFLabelCompare);
            dims := [X[f]`dim:f in forms];
            assert &+dims eq g;
            rank := &+[X[f]`rank:f in forms]; // note that cmfdata.txt stores the rank of the Galois orbit
            return forms, dims, rank;
        end if;
        maxi := Ceiling(1.5*maxi);
    end while;
end function;

// Output file format is label:gens:children:parents:orbits:iorbits:ccsig:sl2twists:qtwists:obstructions:cusps:ratcusps:iclass:rank:cplabel:forms:dims
// Currently we only fill in iclass:forms:dims:rank for genus 1
function GL2Data(p:cmfdatafile:="cmfdata.txt",cpdatafile:="cpdata.txt",rzbdatafile:="rzbdata.txt",szdatafile:="szdata.txt",outfile:="",Cheat:=false)
    assert IsPrime(p);
    t := Cputime(); s:=t;
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
    try cpdata := CPLoad(p,maxN:cpdatafile:=cpdatafile); catch e; cpdata:=[]; printf "Unable to find/read file '%o', CP labels will not be set (use cpdatafile to specify an alternate location)\n", cpdatafile; end try;
    try rzbdata := RZBLoad(p,maxN,maxI:rzbdatafile:=rzbdatafile); catch e; printf "Unable to find/read file '%o', RZB labels will not be set (use rzbdatafile to specify an alternate location)\n", rzbdatafile; end try;
    try szdata := SZLoad(p,maxN,maxI:szdatafile:=szdatafile); catch e; printf "Unable to find/read file '%o', SZ labels will not be set (use szdatafile to specify an alternate location)\n", szdatafile; end try;
    try cmfdata := CMFLoad(p,maxN:cmfdatafile:=cmfdatafile); catch e; cmfdata:=[]; printf "Unable to find/read file '%o', newform decompositions will not be computed (use cmfdatafile to specify an alternate location)\n", cmfdatafile; end try;
    X := GL2Lattice(maxN,maxI:Verbose);
    L := Sort([k:k in Keys(X)],func<a,b|GL2CompareLabels(a,b)>);
    T := [X[k]:k in L];
    lcmp := func<a,b|GL2CompareLabels(a,b)>;
    printf "Computed subgroup lattice and labels for %o groups in %.3os\n", #L, Cputime()-s; s:=Cputime();
    allchildren := [k eq "1.1.0.1" select true else #[H:H in MaximalSubgroups(X[k]`subgroup)|H`order * maxI lt GL2Size(X[k]`level)] eq 0 : k in L];
    printf "Computed maximal subgroups of %o groups in %.3os\n", #L, Cputime()-s; s:=Cputime();
    reductions := [Sort([GL2LookupLabel(X,ChangeRing(T[i]`subgroup,Integers(T[i]`level div p^e))) :e in [1..Valuation(T[i]`level,p)-1]],lcmp):i in [1..#T]];
    printf "Computed reduction labels for %o groups in %.3os\n", #T, Cputime()-s; s:=Cputime();
    for i:=1 to #T do if T[i]`level gt 1 then T[i]`subgroup := GL2Standardize(T[i]`subgroup); end if; end for;
    printf "Standardized generators for %o groups in %.3os\n", #T, Cputime()-s; s:=Cputime();
    qtwists := [GL2LookupLabel(X,GL2GenericQuadraticTwist(T[i]`subgroup):g:=T[i]`genus) : i in [1..#T]];
    Z := index([1..#L],func<i|qtwists[i]>);
    qtwists := [Sort([L[j] : j in Z[qtwists[i]]],lcmp) : i in [1..#qtwists]];
    printf "Computed %o quadratic twists of %o subgroups in %.3os\n", &+[#r:r in qtwists], #T, Cputime()-s; s:=Cputime();
    cplabels := ["?":i in [1..#T]];
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
        assert not "?" in cplabels;
        printf "Computed %o CPlabels in %.3os\n", #[s:s in cplabels|s ne ""], Cputime()-s; s:=Cputime();
    end if;
    if #rzbdata gt 0 then
        Z := index(rzbdata,func<r|GL2LookupLabel(X,GL2Transpose(r[2]))>:Project:=func<r|r[1]>,Unique);
        rzblabels := [IsDefined(Z,k) select Z[k] else "" : k in L];
        printf "Computed %o RZBlabels in %.3os\n", #[x:x in rzblabels|x ne ""], Cputime()-s; s:=Cputime();
    end if;
    slabels := [GL2SLabel(X[k]`subgroup,p) : k in L];
    printf "Computed %o Slabels in %.3os\n", #[x:x in slabels|x ne ""], Cputime()-s; s:=Cputime();
    if #szdata gt 0 then
        Z := index(szdata,func<r|GL2LookupLabel(X,r[2])>:Project:=func<r|r[1]>,Unique);
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
    for i in [1..#T] do if ratcusps[i] eq 0 then obs[i] := GL2QObstructions(T[i]`subgroup:B:=100); end if; end for;
    printf "Identified local obstructions in %.3os\n", Cputime()-s; s:=Cputime();
    iclasses := ["":i in [1..#T]];  ranks := [-1:i in [1..#T]]; n:=0;
    for i in [1..#T] do if T[i]`genus eq 1 then e,r := GL2IsogenyClass(T[i]`subgroup); iclasses[i]:= e; ranks[i]:=r; n+:=1; end if; end for;
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
                if T[i]`genus eq 1 then assert r eq ranks[i]; end if;
                newforms[i] := f; dims[i] := d; ranks[i] := r;
                if #newforms eq 0 then printf "Missing newforms in decomposition of J_H for %o\n", L[i]; end if;
            end if;
        end for;
        printf "Computed newform decompositions in %.3os\n", Cputime()-s; s:=Cputime();
    end if;
    recs := Sort([GL2RecClean(rec<gl2rec|label:=L[i],level:=T[i]`level,index:=T[i]`index,genus:=T[i]`genus,dlabel:=T[i]`dlabel,zlabel:=T[i]`zlabel,subgroup:=T[i]`subgroup,
                             children:=T[i]`children,parents:=T[i]`parents,allchildren:=allchildren[i],reductions:=reductions[i],orbits:=T[i]`orbits,
                             korbits:=korbits[i],iorbits:=iorbits[i],qtwists:=qtwists[i],obstructions:=obs[i],cusps:=cusps[i],ratcusps:=ratcusps[i],
                             iclass:=iclasses[i],gclass:=gclasses[i],CPlabel:=cplabels[i],Slabel:=slabels[i],RZBlabel:=p eq 2 select rzblabels[i] else "",
                             newforms:=newforms[i],dims:=dims[i],rank:=ranks[i]>):i in [1..#T]],
                 func<a,b|GL2CompareLabels(a`label,b`label)>);
    if #outfile gt 0 then
        fp := Open(outfile, "w");
        for r in recs do Puts(fp,GL2RecToString(r)); end for;
        Flush(fp);
        printf "Output written to %o\n", outfile;
    end if;
    printf "Total time: %os\n", Cputime()-t;
    return index(recs,func<r|r`label>:Unique);
end function;

function GL2Load(p)
    if Type(p) eq RngIntElt then assert IsPrime(p); filename := Sprintf("gl2_%oadic.txt",p); else filename:= p; end if;
    return index([GL2RecFromString(s):s in Split(Read(filename))],func<r|r`label>:Unique);
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
    S := GL2ArithmeticallyMaximal(X);
    top := "\\begin{table}\n\\begin{center}\\small\n\\begin{tabular}{lllrrrrl}\nlabel & generators & CP & \\hspace{-12pt}$\\#X_H^\\infty(\\Qbar)$ & \\hspace{-4pt}$\\#X_H^\\infty(\\Q)$ & $r$ & $g$ & dimensions\\\\\\toprule";
    bottom := "\\end{tabular}\n\\end{center}\n\\end{table}";
    if #S ge 22 then print top; end if;
    for i:=1 to #S do
        r := X[S[i]];
        s := Sprintf("\\texttt{%o}",r`label);
        s cat:= " & $" cat Join([Sprintf("\\smallmat{%o}{%o}{%o}{%o}",g[1][1],g[1][2],g[2][1],g[2][2]):g in Generators(r`subgroup)],", ") cat "$";
        s cat:= " & " cat texcplabel(r`cplabel);
        s cat:= Sprintf(" & %o & %o", r`cusps, r`ratcusps);
        s cat:= Sprintf(" & %o & %o", r`rank, r`genus);
        M := Multiset(r`dims);  D := Sort([d:d in Set(r`dims)]);
        s cat:= " & $" cat Join([texdim(d,Multiplicity(M,d)):d in D], ", ") cat "$";
        s cat:= "\\\\[0.5pt]\n& \\multicolumn{7}{l}{\\parbox[l]{13.0cm}{\\raggedright";
        s cat:= texmflabels(r`newforms);
        s cat:= "}}\\\\[-1pt]";
        if i lt #S then s cat:= "\\hline\\noalign{\\vskip 2pt}"; end if;
        print s;        
        if i mod 22 eq 0 then print bottom; print top; end if;
    end for;
    if #S ge 22 then print bottom; end if;
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
