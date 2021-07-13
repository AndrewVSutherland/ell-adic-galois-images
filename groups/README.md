This subdirectory contains `Magma` code and datafiles related to Sections 3, 5, 6 and Appendix B of the paper *l-adic images of Galois for elliptic curves over Q*, by Jeremy Rouse, Andrew V. Sutherland, and David Zureick-Brown.

- `gl2.m` defines `Magma` intrinsics prefixed by `GL2` for working with open subgroups H of GL(2,Zhat) that are represented by their projections to GL(2,Z/NZ) such that H is the full inverse image of its projection.  For more details see comments at the top of the file.  Use `Attach("gl2.m")` to make these functions available in `Magma`.

- `gl2data.m` implements the functions `GL2Data(l)` and `GL2Load(l)`.  The function `GL2Data(l)` computes the lattice of open subgroups H of GL(2,Z\_l) with surjective determinant up to specified level and index bounds (by default the minimum necessary to include all qrithmetically maximal subgroups), along with associated data for each group, including local obstructions to rational points on X_H(Q) at good primes (as described in Section 5) and the decomposition of its Jacobian into abelian varieties associated to (Galois orbits of) modular forms identified by their LFMDB labels (as described in Section 6).  This code makes use of the auxiliary files `cpdata.txt`, `rzbdata.txt`, and `cmfdata.txt` described below.

- `cpdata.txt` contains a list of the subgroups of PSL(2,Z) of genus up to 24 along with the labels assigned to them by Cummins and Pauli in [CP03a,CP03b].

- `fmdata.txt` contains a list of fine models [a(t),b(t)] for genus zero groups H with infinitely many rational points that do not contain -I defining the universeal elliptic curve y^2 = x^3 + a(t)x + b(t) whose ell-adic image is generically equal to H (the fine models for ell=2 are from [RZB15]).

- `rzbdata.txt` contains a list of subgroups of GL(2,Z_2) and the labels assigned to them by Rouse and Zureick-Brown in [RZB15].

- `szdata.txt` contains a list of subgroups of GL(2,Z_l) and the labels assigned to them by Sutherland and Zywina in [SZ17].

- `cmfdata.txt` contains a list of Galois orbits of modular forms of weight 2 and prime power level l^e &le; 10000 for 2 &le; l &le; 37 along with their trace forms and LMFDB labels (see [BBB+20] for details).  Note that for l^e &gt; 1000 not every such Galois orbit is necessarily included (all with trivial character are).

- `examples.txt` contains a list of 1315 pairs (H,E) where E is a non-CM elliptic curve over Q with ell-adic image H that covers every case known to occur.  This data can be loaded using `GL2LoadExamples();` which returns an associative array whose keys are group labels and whose values are elliptic curves.

- `gl2_ladic.txt` for primes 2 &le; l &le; 37 these files contain the output cumputed by `GL2Data(l)` which can be loaded into `Magma` using the function `GL2Load(l)`.  For each prime l, the file `gl2_ladic.txt` can be recreated via `GL2Data(l:outfile:="gl2_ladic.txt")`.

- `gl2_Qcheck.txt` contains data for all subgroups of GL(2,Zhat) that are known to occur as the ell-adic image of a non-CM elliptic curve over Q.  This data can be loaded using `X:=GL2Load(0);`, which will also perform precomputation necessary to compute ell-adic images (this takes about ten seconds).  Once loaded you can use this data to compute the ell-adic images of any non-CM elliptic curve E/Q via `GL2EllAdicImages(E,X);` which will return a list of labels of images of every prime ell where the ell-adic representation for E is non-surjective (the empty list means E has surjective ell-adic image at all primes).