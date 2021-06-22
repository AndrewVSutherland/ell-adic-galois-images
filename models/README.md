This folder contains Magma scripts and output files for computing models
of modular curves as described in Section 7 of the paper [*l-adic images of Galois for elliptic curves over Q*](https://arxiv.org/abs/2106.11141). The main scripts are `model.m` and `whichtwist2.m`.

- `model.m`: This script takes a command line parameter `N.i.g.n` indicating the label of
the subgroup *H* (with *-I* in *H*) for which the modular curve *X\_H* should be
computed. This script constructs *X\_H* as a cover of a genus zero modular curve
*X\_H'* for a larger group *H'*.  It outputs a log file `N.i.g.m.out`, a model file, and a
map from *X\_H -> X\_H'*. 
This script reads `gl2data.m` and `gl2.m` from the groups directory.  It
also reads subdatap.txt from the models directory. The subgroup *H* must
literally be a subgroup of *H'* (and not just conjugate to a subgroup of
*H'*). Also, the script requires the Fourier expansion of a generator
for the function field *Q(X\_H')*, which should have been computed and saved when
the script computed a model for *X\_H'*.

- `whichtwist2.m`: This script takes a command line parameter m indicating the
label of a subgroup *H* (with *-I* not in *H*) for which the universal elliptic curve
over a subscheme of *X\_H/Q* should be computed. It reads `gl2data.m`, `gl2.m`
and `gl2_padic.txt` from the groups directory. It assumes that the model
for the modular curve *X\_&lt;H,-I&gt;* has already been computed and is stored in the
same directory. The resulting elliptic curve over *Q(t)* is written to `eqfm.txt`,
and a log file is written to `fmodelm.out`. 

- `subparse.m`: `Magma` scripts that will create the subgroup data `subdatap.txt`
that is required by `model.m`

- `todo.m`: A `Magma` script that automatically lists the cases where `model.m` should be run. Output files are `todo3.txt`, `todo5.txt`, and `todo7.txt` (which are text files).

- `todofine.m`: A `Magma` script that lists cases where `whichtwist2.m`
should be run. The output files (`finescript3.txt`, `finescript5.txt` and
`finescript7.txt`) are shell scripts that will call `whichtwist2.m`.

- `3adicim.m`, `5adicim.m`, `7adicim.m`, `11adicim.m`: `Magma` scripts that will
use the computed model data to determine the l-adic image of Galois for every
elliptic curve in the Cremona database.

- `3adicim.out`, `5adicim.out`, `7adicim.out`, `11adicim.out`: Output files of
the scripts mentioned above. Only non-CM curves and curves for which
`rho_{E,l^{\infty}}` is not surjective are listed.

- `sample.txt`: A text file that lists each l-adic that occurs for an
elliptic curve in the Cremona database. All l-adic images (with *3 &le; l &le; 11*) that are known to occur do occur within the range of the
Cremona database. The smallest conductor curve with a given image is
listed. CM curves are not listed.
