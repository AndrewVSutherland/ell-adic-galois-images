This folder stores code and output files for computations of canonical
models.  The only canonical models that were computed were for the modular
curves `27.243.12.1` (X\_ns^+(27)), `25.250.14.1` (X\_ns^+(25)), `25.625.36.1`, `27.729.43.1`, and `13.91.3.2`.

- `canmodel.m`: This script takes a command line parameter l and computes
the canonical model of the modular curve *X\_H*. It reads the files `gl2.m` and `gl2data.m` as well as the relevant subgroup data file from
the groups directory. The output is a Magma script `modelfilel.txt`. It
outputs Fourier expansions of the cusp forms for the subgroup *H*, as
well as representations of E4 and E6 as ratios of elements in the
canonical ring, from which the map from *X\_H* to the *j*-line can be
obtained. The log file output is `modelN.i.g.n.out`.

- `canmodel2.m`: Exactly the same as `canmodel.m`, but uses many more terms in the
Fourier expansions.



