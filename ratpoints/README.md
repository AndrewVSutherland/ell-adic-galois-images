This subdirectory contains `Magma` source files which verify the claims about rational points on the modular curves in Sections 8, 9, and 10 of the paper [*l-adic images of Galois for elliptic curves over Q*](https://arxiv.org/abs/2106.11141).

- The files `N.i.g.n.m` contain an analysis of the rational points on the corresponding modular curve.
- The file `check-for-sporadic-points.m` verifies that the rational points on curves from Section 8 all correspond to cusps of CM elliptic curves.
- The file `genus-2-analysis.m` contains the analysis of the genus 2 curves from Section 8.
- The file `functions.m` contains a few functions used in the rational points analysis.
- The file `checkimages.m` verifies that the ell-adic images for the sporadic points in Table 1 are not smaller than the labels given there.
- The analysis files use the models from the folder `models` and some functions from the `groups` folder; in particular, the folder `ratpoints` needs to be in the same folder as `models` and `groups`.
