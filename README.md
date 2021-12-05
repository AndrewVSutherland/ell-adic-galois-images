This repository contains code and data associated to the paper [*l-adic images of Galois for elliptic curves over Q*](https://arxiv.org/abs/2106.11141), by Jeremy Rouse, Andrew V. Sutherland, and David Zureick-Brown, arXiv:2106.11141 (2021).

The directories are organized as follows:

- `canmodels` contains `Magma` code and data for computing canonical models of high genus modular curves as described in Section 7 of the paper.

- `groups` contains `Magma` code and data for computing the lattice of open subgroups of GL(2,Z_l) up to a given index and level bound, including all arithmetically maximal subgroups (Section 3 of the paper), `Magma` code for counting points on X\_H/F\_q and computing the isogeny decomposition of J\_H/Q (Sections 5 and 6 of the paper), and for computing l-adic images of Galois for a given elliptic curve E/Q (Sections 11 and 12 of the paper).

- `matchmf` contains `Magma` scripts that verify that the Jacobian of the modular curve associated to the group 121.605.41.1 is isogenous to the product of the modular abelian varieties associated to the Galois orbits of the newforms `121.2.a.b`, `14641.2.a.a`, `14641.2.a.c`, as described in Section 6 of paper.

- `models` contains `Magma` code and data for computing models of modular curves as covers of other modular curves, as described in Section 7 of the paper.

- `pointsearch' contains `Magma` code and data for point searching on modular curves whose rational points we were not able to provably determine, as discussed in Section 9 of the paper.

- `ratpoints` contains `Magma` scripts that verify the claims about rational points on modular curves made in Sections 8, 9, and 10 of the paper.

See the individual README files in each subdirectory for more detailed information.

You are welcome to use the code in this repository for your own research, but we ask that you please cite our paper if and when you publish your results.
