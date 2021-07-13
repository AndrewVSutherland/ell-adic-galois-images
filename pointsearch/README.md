This folder contains scripts and output files for point searching on modular
curves *X\_H* whose rational points we were not able to provably determine.

The Magma scripts which perform the point searching are the following.


- `17.136.6.1.m`: This script uses the Mordell-Weil sieve to point search on *X\_ns^+(17)* using a morphism *X\_ns^+(17) -> E*, where *E* is an elliptic curve. 

- `25.250.14.1.m`: This script point searches on *X\_ns^+(25)* by creating low height points on *X\_ns^+(5)* and seeing if the lift to *X\_ns^+(25)* by writing down elliptic curves with candidate *j*-invariants and seeing if the pair <p+1-#E(F_p),p> is consistent with having image contained in the normalizer of the non-split Cartan mod 25. 

- `27.243.12.1.m`: This script point searches on *X\_ns^+(27)* by creating low height points on *X\_ns^+(9)* and seeing if they lift to the genus 3 curve *X\_H* described in Subsection 12.1 of the paper.

- `49.147.9.1.m`: This script point searches on 49.147.9.1 using the simple (singular) plane model that was computed. The script automatically computes images on the j-line of points that are found. It reads model data from the models folder.

- `49.196.9.1.m`: This script point searches on 49.196.9.1 using the simple (singular) plane model that was computed. The script automatically computes images on the j-line of points that are found. It reads model data from the models folder.

- `49.1029.69.1.m`: This script point searches on *X\_ns^+(49)* using a similar technique to *X\_ns^+(25)*. 

- `121.6655.511.1.m`: This script uses the Mordell-Weil sieve and the map *X\_ns^+(121) -> X\_ns^+(11)* to point search on *X\_ns^+(121)*. Candidate j-invariants are tested and ruled out using similar techniques as for *X\_ns^+(25)* and *X\_ns^+(49)*.

- `17.136.6.1.out`, `25.250.14.1.out`, `27.243.12.1.out`, `49.147.9.1.out`, `49.196.9.1.out`, `49.1029.69.1.out`, `121.6655.511.1.out`: These files are output files of the scripts mentioned above.

- `nonsplit.m`: This script uses an equationless point searching technique to
search for points on *X\_ns^+(l^r)* with l and r specified in the script. It is
not particularly fast, but can be used when an equation for *X\_ns^+(l^r)* is not available.