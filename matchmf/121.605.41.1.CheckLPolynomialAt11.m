// depends on the magma package ModFrmGL2 available at https://github.com/assaferan/ModFrmGL2 
try assert eval("Type(PSL2Subgroup) eq Intrinsic"); catch e error "You need to AttachSpec ModFrmGL2.spec before running this script -- you can download it from https://github.com/assaferan/ModFrmGL2."; end try;
H := sub<GL(2,Integers(11^2))|[[38,50,41,61],[68,68,45,68]]>; // conjugate of 121.605.41.1 containing [-1,0,0,1]
print "Constructed the group H = 121.605.41.1, decomposing the associatted space of modular symbols...";
S := CuspidalSubspace(ModularSymbols(PSL2Subgroup(H),2,Rationals(),0));
D := Decomposition(S,HeckeBound(S));
assert [ExactQuotient(Dimension(d),2):d in D] eq [1,5,35];
print "Verified the space splits into isotypic subspaces of dimensions 1,5,35.  Computing L-polynomial at 11, which should take 15-20 minutes...";
time F := [* qEigenform(d,12):d in D *];
assert &and[Coefficient(f,11) eq 0: f in F];
print "Verified that all every form in the space has T_11-eigenvalue 0, so the L-polynomial of X_H at 11 is 1.";
