/*
    This magma script verifies the claim made in Section 14 that the mod-16 and mod-27 images of 
    CM elliptic curve E over its minimal field of definition F=Q(j(E)) can be unquely determined
    by computing orbit torsion orbits and sampling Frobenius elements.  This is tested group
    theoretically by verifying that for a representative set of CM discriminants sufficient to
    realize every possible mod-16 or mod-27 image that in all cases any pair of groups H1,H2 that
    are not distinguished by their action on n-torsion points for suitable n dividing 16 or 27
    have the property that H1 contains an element that is not GL2-conjugate to any element of H2
    and H2 contains an elemennt that is not GL2-conjugate to any element of H1 (the Chebotarev
    density theorem then implies that sampling Frobenius elements will eventually rule of of them).
*/

Attach("gl2.m");

// Verify Theorem 14.3.1
print "Checking Theorem 14.3.1...";
assert #GL2CMTwists(16) eq 59;
assert #GL2CMTwists(16:Qonly) eq 28;
assert #GL2CMMaximalTwists(16) eq 14;
assert #GL2CMMaximalTwists(16:Qonly) eq 7;
assert #GL2CMTwists(27) eq 26;
assert #GL2CMTwists(27:Qonly) eq 17;
assert #GL2CMMaximalTwists(27) eq 7;
assert #GL2CMMaximalTwists(27:Qonly) eq 4;
print "done.";

function sscheck(S,O)
    A := AssociativeArray();
    for H in S do
        assert &and[IsDivisibleBy(#BaseRing(H),n):n in O];
        k := [[GL2Orbits(H,n)]:n in O];
        A[k] := IsDefined(A,k) select Append(A[k],H) else [H];
    end for;
    for k in Keys(A) do
        if #A[k] eq 1 then continue; end if;
        T := [GL2SimilaritySet(H):H in A[k]];
        for i:= 1 to #T do
            if not &and[#(T[i] diff T[j]) gt 0:j in [1..#T]|j ne i] then return false; end if;
        end for;
    end for;
    return true;
end function;

print "Checking that 4/8-orbits or 3/9-orbits plus Frobenius sampling suffice for all mod-16 and mod-27 CM images...";
assert sscheck(GL2CMTwists(-4,16),[4,8]);
assert sscheck(GL2CMTwists(-3,27),[3,9]);
for D in CMDiscriminantRepresentatives(16) do assert sscheck(GL2QuadraticTwists(GL2CartanNormalizer(D,16)),[4,8]); end for;
for D in CMDiscriminantRepresentatives(27) do assert sscheck(GL2QuadraticTwists(GL2CartanNormalizer(D,27)),[3,9]); end for;
print "done.";
