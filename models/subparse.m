// Arrange all subgroups for which models are needed as follows.
// i) Compute groups to check.
// ii) For each one, pick a parent so index is minimal.
// iii) Use fixed choice of parent.
// iv) Conjugate group itself so it is literally a subgroup of the parent.

Attach("../groups/gl2.m");
load "../groups/gl2data.m";
p := 7;
str := "../groups/gl2_" cat IntegerToString(p) cat "adic.txt";
gps := GL2Load(str);
labelstocheck := GL2ArithmeticallyMaximal(gps) cat GL2QInfinite(gps);
labelstocheck := [ labelstocheck[i] : i in [1..#labelstocheck] | labelstocheck[i] ne "1.1.0.1"];
inds := [ gps[labelstocheck[i]]`index : i in [1..#labelstocheck]];
ParallelSort(~inds,~labelstocheck);

chosenconj := <>;
for i in [1..#inds] do
  curlab := labelstocheck[i];
  if (#gps[curlab]`parents eq 1) and (gps[curlab]`parents[1] eq "1.1.0.1") then
    // The group is a maximal subgroup of GL_2(Z/p^k Z)
    Append(~chosenconj,<curlab,gps[curlab]`subgroup,"1.1.0.1">);
    printf "Parent for %o is %o.\n",curlab,"1.1.0.1";
  else
    parentinds := [ gps[gps[curlab]`parents[j]]`index : j in [1..#gps[curlab]`parents]];
    mx := Max(parentinds);
    parentchoices := [ gps[curlab]`parents[j] : j in [1..#gps[curlab]`parents] | gps[gps[curlab]`parents[j]]`index eq mx ];
    parentlab := parentchoices[1];
    ind := Index(labelstocheck,parentlab);
    covergp := chosenconj[ind][2];
    curgp := gps[curlab]`subgroup;
    if gps[parentlab]`level lt gps[curlab]`level then
      covergp := GL2Lift(covergp,gps[curlab]`level);
    end if;
    conjstochoose := [ K : K in Conjugates(GL(2,Integers(gps[curlab]`level)),curgp) | K subset covergp ];
    Append(~chosenconj,<curlab,conjstochoose[1],parentlab>);
    printf "Parent for %o is %o. Conjugates choices = %o.\n",curlab,parentlab,#conjstochoose;
  end if;
end for;

outfile := "subdata" cat IntegerToString(p) cat ".txt";
PrintFile(outfile,"subdata := ");
PrintFileMagma(outfile,chosenconj);
PrintFile(outfile,";");
PrintFile(outfile,"return subdata;");

