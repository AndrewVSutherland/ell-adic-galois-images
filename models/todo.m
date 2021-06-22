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
sortorder := [];
for i in [1..#labelstocheck] do
  lsplit := Split(labelstocheck[i],".");
  Append(~sortorder,[ StringToInteger(lsplit[i]) : i in [1..#lsplit]]);
end for;	       
ParallelSort(~sortorder,~labelstocheck);

printf "Groups to do:\n";
scriptfile := "script" cat IntegerToString(p) cat ".txt";
for i in [1..#labelstocheck] do
  if labelstocheck[i] eq GL2LookupLabel(gps,GL2GenericQuadraticTwist(gps[labelstocheck[i]]`subgroup)) then
    printf "%o\n",labelstocheck[i];
    // Don't use model.m for curve of genus >= 10. 
    if StringToInteger(Split(labelstocheck[i],".")[3]) le 9 then
      PrintFile(scriptfile,Sprintf("magma l:=%o model.m",labelstocheck[i]));
    end if;
  end if;
end for;



