// This script outputs a list of genus zero fine models that need to
// be computed.
// In some cases, (like p = 7 and p = 11) there might be some genus > 0
// fine models to work with.

p := 7;

Attach("../groups/gl2.m");
load "../groups/gl2data.m";
subdat := GL2Load("../groups/gl2_" cat IntegerToString(p) cat "adic.txt");

labelstocheck := [];
for s in Keys(subdat) do
  if subdat[s]`genus eq 0 then
    if subdat[s]`qtwists[1] ne s then
      Append(~labelstocheck,s);
    end if;
  end if;
end for;
sortorder := [];
for i in [1..#labelstocheck] do
  lsplit := Split(labelstocheck[i],".");
  Append(~sortorder,[ StringToInteger(lsplit[i]) : i in [1..#lsplit]]);
end for;               
ParallelSort(~sortorder,~labelstocheck);

printf "Groups to do:\n";
scriptfile := "finescript" cat IntegerToString(p) cat ".txt";
for i in [1..#labelstocheck] do
  printf "%o\n",labelstocheck[i];
  PrintFile(scriptfile,Sprintf("magma m:=%o whichtwist2.txt",labelstocheck[i]));
end for;
