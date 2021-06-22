///////////////////////////////////////////////////////////////////////////////////////////////////////////////
// This file verifies the claims made about the sporadic points on the curves with labels
//
// "9.12.1.1", "9.54.1.1", "9.81.1.1", "27.36.1.2", "9.36.2.1", "27.36.2.1", "27.36.2.2", "9.54.2.2",
// "9.108.3.1", "9.108.4.1", "27.36.3.1", "27.108.3.1", "27.108.4.1", "27.108.4.3", "27.108.6.1"
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

 Attach("../groups/gl2.m");
 load "../groups/gl2data.m";

 labels := ["9.12.1.1", "9.54.1.1", "9.81.1.1", "27.36.1.2", "9.36.2.1", "27.36.2.1", "27.36.2.2", "9.54.2.2", "9.108.3.1", "9.108.4.1", "27.36.3.1", "27.108.3.1", "27.108.4.1", "27.108.4.3", "27.108.6.1"];

for m in labels do
  lev := StringToInteger(Split(m,".")[1]);
  chk, p := IsPrimePower(lev);
  subs := GL2Load("../groups/gl2_" cat IntegerToString(p) cat "adic.txt");
  subfilename := "../models/subdata" cat IntegerToString(p) cat ".txt";
  subdata := eval Read(subfilename);
  coverlist := [];
  // We exclude modular curves for which (i) the canonical model was computed
  // (ii) the model was unnecessary because of prior work, or (iii)
  // we didn't try to compute a model (namely X_ns^+(49)).
  excludedlist := ["27.243.12.1", "27.729.43.1", "25.150.8.1", "125.150.8.1", "25.250.14.1", "25.375.22.1", "25.625.36.1", "49.168.12.1", "49.168.12.2", "49.1029.69.1", "49.1372.94.1"];
  for i in [1..#subdata] do
    if subs[subdata[i][1]]`qtwists[1] eq subdata[i][1] then
      if not (subdata[i][1] in excludedlist) then
        Append(~coverlist,<subdata[i][1],subdata[i][3]>);
      end if;
    end if;
  end for;
  
  // Make a master list of modular curves
  
  modcurves := <>;
  for lab in ["1.1.0.1"] cat [ coverlist[i][1] : i in [1..#coverlist]] do
    filename := Sprintf("../models/model%o.txt",lab);
    Append(~modcurves,<lab,Curve(eval Read(filename))>);
  end for;
  
  if (not m in Keys(subs)) then
    printf "Error. Label not found.\n";
    bad := 0;
    bad2 := 1/bad;
  end if;
  
  curlab := m;
  firsttime := true;
  curmap := 0;
  while (curlab ne "1.1.0.1") do
      ind := Index([ coverlist[i][1] : i in [1..#coverlist]],curlab);
      coverlab := coverlist[ind][2];
      modcurveind1 := Index([ modcurves[i][1] : i in [1..#modcurves]],curlab);
      modcurveind2 := Index([ modcurves[i][1] : i in [1..#modcurves]],coverlab);  
  
      mapfilename := "../models/" cat curlab cat "map" cat coverlab cat ".txt";
      // Specify DD is the domain of the map, and CC is the codomain
      DD := modcurves[modcurveind1][2];
      CC := modcurves[modcurveind2][2];
      mp := eval Read(mapfilename);

      if (firsttime) then
        firsttime := false;
	ps := PointSearch(DD,1000);
	ps := [pl :pl in Places(pt),  pt in ps | Degree(pl) eq 1];
	ps := [ Support(Pushforward(mp, ps[i]))[1] : i in [1..#ps]];	
      else
	ps := [ Support(Pushforward(mp, ps[i]))[1] : i in [1..#ps]];
      end if;
      curlab := coverlab;
  end while;
  
  printf "We find rational points on %o with j-invariants %o.\n",m, ps;
end for;         
