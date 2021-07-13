// Point search on 49.147.9.1

bound := 1000000;
// 10.9 sec for 10000
// 78.92 sec for 100000
// 740.64 sec for 1000000

X := eval Read("../models/model49.147.9.1.txt");
DD := X;
CC := eval Read("../models/model7.21.0.1.txt");
mp := eval Read("../models/49.147.9.1map7.21.0.1.txt");

DD := eval Read("../models/model7.21.0.1.txt");
CC := eval Read("../models/model1.1.0.1.txt");
mp2 := eval Read("../models/7.21.0.1map1.1.0.1.txt");

t0 := Cputime();
pts := PointSearch(X,bound);
printf "Point searching to bound %o took %o sec.\n",bound,Cputime(t0);
printf "Found %o points: %o.\n",#pts,pts;
ims := [];

// There are two singular points on X: (0 : 1 : 0) and (1/2 : -7/2 : 1).
// The first has one place of degree 7 above it, the other has one place of
// degree 2 above it.

for i in [1..#pts] do
  if not IsSingular(pts[i]) then
    printf "Point %o is non-singular.\n",pts[i];    
    im := mp(pts[i]);
    im2 := mp2(Eltseq(im));
    printf "Image on the j-line is %o.\n",im2;
  end if;
end for;





