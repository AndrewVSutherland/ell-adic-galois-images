// Point search on 49.196.9.1

bound := 1000000;
// 26.07 seconds for 10000
// 54.27 seconds for 100000
// 624.85 seconds for 1000000

X := eval Read("../models/model49.196.9.1.txt");
DD := X;
CC := eval Read("../models/model7.28.0.1.txt");
mp := eval Read("../models/49.196.9.1map7.28.0.1.txt");

DD := eval Read("../models/model7.28.0.1.txt");
CC := eval Read("../models/model1.1.0.1.txt");
mp2 := eval Read("../models/7.28.0.1map1.1.0.1.txt");

t0 := Cputime();
pts := PointSearch(X,bound);
printf "Point searching to bound %o took %o sec.\n",bound,Cputime(t0);
printf "Found %o points: %o.\n",#pts,pts;
ims := [];

// There are three singular points on X: (0 : 1 : 0), (-1 : 0 : 1), (-1 : 7 : 1).
// The first has one place of degree 7 above it, and the second and third each
// have one place of degree 2 above them.

for i in [1..#pts] do
  if not IsSingular(pts[i]) then
    printf "Point %o is non-singular.\n",pts[i];    
    im := mp(pts[i]);
    im2 := mp2(Eltseq(im));
    printf "Image on the j-line is %o.\n",im2;
  end if;
end for;





