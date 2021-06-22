//////////////////////////////////////////////////////////////////////////////////////////
// A few functions used in the rational points analysis
//////////////////////////////////////////////////////////////////////////////////////////

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // This gives an upper bound on the global class group, given ClassGroup data at several primes
  /////////////////////////////////////////////////////////////////////////////////////////////////
  
  torsBound := function(data)
    n := Minimum([#d : d in data]);
    return [ GCD( [ d[#d-i]: d in data])  :  i in [1..n-1] ];
  end function;  

  
  /////////////////////////////////////////////////////////////////////////
  // divisorSearch
  //
  // Input: a smooth projective curve C
  //        a positive integer deg
  //        a positive integer bound
  //        an optional boolean verbose
  // 
  // Output: the defining ideals of any points of degree deg on C
  //        which arise as the intersection of L and C, 
  //        where L is a hyperplane with coefficients of size at most bound
  //
  ///////////////////////////////////////////////////////////////////////// 

  function divisorSearch(C,deg,bound: verbose := false)
    P<[X]> := AmbientSpace(C);
    B := -1;
    tups := {};
    d := Dimension(P);
    ideals := {@@};
      while B lt bound do
	  tupsOld := tups;
          B := B + 1;  
  	if verbose then B; end if;
          tups := [P![tup[i] : i in [1..#tup]] : 
                   tup in CartesianPower([-B..B],d+1) |
                   not tup eq <0 : i in [1..d+1]>
                   and not P![tup[i] : i in [1..#tup]] in tupsOld];
          tups := [P![tup[i] : i in [1..#tup]] : 
                   tup in CartesianPower([-B..B],d+1) |
                   not tup eq <0 : i in [1..d+1]>
                   and not P![tup[i] : i in [1..#tup]] in tupsOld];
          for c in tups  do  
            L := Scheme(P,&+[c[i]*X[i] : i in [1..Dimension(AmbientSpace(C)) + 1]]);
              irr := IrreducibleComponents(L meet C);
              degs := [Degree(ReducedSubscheme(i)) : i in irr];
              if  deg in degs then
    	      if verbose then c; end if;
    	    for cpt in irr do  
    	      if  Degree(ReducedSubscheme(cpt)) eq deg 
    	          and not Basis(Ideal(ReducedSubscheme(cpt))) in ideals then	      
    	            ideals := ideals join {@Basis(Ideal(ReducedSubscheme(cpt)))@};	   
  		    if verbose then ideals; end if;
    	      end if;
    	    end for;
              end if;  
          end for;
       end while;
     return ideals;
  end function;  

  
  //////////////////////////////////////////////////////////////////////////////////////////
  // The Jacobian of a general curve isn't implemented in Magma.
  //////////////////////////////////////////////////////////////////////////////////////////
  // This function computes the order of a divisor D.
  // Optional paramater: N is a known multiple of the order of D (and we assume that N*D = 0)
  // Optional paramater: B, give up after B
  //////////////////////////////////////////////////////////////////////////////////////////
  // Note: usually it is much faster to compute this mod a prime, but often it is convenient
  // to compute this globally.
  //////////////////////////////////////////////////////////////////////////////////////////  

  order := function(D : N := 0, B := N eq 0 select 500 else N)
    currentBound := 0;
    found := false;
    if N eq 0 then
      while not found and currentBound le B do
        currentBound := currentBound + 1;
        found := IsPrincipal(currentBound * D);
      end while;
        return found select currentBound else 0, found;
    else
      for n in [d : d in Divisors(N) | not d eq N] do
        found := IsPrincipal(n*(D));
        if found then
          currentBound := n; break;
        end if;
      end for;
      return found select currentBound else N, true;
     end if;
  end function;

