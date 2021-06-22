///////////////////////////////////////////////////////////////////////////////////////////////////////////////
// This file verifies the analysis of genus 2 curves with labels
// "9.36.2.1", "27.36.2.1", "27.36.2.2", "9.54.2.2"
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

    label := "9.36.2.1";
    X1 := eval Read("../models/model" cat label cat ".txt");
      _,X1 := IsHyperelliptic(X1);
      X1 := SimplifiedModel(X1);

    label := "27.36.2.1";
    X2 := eval Read("../models/model" cat label cat ".txt");
      _,X2 := IsHyperelliptic(X2);
      X2 := SimplifiedModel(X2);

    label := "27.36.2.2";
    X3 := eval Read("../models/model" cat label cat ".txt");
      _,X3 := IsHyperelliptic(X3);
      X3 := SimplifiedModel(X3);

    label := "9.54.2.2";
    X4 := eval Read("../models/model" cat label cat ".txt");
      _,X4 := IsHyperelliptic(X4);
      X4 := SimplifiedModel(X4);
      
    IsIsomorphic(X1,X2); // true


  ///////////////////////////////////////////////////////////////////////////
  //  Verify ranks and perform Chabauty
  ///////////////////////////////////////////////////////////////////////////

    RankBound(Jacobian(X1)); // 0
    RankBound(Jacobian(X3)); // 0
    RankBound(Jacobian(X4)); // 0

    #Chabauty0(Jacobian(X1)); // 2; we know from Appendix B that both cusps are rational
    #Chabauty0(Jacobian(X3)); // 2; we know from Appendix B that both cusps are rational
    #Chabauty0(Jacobian(X4)); // 0





    
