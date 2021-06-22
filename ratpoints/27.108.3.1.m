//////////////////////////////////////////////////////////////////////////////
//  27.108.3.1
//    Isomorphic to 9.108.3.1; we verify this
//    X has 0 rational cusps and 2 CM points with j = 0
//////////////////////////////////////////////////////////////////////////////

  load "functions.m";
  label := "27.108.3.1";
  C1 := eval Read("../models/model" cat label cat ".txt");

  label := "9.108.3.1";
  C2 := eval Read("../models/model" cat label cat ".txt");

  IsIsomorphic(C1,C2);
  
