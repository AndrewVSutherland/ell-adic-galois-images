///////////////////////////////////////////////////////////////////////////
//  27.108.4.3
//  isomorphic to 9.108.4.1
//  3 rational cusps 
///////////////////////////////////////////////////////////////////////////

  load "functions.m";
  label := "27.108.4.3";
  X1 := eval Read("../models/model" cat label cat ".txt");

  label := "9.108.4.1";
  X2 := eval Read("../models/model" cat label cat ".txt");

  IsIsomorphic(X1,X2); // true
  
