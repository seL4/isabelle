(*  Title:      ZF/Datatype.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Datatype Definitions for Zermelo-Fraenkel Set Theory
*)


(*Typechecking rules for most datatypes involving univ*)
structure Data_Arg =
  struct
  val intrs = 
      [SigmaI, InlI, InrI,
       Pair_in_univ, Inl_in_univ, Inr_in_univ, 
       zero_in_univ, A_into_univ, nat_into_univ, UnCI];

  (*Needed for mutual recursion*)
  val elims = [make_elim InlD, make_elim InrD];
  end;


structure Data_Package = 
    Add_datatype_def_Fun
      (structure Fp=Lfp and Pr=Standard_Prod and CP=Standard_CP
       and Su=Standard_Sum
       and Ind_Package = Ind_Package
       and Datatype_Arg = Data_Arg);


(*Typechecking rules for most codatatypes involving quniv*)
structure CoData_Arg =
  struct
  val intrs = 
      [QSigmaI, QInlI, QInrI,
       QPair_in_quniv, QInl_in_quniv, QInr_in_quniv, 
       zero_in_quniv, A_into_quniv, nat_into_quniv, UnCI];

  val elims = [make_elim QInlD, make_elim QInrD];
  end;

structure CoData_Package = 
    Add_datatype_def_Fun(structure Fp=Gfp and Pr=Quine_Prod and CP=Quine_CP
                          and Su=Quine_Sum
			  and Ind_Package = CoInd_Package
			  and Datatype_Arg = CoData_Arg);

