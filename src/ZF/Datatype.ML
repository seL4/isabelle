(*  Title: 	ZF/datatype.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Datatype Definitions for Zermelo-Fraenkel Set Theory
*)


(*Datatype definitions use least fixedpoints, standard products and sums*)
functor Datatype_Fun (Const: CONSTRUCTOR) 
         : sig include CONSTRUCTOR_RESULT INTR_ELIM INDRULE end =
struct
structure Constructor = Constructor_Fun (structure Const=Const and 
  		                      Pr=Standard_Prod and Su=Standard_Sum);
open Const Constructor;

structure Inductive = Inductive_Fun
        (val thy = con_thy;
         val thy_name = thy_name;
	 val rec_doms = (map #1 rec_specs) ~~ (map #2 rec_specs);
	 val sintrs = sintrs;
	 val monos = monos;
	 val con_defs = con_defs;
	 val type_intrs = type_intrs;
	 val type_elims = type_elims);

open Inductive
end;


(*Codatatype definitions use greatest fixedpoints, Quine products and sums*)
functor CoDatatype_Fun (Const: CONSTRUCTOR) 
         : sig include CONSTRUCTOR_RESULT INTR_ELIM COINDRULE end =
struct
structure Constructor = Constructor_Fun (structure Const=Const and 
  		                      Pr=Quine_Prod and Su=Quine_Sum);
open Const Constructor;

structure CoInductive = CoInductive_Fun
        (val thy = con_thy;
         val thy_name = thy_name;
	 val rec_doms = (map #1 rec_specs) ~~ (map #2 rec_specs);
	 val sintrs = sintrs;
	 val monos = monos;
	 val con_defs = con_defs;
	 val type_intrs = type_intrs;
	 val type_elims = type_elims);

open CoInductive
end;



(*For most datatypes involving univ*)
val datatype_intrs = 
    [SigmaI, InlI, InrI,
     Pair_in_univ, Inl_in_univ, Inr_in_univ, 
     zero_in_univ, A_into_univ, nat_into_univ, UnCI];

(*Needed for mutual recursion*)
val datatype_elims = [make_elim InlD, make_elim InrD];

(*For most codatatypes involving quniv*)
val codatatype_intrs = 
    [QSigmaI, QInlI, QInrI,
     QPair_in_quniv, QInl_in_quniv, QInr_in_quniv, 
     zero_in_quniv, A_into_quniv, nat_into_quniv, UnCI];

val codatatype_elims = [make_elim QInlD, make_elim QInrD];

