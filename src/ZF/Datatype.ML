(*  Title:      ZF/Datatype.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Datatype Definitions for Zermelo-Fraenkel Set Theory
*)


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

signature INDUCTIVE_THMS =
  sig
  val monos      : thm list             (*monotonicity of each M operator*)
  val type_intrs : thm list             (*type-checking intro rules*)
  val type_elims : thm list             (*type-checking elim rules*)
  end;

functor Data_section_Fun
 (Arg: sig include CONSTRUCTOR_ARG INDUCTIVE_I INDUCTIVE_THMS end)  
    : sig include CONSTRUCTOR_RESULT INTR_ELIM INDRULE end =
struct

structure Con = Constructor_Fun 
        (structure Const = Arg and Pr=Standard_Prod and Su=Standard_Sum);

structure Inductive = Ind_section_Fun
   (open Arg; 
    val con_defs = Con.con_defs
    val type_intrs = Arg.type_intrs @ datatype_intrs
    val type_elims = Arg.type_elims @ datatype_elims);

open Inductive Con
end;


functor CoData_section_Fun
 (Arg: sig include CONSTRUCTOR_ARG INDUCTIVE_I INDUCTIVE_THMS end)  
    : sig include CONSTRUCTOR_RESULT INTR_ELIM COINDRULE end =
struct

structure Con = Constructor_Fun 
        (structure Const = Arg and Pr=Quine_Prod and Su=Quine_Sum);

structure CoInductive = CoInd_section_Fun
   (open Arg; 
    val con_defs = Con.con_defs
    val type_intrs = Arg.type_intrs @ codatatype_intrs
    val type_elims = Arg.type_elims @ codatatype_elims);

open CoInductive Con
end;


