(*  Title: 	ZF/inductive.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive Definitions for Zermelo-Fraenkel Set Theory

Uses least fixedpoints with standard products and sums

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)


structure Lfp =
  struct
  val oper	= Const("lfp",      [iT,iT-->iT]--->iT)
  val bnd_mono	= Const("bnd_mono", [iT,iT-->iT]--->oT)
  val bnd_monoI	= bnd_monoI
  val subs	= def_lfp_subset
  val Tarski	= def_lfp_Tarski
  val induct	= def_induct
  end;

structure Standard_Prod =
  struct
  val sigma	= Const("Sigma", [iT, iT-->iT]--->iT)
  val pair	= Const("Pair", [iT,iT]--->iT)
  val split_const	= Const("split", [[iT,iT]--->iT, iT]--->iT)
  val fsplit_const	= Const("fsplit", [[iT,iT]--->oT, iT]--->oT)
  val pair_iff	= Pair_iff
  val split_eq	= split
  val fsplitI	= fsplitI
  val fsplitD	= fsplitD
  val fsplitE	= fsplitE
  end;

structure Standard_Sum =
  struct
  val sum	= Const("op +", [iT,iT]--->iT)
  val inl	= Const("Inl", iT-->iT)
  val inr	= Const("Inr", iT-->iT)
  val elim	= Const("case", [iT-->iT, iT-->iT, iT]--->iT)
  val case_inl	= case_Inl
  val case_inr	= case_Inr
  val inl_iff	= Inl_iff
  val inr_iff	= Inr_iff
  val distinct	= Inl_Inr_iff
  val distinct' = Inr_Inl_iff
  end;

functor Inductive_Fun (Ind: INDUCTIVE) : sig include INTR_ELIM INDRULE end =
struct
structure Intr_elim = 
    Intr_elim_Fun(structure Ind=Ind and Fp=Lfp and 
		  Pr=Standard_Prod and Su=Standard_Sum);

structure Indrule = Indrule_Fun (structure Ind=Ind and 
		                 Pr=Standard_Prod and Intr_elim=Intr_elim);

open Intr_elim Indrule
end;

