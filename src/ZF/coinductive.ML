(*  Title: 	ZF/coinductive.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Coinductive Definitions for Zermelo-Fraenkel Set Theory

Uses greatest fixedpoints with Quine-inspired products and sums

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

structure Gfp =
  struct
  val oper	= Const("gfp",      [iT,iT-->iT]--->iT)
  val bnd_mono	= Const("bnd_mono", [iT,iT-->iT]--->oT)
  val bnd_monoI	= bnd_monoI
  val subs	= def_gfp_subset
  val Tarski	= def_gfp_Tarski
  val induct	= def_Collect_coinduct
  end;

structure Quine_Prod =
  struct
  val sigma	= Const("QSigma", [iT, iT-->iT]--->iT)
  val pair	= Const("QPair", [iT,iT]--->iT)
  val split_const	= Const("qsplit", [[iT,iT]--->iT, iT]--->iT)
  val fsplit_const	= Const("qfsplit", [[iT,iT]--->oT, iT]--->oT)
  val pair_iff	= QPair_iff
  val split_eq	= qsplit
  val fsplitI	= qfsplitI
  val fsplitD	= qfsplitD
  val fsplitE	= qfsplitE
  end;

structure Quine_Sum =
  struct
  val sum	= Const("op <+>", [iT,iT]--->iT)
  val inl	= Const("QInl", iT-->iT)
  val inr	= Const("QInr", iT-->iT)
  val elim	= Const("qcase", [iT-->iT, iT-->iT, iT]--->iT)
  val case_inl	= qcase_QInl
  val case_inr	= qcase_QInr
  val inl_iff	= QInl_iff
  val inr_iff	= QInr_iff
  val distinct	= QInl_QInr_iff
  val distinct' = QInr_QInl_iff
  end;

signature COINDRULE =
  sig
  val coinduct : thm
  end;


functor CoInductive_Fun (Ind: INDUCTIVE) 
          : sig include INTR_ELIM COINDRULE end =
struct
structure Intr_elim = 
    Intr_elim_Fun(structure Ind=Ind and Fp=Gfp and 
		  Pr=Quine_Prod and Su=Quine_Sum);

open Intr_elim 
val coinduct = raw_induct
end;

