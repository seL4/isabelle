(*  Title: 	ZF/Inductive.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Inductive Definitions for Zermelo-Fraenkel Set Theory

Inductive definitions use least fixedpoints with standard products and sums
Coinductive definitions use greatest fixedpoints with Quine products and sums

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

local open Ind_Syntax
in
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
end;

functor Ind_section_Fun (Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end) 
  : sig include INTR_ELIM INDRULE end =
struct
structure Intr_elim = 
    Intr_elim_Fun(structure Inductive=Inductive and Fp=Lfp and 
		  Pr=Standard_Prod and Su=Standard_Sum);

structure Indrule = 
    Indrule_Fun (structure Inductive=Inductive and 
		 Pr=Standard_Prod and Su=Standard_Sum and Intr_elim=Intr_elim);

open Intr_elim Indrule
end;


structure Ind = Add_inductive_def_Fun
    (structure Fp=Lfp and Pr=Standard_Prod and Su=Standard_Sum);


local open Ind_Syntax
in
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
end;


signature COINDRULE =
  sig
  val coinduct : thm
  end;


functor CoInd_section_Fun
 (Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end) 
    : sig include INTR_ELIM COINDRULE end =
struct
structure Intr_elim = 
    Intr_elim_Fun(structure Inductive=Inductive and Fp=Gfp and 
		  Pr=Quine_Prod and Su=Quine_Sum);

open Intr_elim 
val coinduct = raw_induct
end;


structure CoInd = 
    Add_inductive_def_Fun(structure Fp=Gfp and Pr=Quine_Prod and Su=Quine_Sum);


