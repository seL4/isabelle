(*  Title:      ZF/Inductive.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Inductive Definitions for Zermelo-Fraenkel Set Theory

Inductive definitions use least fixedpoints with standard products and sums
Coinductive definitions use greatest fixedpoints with Quine products and sums

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

val iT = Ind_Syntax.iT
and oT = FOLogic.oT;

structure Lfp =
  struct
  val oper      = Const("Fixedpt.lfp", [iT,iT-->iT]--->iT)
  val bnd_mono  = Const("Fixedpt.bnd_mono", [iT,iT-->iT]--->oT)
  val bnd_monoI = bnd_monoI
  val subs      = def_lfp_subset
  val Tarski    = def_lfp_unfold
  val induct    = def_induct
  end;

structure Standard_Prod =
  struct
  val sigma     = Const("Sigma", [iT, iT-->iT]--->iT)
  val pair      = Const("Pair", [iT,iT]--->iT)
  val split_name = "split"
  val pair_iff  = Pair_iff
  val split_eq  = split
  val fsplitI   = splitI
  val fsplitD   = splitD
  val fsplitE   = splitE
  end;

structure Standard_CP = CartProd_Fun (Standard_Prod);

structure Standard_Sum =
  struct
  val sum       = Const("op +", [iT,iT]--->iT)
  val inl       = Const("Inl", iT-->iT)
  val inr       = Const("Inr", iT-->iT)
  val elim      = Const("case", [iT-->iT, iT-->iT, iT]--->iT)
  val case_inl  = case_Inl
  val case_inr  = case_Inr
  val inl_iff   = Inl_iff
  val inr_iff   = Inr_iff
  val distinct  = Inl_Inr_iff
  val distinct' = Inr_Inl_iff
  val free_SEs  = Ind_Syntax.mk_free_SEs
            [distinct, distinct', inl_iff, inr_iff, Standard_Prod.pair_iff]
  end;


structure Ind_Package =
    Add_inductive_def_Fun
      (structure Fp=Lfp and Pr=Standard_Prod and CP=Standard_CP
       and Su=Standard_Sum val coind = false);


structure Gfp =
  struct
  val oper      = Const("Fixedpt.gfp", [iT,iT-->iT]--->iT)
  val bnd_mono  = Const("Fixedpt.bnd_mono", [iT,iT-->iT]--->oT)
  val bnd_monoI = bnd_monoI
  val subs      = def_gfp_subset
  val Tarski    = def_gfp_unfold
  val induct    = def_Collect_coinduct
  end;

structure Quine_Prod =
  struct
  val sigma     = Const("QPair.QSigma", [iT, iT-->iT]--->iT)
  val pair      = Const("QPair.QPair", [iT,iT]--->iT)
  val split_name = "QPair.qsplit"
  val pair_iff  = QPair_iff
  val split_eq  = qsplit
  val fsplitI   = qsplitI
  val fsplitD   = qsplitD
  val fsplitE   = qsplitE
  end;

structure Quine_CP = CartProd_Fun (Quine_Prod);

structure Quine_Sum =
  struct
  val sum       = Const("QPair.op <+>", [iT,iT]--->iT)
  val inl       = Const("QPair.QInl", iT-->iT)
  val inr       = Const("QPair.QInr", iT-->iT)
  val elim      = Const("QPair.qcase", [iT-->iT, iT-->iT, iT]--->iT)
  val case_inl  = qcase_QInl
  val case_inr  = qcase_QInr
  val inl_iff   = QInl_iff
  val inr_iff   = QInr_iff
  val distinct  = QInl_QInr_iff
  val distinct' = QInr_QInl_iff
  val free_SEs  = Ind_Syntax.mk_free_SEs
            [distinct, distinct', inl_iff, inr_iff, Quine_Prod.pair_iff]
  end;


structure CoInd_Package =
  Add_inductive_def_Fun(structure Fp=Gfp and Pr=Quine_Prod and CP=Quine_CP
    and Su=Quine_Sum val coind = true);
