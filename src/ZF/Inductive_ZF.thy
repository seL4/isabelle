(*  Title:      ZF/Inductive_ZF.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definitions use least fixedpoints with standard products and sums
Coinductive definitions use greatest fixedpoints with Quine products and sums

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

header{*Inductive and Coinductive Definitions*}

theory Inductive_ZF
imports Fixedpt QPair Nat_ZF
keywords
  "elimination" "induction" "case_eqns" "recursor_eqns"
  "domains" "intros" "monos" "con_defs" "type_intros" "type_elims"
uses
  ("ind_syntax.ML")
  ("Tools/cartprod.ML")
  ("Tools/ind_cases.ML")
  ("Tools/inductive_package.ML")
  ("Tools/induct_tacs.ML")
  ("Tools/primrec_package.ML")
begin

lemma def_swap_iff: "a == b ==> a = c \<longleftrightarrow> c = b"
  by blast

lemma def_trans: "f == g ==> g(a) = b ==> f(a) = b"
  by simp

lemma refl_thin: "!!P. a = a ==> P ==> P" .

use "ind_syntax.ML"
use "Tools/ind_cases.ML"
use "Tools/cartprod.ML"
use "Tools/inductive_package.ML"
use "Tools/induct_tacs.ML"
use "Tools/primrec_package.ML"

setup IndCases.setup
setup DatatypeTactics.setup

ML {*
structure Lfp =
  struct
  val oper      = @{const lfp}
  val bnd_mono  = @{const bnd_mono}
  val bnd_monoI = @{thm bnd_monoI}
  val subs      = @{thm def_lfp_subset}
  val Tarski    = @{thm def_lfp_unfold}
  val induct    = @{thm def_induct}
  end;

structure Standard_Prod =
  struct
  val sigma     = @{const Sigma}
  val pair      = @{const Pair}
  val split_name = @{const_name split}
  val pair_iff  = @{thm Pair_iff}
  val split_eq  = @{thm split}
  val fsplitI   = @{thm splitI}
  val fsplitD   = @{thm splitD}
  val fsplitE   = @{thm splitE}
  end;

structure Standard_CP = CartProd_Fun (Standard_Prod);

structure Standard_Sum =
  struct
  val sum       = @{const sum}
  val inl       = @{const Inl}
  val inr       = @{const Inr}
  val elim      = @{const case}
  val case_inl  = @{thm case_Inl}
  val case_inr  = @{thm case_Inr}
  val inl_iff   = @{thm Inl_iff}
  val inr_iff   = @{thm Inr_iff}
  val distinct  = @{thm Inl_Inr_iff}
  val distinct' = @{thm Inr_Inl_iff}
  val free_SEs  = Ind_Syntax.mk_free_SEs
            [distinct, distinct', inl_iff, inr_iff, Standard_Prod.pair_iff]
  end;


structure Ind_Package =
    Add_inductive_def_Fun
      (structure Fp=Lfp and Pr=Standard_Prod and CP=Standard_CP
       and Su=Standard_Sum val coind = false);


structure Gfp =
  struct
  val oper      = @{const gfp}
  val bnd_mono  = @{const bnd_mono}
  val bnd_monoI = @{thm bnd_monoI}
  val subs      = @{thm def_gfp_subset}
  val Tarski    = @{thm def_gfp_unfold}
  val induct    = @{thm def_Collect_coinduct}
  end;

structure Quine_Prod =
  struct
  val sigma     = @{const QSigma}
  val pair      = @{const QPair}
  val split_name = @{const_name qsplit}
  val pair_iff  = @{thm QPair_iff}
  val split_eq  = @{thm qsplit}
  val fsplitI   = @{thm qsplitI}
  val fsplitD   = @{thm qsplitD}
  val fsplitE   = @{thm qsplitE}
  end;

structure Quine_CP = CartProd_Fun (Quine_Prod);

structure Quine_Sum =
  struct
  val sum       = @{const qsum}
  val inl       = @{const QInl}
  val inr       = @{const QInr}
  val elim      = @{const qcase}
  val case_inl  = @{thm qcase_QInl}
  val case_inr  = @{thm qcase_QInr}
  val inl_iff   = @{thm QInl_iff}
  val inr_iff   = @{thm QInr_iff}
  val distinct  = @{thm QInl_QInr_iff}
  val distinct' = @{thm QInr_QInl_iff}
  val free_SEs  = Ind_Syntax.mk_free_SEs
            [distinct, distinct', inl_iff, inr_iff, Quine_Prod.pair_iff]
  end;


structure CoInd_Package =
  Add_inductive_def_Fun(structure Fp=Gfp and Pr=Quine_Prod and CP=Quine_CP
    and Su=Quine_Sum val coind = true);

*}

end
