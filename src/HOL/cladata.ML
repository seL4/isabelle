(*  Title:      HOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner.
*)


(** Applying HypsubstFun to generate hyp_subst_tac **)
section "Classical Reasoner";

structure Hypsubst_Data =
  struct
  structure Simplifier = Simplifier
  (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("op =",T)  $ t $ u) = (t, u, domain_type T)
  val dest_Trueprop = HOLogic.dest_Trueprop
  val dest_imp = HOLogic.dest_imp
  val eq_reflection = eq_reflection
  val imp_intr = impI
  val rev_mp = rev_mp
  val subst = subst
  val sym = sym
  val thin_refl = prove_goal HOL.thy 
		  "!!X. [|x=x; PROP W|] ==> PROP W" (K [atac 1]);
  end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val sizef     = size_of_thm
  val mp        = mp
  val not_elim  = notE
  val classical = classical
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Classical = ClassicalFun(Classical_Data);
open Classical;

(*Propositional rules*)
val prop_cs = empty_cs addSIs [refl,TrueI,conjI,disjCI,impI,notI,iffI]
                       addSEs [conjE,disjE,impCE,FalseE,iffCE];

(*Quantifier rules*)
val HOL_cs = prop_cs addSIs [allI,ex_ex1I] addIs [exI, select_equality] 
                     addSEs [exE] addEs [allE];

claset_ref() := HOL_cs;

(*Better then ex1E for classical reasoner: needs no quantifier duplication!*)
val major::prems = goal thy
    "[| ?! x. P(x);                                              \
\       !!x. [| P(x);  ALL y y'. P(y) & P(y') --> y=y' |] ==> R  \
\    |] ==> R";
by (rtac (major RS ex1E) 1);
by (REPEAT (ares_tac (allI::prems) 1));
by (etac (dup_elim allE) 1);
by (Fast_tac 1);
qed "alt_ex1E";

AddSEs [alt_ex1E];

(*** Applying BlastFun to create Blast_tac ***)
structure Blast_Data = 
  struct
  type claset	= Classical.claset
  val notE	= notE
  val ccontr	= ccontr
  val contr_tac = Classical.contr_tac
  val dup_intr	= Classical.dup_intr
  val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  val claset	= Classical.claset
  val rep_cs    = Classical.rep_cs
  val cla_modifiers = Classical.cla_modifiers;
  val cla_meth' = Classical.cla_meth'
  end;

structure Blast = BlastFun(Blast_Data);
Blast.overloaded ("op =", domain_type);	(*overloading of equality as iff*)

val Blast_tac = Blast.Blast_tac
and blast_tac = Blast.blast_tac;
