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
  val thin_refl = prove_goal (the_context ())
		  "!!X. [|x=x; PROP W|] ==> PROP W" (K [atac 1]);
  end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;


(*** Applying Make_Elim_Fun to create a classical "make_elim" rule ***)
structure Make_Elim_Data =
struct
  val classical = classical
end;

structure Make_Elim = Make_Elim_Fun (Make_Elim_Data);

(*we don't redeclare the original make_elim (Tactic.make_elim) for 
  compatibliity with strange things done in many existing proofs *)
val cla_make_elim = Make_Elim.make_elim;

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val make_elim = cla_make_elim
  val mp        = mp
  val not_elim  = notE
  val classical = classical
  val sizef     = size_of_thm
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Classical = ClassicalFun(Classical_Data);
structure BasicClassical: BASIC_CLASSICAL = Classical; open BasicClassical;
structure Obtain = ObtainFun(val that_atts = [Simplifier.simp_add_local, Classical.haz_intro_local]);

(*Propositional rules*)
val prop_cs = empty_cs addSIs [refl,TrueI,conjI,disjCI,impI,notI,iffI]
                       addSEs [conjE,disjE,impCE,FalseE,iffCE];

(*Quantifier rules*)
val HOL_cs = prop_cs addSIs [allI,ex_ex1I] addIs [exI, select_equality] 
                     addSEs [exE] addEs [allE];

val clasetup = [fn thy => (claset_ref_of thy := HOL_cs; thy)];
