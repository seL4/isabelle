(*  Title:      ZF/ex/CoUnit.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {* Trivial codatatype definitions, one of which goes wrong! *}

theory CoUnit = Main:

text {*
  See discussion in: L C Paulson.  A Concrete Final Coalgebra Theorem
  for ZF Set Theory.  Report 334, Cambridge University Computer
  Laboratory.  1994.

  \bigskip

  This degenerate definition does not work well because the one
  constructor's definition is trivial!  The same thing occurs with
  Aczel's Special Final Coalgebra Theorem.
*}

consts
  counit :: i
codatatype
  "counit" = Con ("x \<in> counit")

inductive_cases ConE: "Con(x) \<in> counit"
  -- {* USELESS because folding on @{term "Con(xa) == xa"} fails. *}

lemma Con_iff: "Con(x) = Con(y) <-> x = y"
  -- {* Proving freeness results. *}
  by (auto elim!: counit.free_elims)

lemma counit_eq_univ: "counit = quniv(0)"
  -- {* Should be a singleton, not everything! *}
  apply (rule counit.dom_subset [THEN equalityI])
  apply (rule subsetI)
  apply (erule counit.coinduct)
   apply (rule subset_refl)
  apply (unfold counit.con_defs)
  apply fast
  done


text {*
  \medskip A similar example, but the constructor is non-degenerate
  and it works!  The resulting set is a singleton.
*}

consts
  counit2 :: i
codatatype
  "counit2" = Con2 ("x \<in> counit2", "y \<in> counit2")


inductive_cases Con2E: "Con2(x, y) \<in> counit2"

lemma Con2_iff: "Con2(x, y) = Con2(x', y') <-> x = x' & y = y'"
  -- {* Proving freeness results. *}
  by (fast elim!: counit2.free_elims)

lemma Con2_bnd_mono: "bnd_mono(univ(0), %x. Con2(x, x))"
  apply (unfold counit2.con_defs)
  apply (rule bnd_monoI)
   apply (assumption | rule subset_refl QPair_subset_univ QPair_mono)+
  done

lemma lfp_Con2_in_counit2: "lfp(univ(0), %x. Con2(x,x)) \<in> counit2"
  apply (rule singletonI [THEN counit2.coinduct])
  apply (rule qunivI [THEN singleton_subsetI])
  apply (rule subset_trans [OF lfp_subset empty_subsetI [THEN univ_mono]])
  apply (fast intro!: Con2_bnd_mono [THEN lfp_unfold])
  done

lemma counit2_Int_Vset_subset [rule_format]:
  "Ord(i) ==> \<forall>x y. x \<in> counit2 --> y \<in> counit2 --> x Int Vset(i) \<subseteq> y"
  -- {* Lemma for proving finality. *}
  apply (erule trans_induct)
  apply (tactic "safe_tac subset_cs")
  apply (erule counit2.cases)
  apply (erule counit2.cases)
  apply (unfold counit2.con_defs)
  apply (tactic {* fast_tac (subset_cs
    addSIs [QPair_Int_Vset_subset_UN RS subset_trans, QPair_mono]
    addSEs [Ord_in_Ord, Pair_inject]) 1 *})
  done

lemma counit2_implies_equal: "[| x \<in> counit2;  y \<in> counit2 |] ==> x = y"
  apply (rule equalityI)
  apply (assumption | rule conjI counit2_Int_Vset_subset [THEN Int_Vset_subset])+
  done

lemma counit2_eq_univ: "counit2 = {lfp(univ(0), %x. Con2(x,x))}"
  apply (rule equalityI)
   apply (rule_tac [2] lfp_Con2_in_counit2 [THEN singleton_subsetI])
  apply (rule subsetI)
  apply (drule lfp_Con2_in_counit2 [THEN counit2_implies_equal])
  apply (erule subst)
  apply (rule singletonI)
  done

end
