(*  Title:      HOL/Lambda/ListBeta.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

header {* Lifting beta-reduction to lists *}

theory ListBeta = ListApplication + ListOrder:

text {*
  Lifting beta-reduction to lists of terms, reducing exactly one element.
*}

syntax
  "_list_beta" :: "dB => dB => bool"   (infixl "=>" 50)
translations
  "rs => ss" == "(rs, ss) : step1 beta"

lemma head_Var_reduction_aux:
  "v -> v' ==> \<forall>rs. v = Var n \<degree>\<degree> rs --> (\<exists>ss. rs => ss \<and> v' = Var n \<degree>\<degree> ss)"
  apply (erule beta.induct)
     apply simp
    apply (rule allI)
    apply (rule_tac xs = rs in rev_exhaust)
     apply simp
    apply (force intro: append_step1I)
   apply (rule allI)
   apply (rule_tac xs = rs in rev_exhaust)
    apply simp
    apply (auto 0 3 intro: disjI2 [THEN append_step1I])
  done

lemma head_Var_reduction:
  "Var n \<degree>\<degree> rs -> v ==> (\<exists>ss. rs => ss \<and> v = Var n \<degree>\<degree> ss)"
  apply (drule head_Var_reduction_aux)
  apply blast
  done

lemma apps_betasE_aux:
  "u -> u' ==> \<forall>r rs. u = r \<degree>\<degree> rs -->
    ((\<exists>r'. r -> r' \<and> u' = r' \<degree>\<degree> rs) \<or>
     (\<exists>rs'. rs => rs' \<and> u' = r \<degree>\<degree> rs') \<or>
     (\<exists>s t ts. r = Abs s \<and> rs = t # ts \<and> u' = s[t/0] \<degree>\<degree> ts))"
  apply (erule beta.induct)
     apply (clarify del: disjCI)
     apply (case_tac r)
       apply simp
      apply (simp add: App_eq_foldl_conv)
      apply (split split_if_asm)
       apply simp
       apply blast
      apply simp
     apply (simp add: App_eq_foldl_conv)
     apply (split split_if_asm)
      apply simp
     apply simp
    apply (clarify del: disjCI)
    apply (drule App_eq_foldl_conv [THEN iffD1])
    apply (split split_if_asm)
     apply simp
     apply blast
    apply (force intro!: disjI1 [THEN append_step1I])
   apply (clarify del: disjCI)
   apply (drule App_eq_foldl_conv [THEN iffD1])
   apply (split split_if_asm)
    apply simp
    apply blast
   apply (clarify, auto 0 3 intro!: exI intro: append_step1I)
  done

lemma apps_betasE [elim!]:
  "[| r \<degree>\<degree> rs -> s; !!r'. [| r -> r'; s = r' \<degree>\<degree> rs |] ==> R;
    !!rs'. [| rs => rs'; s = r \<degree>\<degree> rs' |] ==> R;
    !!t u us. [| r = Abs t; rs = u # us; s = t[u/0] \<degree>\<degree> us |] ==> R |]
  ==> R"
proof -
  assume major: "r \<degree>\<degree> rs -> s"
  case rule_context
  show ?thesis
    apply (cut_tac major [THEN apps_betasE_aux, THEN spec, THEN spec])
    apply (assumption | rule refl | erule prems exE conjE impE disjE)+
    done
qed

lemma apps_preserves_beta [simp]:
    "r -> s ==> r \<degree>\<degree> ss -> s \<degree>\<degree> ss"
  apply (induct_tac ss rule: rev_induct)
  apply auto
  done

lemma apps_preserves_beta2 [simp]:
    "r ->> s ==> r \<degree>\<degree> ss ->> s \<degree>\<degree> ss"
  apply (erule rtrancl_induct)
   apply blast
  apply (blast intro: apps_preserves_beta rtrancl_into_rtrancl)
  done

lemma apps_preserves_betas [rule_format, simp]:
    "\<forall>ss. rs => ss --> r \<degree>\<degree> rs -> r \<degree>\<degree> ss"
  apply (induct_tac rs rule: rev_induct)
   apply simp
  apply simp
  apply clarify
  apply (rule_tac xs = ss in rev_exhaust)
   apply simp
  apply simp
  apply (drule Snoc_step1_SnocD)
  apply blast
  done

end
