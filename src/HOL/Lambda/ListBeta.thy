(*  Title:      HOL/Lambda/ListBeta.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

header {* Lifting beta-reduction to lists *}

theory ListBeta imports ListApplication ListOrder begin

text {*
  Lifting beta-reduction to lists of terms, reducing exactly one element.
*}

abbreviation (output)
  list_beta :: "dB list => dB list => bool"   (infixl "=>" 50)
  "(rs => ss) = ((rs, ss) : step1 beta)"

lemma head_Var_reduction:
  "Var n \<degree>\<degree> rs -> v \<Longrightarrow> \<exists>ss. rs => ss \<and> v = Var n \<degree>\<degree> ss"
  apply (induct u == "Var n \<degree>\<degree> rs" v fixing: rs set: beta)
     apply simp
    apply (rule_tac xs = rs in rev_exhaust)
     apply simp
    apply (atomize, force intro: append_step1I)
   apply (rule_tac xs = rs in rev_exhaust)
    apply simp
    apply (auto 0 3 intro: disjI2 [THEN append_step1I])
  done

lemma apps_betasE [elim!]:
  assumes major: "r \<degree>\<degree> rs -> s"
    and cases: "!!r'. [| r -> r'; s = r' \<degree>\<degree> rs |] ==> R"
      "!!rs'. [| rs => rs'; s = r \<degree>\<degree> rs' |] ==> R"
      "!!t u us. [| r = Abs t; rs = u # us; s = t[u/0] \<degree>\<degree> us |] ==> R"
  shows R
proof -
  from major have
   "(\<exists>r'. r -> r' \<and> s = r' \<degree>\<degree> rs) \<or>
    (\<exists>rs'. rs => rs' \<and> s = r \<degree>\<degree> rs') \<or>
    (\<exists>t u us. r = Abs t \<and> rs = u # us \<and> s = t[u/0] \<degree>\<degree> us)"
    apply (induct u == "r \<degree>\<degree> rs" s fixing: r rs set: beta)
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
      apply (drule App_eq_foldl_conv [THEN iffD1])
      apply (split split_if_asm)
       apply simp
       apply blast
      apply (force intro!: disjI1 [THEN append_step1I])
     apply (drule App_eq_foldl_conv [THEN iffD1])
     apply (split split_if_asm)
      apply simp
      apply blast
     apply (clarify, auto 0 3 intro!: exI intro: append_step1I)
    done
  with cases show ?thesis by blast
qed

lemma apps_preserves_beta [simp]:
    "r -> s ==> r \<degree>\<degree> ss -> s \<degree>\<degree> ss"
  by (induct ss rule: rev_induct) auto

lemma apps_preserves_beta2 [simp]:
    "r ->> s ==> r \<degree>\<degree> ss ->> s \<degree>\<degree> ss"
  apply (induct set: rtrancl)
   apply blast
  apply (blast intro: apps_preserves_beta rtrancl_into_rtrancl)
  done

lemma apps_preserves_betas [simp]:
    "rs => ss \<Longrightarrow> r \<degree>\<degree> rs -> r \<degree>\<degree> ss"
  apply (induct rs fixing: ss rule: rev_induct)
   apply simp
  apply simp
  apply (rule_tac xs = ss in rev_exhaust)
   apply simp
  apply simp
  apply (drule Snoc_step1_SnocD)
  apply blast
  done

end
