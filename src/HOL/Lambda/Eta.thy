(*  Title:      HOL/Lambda/Eta.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen
*)

header {* Eta-reduction *}

theory Eta = ParRed:


subsection {* Definition of eta-reduction and relatives *}

consts
  free :: "dB => nat => bool"
primrec
  "free (Var j) i = (j = i)"
  "free (s $ t) i = (free s i \<or> free t i)"
  "free (Abs s) i = free s (i + 1)"

consts
  eta :: "(dB \<times> dB) set"

syntax 
  "_eta" :: "[dB, dB] => bool"   (infixl "-e>" 50)
  "_eta_rtrancl" :: "[dB, dB] => bool"   (infixl "-e>>" 50)
  "_eta_reflcl" :: "[dB, dB] => bool"   (infixl "-e>=" 50)
translations
  "s -e> t" == "(s, t) \<in> eta"
  "s -e>> t" == "(s, t) \<in> eta^*"
  "s -e>= t" == "(s, t) \<in> eta^="

inductive eta
  intros [simp, intro]
    eta: "\<not> free s 0 ==> Abs (s $ Var 0) -e> s[dummy/0]"
    appL: "s -e> t ==> s $ u -e> t $ u"
    appR: "s -e> t ==> u $ s -e> u $ t"
    abs: "s -e> t ==> Abs s -e> Abs t"

inductive_cases eta_cases [elim!]:
  "Abs s -e> z"
  "s $ t -e> u"
  "Var i -e> t"


subsection "Properties of eta, subst and free"

lemma subst_not_free [rulify, simp]:
    "\<forall>i t u. \<not> free s i --> s[t/i] = s[u/i]"
  apply (induct_tac s)
    apply (simp_all add: subst_Var)
  done

lemma free_lift [simp]:
    "\<forall>i k. free (lift t k) i =
      (i < k \<and> free t i \<or> k < i \<and> free t (i - 1))"
  apply (induct_tac t)
    apply (auto cong: conj_cong)
  apply arith
  done

lemma free_subst [simp]:
    "\<forall>i k t. free (s[t/k]) i =
      (free s k \<and> free t i \<or> free s (if i < k then i else i + 1))"
  apply (induct_tac s)
    prefer 2
    apply simp
    apply blast
   prefer 2
   apply simp
  apply (simp add: diff_Suc subst_Var split: nat.split)
  apply clarify
  apply (erule linorder_neqE)
  apply simp_all
  done

lemma free_eta [rulify]:
    "s -e> t ==> \<forall>i. free t i = free s i"
  apply (erule eta.induct)
     apply (simp_all cong: conj_cong)
  done

lemma not_free_eta:
    "[| s -e> t; \<not> free s i |] ==> \<not> free t i"
  apply (simp add: free_eta)
  done

lemma eta_subst [rulify, simp]:
    "s -e> t ==> \<forall>u i. s[u/i] -e> t[u/i]"
  apply (erule eta.induct)
  apply (simp_all add: subst_subst [symmetric])
  done


subsection "Confluence of eta"

lemma square_eta: "square eta eta (eta^=) (eta^=)"
  apply (unfold square_def id_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply simp
  apply (erule eta.induct)
     apply (slowsimp intro: subst_not_free eta_subst free_eta [THEN iffD1])
    apply safe
       prefer 5
       apply (blast intro!: eta_subst intro: free_eta [THEN iffD1])
      apply blast+
  done

theorem eta_confluent: "confluent eta"
  apply (rule square_eta [THEN square_reflcl_confluent])
  done


subsection "Congruence rules for eta*"

lemma rtrancl_eta_Abs: "s -e>> s' ==> Abs s -e>> Abs s'"
  apply (erule rtrancl_induct)
   apply (blast intro: rtrancl_refl rtrancl_into_rtrancl)+
  done

lemma rtrancl_eta_AppL: "s -e>> s' ==> s $ t -e>> s' $ t"
  apply (erule rtrancl_induct)
   apply (blast intro: rtrancl_refl rtrancl_into_rtrancl)+
  done

lemma rtrancl_eta_AppR: "t -e>> t' ==> s $ t -e>> s $ t'"
  apply (erule rtrancl_induct)
   apply (blast intro: rtrancl_refl rtrancl_into_rtrancl)+
  done

lemma rtrancl_eta_App:
    "[| s -e>> s'; t -e>> t' |] ==> s $ t -e>> s' $ t'"
  apply (blast intro!: rtrancl_eta_AppL rtrancl_eta_AppR intro: rtrancl_trans)
  done


subsection "Commutation of beta and eta"

lemma free_beta [rulify]:
    "s -> t ==> \<forall>i. free t i --> free s i"
  apply (erule beta.induct)
     apply simp_all
  done

lemma beta_subst [rulify, intro]:
    "s -> t ==> \<forall>u i. s[u/i] -> t[u/i]"
  apply (erule beta.induct)
     apply (simp_all add: subst_subst [symmetric])
  done

lemma subst_Var_Suc [simp]: "\<forall>i. t[Var i/i] = t[Var(i)/i + 1]"
  apply (induct_tac t)
  apply (auto elim!: linorder_neqE simp: subst_Var)
  done

lemma eta_lift [rulify, simp]:
    "s -e> t ==> \<forall>i. lift s i -e> lift t i"
  apply (erule eta.induct)
     apply simp_all
  done

lemma rtrancl_eta_subst [rulify]:
    "\<forall>s t i. s -e> t --> u[s/i] -e>> u[t/i]"
  apply (induct_tac u)
    apply (simp_all add: subst_Var)
    apply (blast intro: r_into_rtrancl)
   apply (blast intro: rtrancl_eta_App)
  apply (blast intro!: rtrancl_eta_Abs eta_lift)
  done

lemma square_beta_eta: "square beta eta (eta^*) (beta^=)"
  apply (unfold square_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule beta.induct)
     apply (slowsimp intro: r_into_rtrancl rtrancl_eta_subst eta_subst)
    apply (blast intro: r_into_rtrancl rtrancl_eta_AppL)
   apply (blast intro: r_into_rtrancl rtrancl_eta_AppR)
  apply (slowsimp intro: r_into_rtrancl rtrancl_eta_Abs free_beta
    other: dB.distinct [iff del, simp])    (*23 seconds?*)
  done

lemma confluent_beta_eta: "confluent (beta \<union> eta)"
  apply (assumption |
    rule square_rtrancl_reflcl_commute confluent_Un
      beta_confluent eta_confluent square_beta_eta)+
  done


subsection "Implicit definition of eta"

text {* @{term "Abs (lift s 0 $ Var 0) -e> s"} *}

lemma not_free_iff_lifted [rulify]:
    "\<forall>i. (\<not> free s i) = (\<exists>t. s = lift t i)"
  apply (induct_tac s)
    apply simp
    apply clarify
    apply (rule iffI)
     apply (erule linorder_neqE)
      apply (rule_tac x = "Var nat" in exI)
      apply simp
     apply (rule_tac x = "Var (nat - 1)" in exI)
     apply simp
    apply clarify
    apply (rule notE)
     prefer 2
     apply assumption
    apply (erule thin_rl)
    apply (case_tac t)
      apply simp
     apply simp
    apply simp
   apply simp
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (rule allI)
   apply (rule iffI)
    apply (elim conjE exE)
    apply (rename_tac u1 u2)
    apply (rule_tac x = "u1 $ u2" in exI)
    apply simp
   apply (erule exE)
   apply (erule rev_mp)
   apply (case_tac t)
     apply simp
    apply simp
    apply blast
   apply simp
  apply simp
  apply (erule thin_rl)
  apply (rule allI)
  apply (rule iffI)
   apply (erule exE)
   apply (rule_tac x = "Abs t" in exI)
   apply simp
  apply (erule exE)
  apply (erule rev_mp)
  apply (case_tac t)
    apply simp
   apply simp
  apply simp
  apply blast
  done

theorem explicit_is_implicit:
  "(\<forall>s u. (\<not> free s 0) --> R (Abs (s $ Var 0)) (s[u/0])) =
    (\<forall>s. R (Abs (lift s 0 $ Var 0)) s)"
  apply (auto simp add: not_free_iff_lifted)
  done

end