(*  Title:      HOL/Lambda/ParRed.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Properties of => and "cd", in particular the diamond property of => and
confluence of beta.
*)

header {* Parallel reduction and a complete developments *}

theory ParRed = Lambda + Commutation:


subsection {* Parallel reduction *}

consts
  par_beta :: "(dB \<times> dB) set"

syntax
  par_beta :: "[dB, dB] => bool"  (infixl "=>" 50)
translations
  "s => t" == "(s, t) \<in> par_beta"

inductive par_beta
  intros [simp, intro!]
    var: "Var n => Var n"
    abs: "s => t ==> Abs s => Abs t"
    app: "[| s => s'; t => t' |] ==> s $ t => s' $ t'"
    beta: "[| s => s'; t => t' |] ==> (Abs s) $ t => s'[t'/0]"

inductive_cases par_beta_cases [elim!]:
  "Var n => t"
  "Abs s => Abs t"
  "(Abs s) $ t => u"
  "s $ t => u"
  "Abs s => t"


subsection {* Inclusions *}

text {* @{text "beta \<subseteq> par_beta \<subseteq> beta^*"} \medskip *}

lemma par_beta_varL [simp]:
    "(Var n => t) = (t = Var n)"
  apply blast
  done

lemma par_beta_refl [simp]: "t => t"  (* par_beta_refl [intro!] causes search to blow up *)
  apply (induct_tac t)
    apply simp_all
  done

lemma beta_subset_par_beta: "beta <= par_beta"
  apply (rule subsetI)
  apply clarify
  apply (erule beta.induct)
     apply (blast intro!: par_beta_refl)+
  done

lemma par_beta_subset_beta: "par_beta <= beta^*"
  apply (rule subsetI)
  apply clarify
  apply (erule par_beta.induct)
     apply blast
    apply (blast del: rtrancl_refl intro: rtrancl_into_rtrancl)+
      -- {* @{thm[source] rtrancl_refl} complicates the proof by increasing the branching factor *}
  done


subsection {* Misc properties of par-beta *}

lemma par_beta_lift [rule_format, simp]:
    "\<forall>t' n. t => t' --> lift t n => lift t' n"
  apply (induct_tac t)
    apply fastsimp+
  done

lemma par_beta_subst [rule_format]:
    "\<forall>s s' t' n. s => s' --> t => t' --> t[s/n] => t'[s'/n]"
  apply (induct_tac t)
    apply (simp add: subst_Var)
   apply (intro strip)
   apply (erule par_beta_cases)
    apply simp
   apply (simp add: subst_subst [symmetric])
   apply (fastsimp intro!: par_beta_lift)
  apply fastsimp
  done


subsection {* Confluence (directly) *}

lemma diamond_par_beta: "diamond par_beta"
  apply (unfold diamond_def commute_def square_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule par_beta.induct)
     apply (blast intro!: par_beta_subst)+
  done


subsection {* Complete developments *}

consts
  "cd" :: "dB => dB"
recdef "cd" "measure size"
  "cd (Var n) = Var n"
  "cd (Var n $ t) = Var n $ cd t"
  "cd ((s1 $ s2) $ t) = cd (s1 $ s2) $ cd t"
  "cd (Abs u $ t) = (cd u)[cd t/0]"
  "cd (Abs s) = Abs (cd s)"

lemma par_beta_cd [rule_format]:
    "\<forall>t. s => t --> t => cd s"
  apply (induct_tac s rule: cd.induct)
      apply auto
  apply (fast intro!: par_beta_subst)
  done


subsection {* Confluence (via complete developments) *}

lemma diamond_par_beta2: "diamond par_beta"
  apply (unfold diamond_def commute_def square_def)
  apply (blast intro: par_beta_cd)
  done

theorem beta_confluent: "confluent beta"
  apply (rule diamond_par_beta2 diamond_to_confluence
    par_beta_subset_beta beta_subset_par_beta)+
  done

end