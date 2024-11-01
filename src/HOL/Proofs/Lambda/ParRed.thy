(*  Title:      HOL/Proofs/Lambda/ParRed.thy
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Properties of => and "cd", in particular the diamond property of => and
confluence of beta.
*)

section \<open>Parallel reduction and a complete developments\<close>

theory ParRed imports Lambda Commutation begin


subsection \<open>Parallel reduction\<close>

inductive par_beta :: "[dB, dB] => bool"  (infixl \<open>=>\<close> 50)
  where
    var [simp, intro!]: "Var n => Var n"
  | abs [simp, intro!]: "s => t ==> Abs s => Abs t"
  | app [simp, intro!]: "[| s => s'; t => t' |] ==> s \<degree> t => s' \<degree> t'"
  | beta [simp, intro!]: "[| s => s'; t => t' |] ==> (Abs s) \<degree> t => s'[t'/0]"

inductive_cases par_beta_cases [elim!]:
  "Var n => t"
  "Abs s => Abs t"
  "(Abs s) \<degree> t => u"
  "s \<degree> t => u"
  "Abs s => t"


subsection \<open>Inclusions\<close>

text \<open>\<open>beta \<subseteq> par_beta \<subseteq> beta\<^sup>*\<close> \medskip\<close>

lemma par_beta_varL [simp]:
    "(Var n => t) = (t = Var n)"
  by blast

lemma par_beta_refl [simp]: "t => t"  (* par_beta_refl [intro!] causes search to blow up *)
  by (induct t) simp_all

lemma beta_subset_par_beta: "beta <= par_beta"
  apply (rule predicate2I)
  apply (erule beta.induct)
     apply (blast intro!: par_beta_refl)+
  done

lemma par_beta_subset_beta: "par_beta \<le> beta\<^sup>*\<^sup>*"
  apply (rule predicate2I)
  apply (erule par_beta.induct)
     apply blast
    apply (blast del: rtranclp.rtrancl_refl intro: rtranclp.rtrancl_into_rtrancl)+
      \<comment> \<open>@{thm[source] rtrancl_refl} complicates the proof by increasing the branching factor\<close>
  done


subsection \<open>Misc properties of \<open>par_beta\<close>\<close>

lemma par_beta_lift [simp]:
    "t => t' \<Longrightarrow> lift t n => lift t' n"
  by (induct t arbitrary: t' n) fastforce+

lemma par_beta_subst:
    "s => s' \<Longrightarrow> t => t' \<Longrightarrow> t[s/n] => t'[s'/n]"
  apply (induct t arbitrary: s s' t' n)
    apply (simp add: subst_Var)
   apply (erule par_beta_cases)
    apply simp
   apply (simp add: subst_subst [symmetric])
   apply (fastforce intro!: par_beta_lift)
  apply fastforce
  done


subsection \<open>Confluence (directly)\<close>

lemma diamond_par_beta: "diamond par_beta"
  apply (unfold diamond_def commute_def square_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule par_beta.induct)
     apply (blast intro!: par_beta_subst)+
  done


subsection \<open>Complete developments\<close>

fun
  cd :: "dB => dB"
where
  "cd (Var n) = Var n"
| "cd (Var n \<degree> t) = Var n \<degree> cd t"
| "cd ((s1 \<degree> s2) \<degree> t) = cd (s1 \<degree> s2) \<degree> cd t"
| "cd (Abs u \<degree> t) = (cd u)[cd t/0]"
| "cd (Abs s) = Abs (cd s)"

lemma par_beta_cd: "s => t \<Longrightarrow> t => cd s"
  apply (induct s arbitrary: t rule: cd.induct)
      apply auto
  apply (fast intro!: par_beta_subst)
  done


subsection \<open>Confluence (via complete developments)\<close>

lemma diamond_par_beta2: "diamond par_beta"
  unfolding diamond_def commute_def square_def
  by (blast intro: par_beta_cd)

theorem beta_confluent: "confluent beta"
  by (rule diamond_par_beta2 diamond_to_confluence
    par_beta_subset_beta beta_subset_par_beta)+

end
