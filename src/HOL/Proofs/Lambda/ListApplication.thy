(*  Title:      HOL/Proofs/Lambda/ListApplication.thy
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

header {* Application of a term to a list of terms *}

theory ListApplication imports Lambda begin

abbreviation
  list_application :: "dB => dB list => dB"  (infixl "\<degree>\<degree>" 150) where
  "t \<degree>\<degree> ts == foldl (op \<degree>) t ts"

lemma apps_eq_tail_conv [iff]: "(r \<degree>\<degree> ts = s \<degree>\<degree> ts) = (r = s)"
  by (induct ts rule: rev_induct) auto

lemma Var_eq_apps_conv [iff]: "(Var m = s \<degree>\<degree> ss) = (Var m = s \<and> ss = [])"
  by (induct ss arbitrary: s) auto

lemma Var_apps_eq_Var_apps_conv [iff]:
    "(Var m \<degree>\<degree> rs = Var n \<degree>\<degree> ss) = (m = n \<and> rs = ss)"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply simp
   apply blast
  apply (induct_tac ss rule: rev_induct)
   apply auto
  done

lemma App_eq_foldl_conv:
  "(r \<degree> s = t \<degree>\<degree> ts) =
    (if ts = [] then r \<degree> s = t
    else (\<exists>ss. ts = ss @ [s] \<and> r = t \<degree>\<degree> ss))"
  apply (rule_tac xs = ts in rev_exhaust)
   apply auto
  done

lemma Abs_eq_apps_conv [iff]:
    "(Abs r = s \<degree>\<degree> ss) = (Abs r = s \<and> ss = [])"
  by (induct ss rule: rev_induct) auto

lemma apps_eq_Abs_conv [iff]: "(s \<degree>\<degree> ss = Abs r) = (s = Abs r \<and> ss = [])"
  by (induct ss rule: rev_induct) auto

lemma Abs_apps_eq_Abs_apps_conv [iff]:
    "(Abs r \<degree>\<degree> rs = Abs s \<degree>\<degree> ss) = (r = s \<and> rs = ss)"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply simp
   apply blast
  apply (induct_tac ss rule: rev_induct)
   apply auto
  done

lemma Abs_App_neq_Var_apps [iff]:
    "Abs s \<degree> t \<noteq> Var n \<degree>\<degree> ss"
  by (induct ss arbitrary: s t rule: rev_induct) auto

lemma Var_apps_neq_Abs_apps [iff]:
    "Var n \<degree>\<degree> ts \<noteq> Abs r \<degree>\<degree> ss"
  apply (induct ss arbitrary: ts rule: rev_induct)
   apply simp
  apply (induct_tac ts rule: rev_induct)
   apply auto
  done

lemma ex_head_tail:
  "\<exists>ts h. t = h \<degree>\<degree> ts \<and> ((\<exists>n. h = Var n) \<or> (\<exists>u. h = Abs u))"
  apply (induct t)
    apply (rule_tac x = "[]" in exI)
    apply simp
   apply clarify
   apply (rename_tac ts1 ts2 h1 h2)
   apply (rule_tac x = "ts1 @ [h2 \<degree>\<degree> ts2]" in exI)
   apply simp
  apply simp
  done

lemma size_apps [simp]:
  "size (r \<degree>\<degree> rs) = size r + foldl (op +) 0 (map size rs) + length rs"
  by (induct rs rule: rev_induct) auto

lemma lem0: "[| (0::nat) < k; m <= n |] ==> m < n + k"
  by simp

lemma lift_map [simp]:
    "lift (t \<degree>\<degree> ts) i = lift t i \<degree>\<degree> map (\<lambda>t. lift t i) ts"
  by (induct ts arbitrary: t) simp_all

lemma subst_map [simp]:
    "subst (t \<degree>\<degree> ts) u i = subst t u i \<degree>\<degree> map (\<lambda>t. subst t u i) ts"
  by (induct ts arbitrary: t) simp_all

lemma app_last: "(t \<degree>\<degree> ts) \<degree> u = t \<degree>\<degree> (ts @ [u])"
  by simp


text {* \medskip A customized induction schema for @{text "\<degree>\<degree>"}. *}

lemma lem:
  assumes "!!n ts. \<forall>t \<in> set ts. P t ==> P (Var n \<degree>\<degree> ts)"
    and "!!u ts. [| P u; \<forall>t \<in> set ts. P t |] ==> P (Abs u \<degree>\<degree> ts)"
  shows "size t = n \<Longrightarrow> P t"
  apply (induct n arbitrary: t rule: nat_less_induct)
  apply (cut_tac t = t in ex_head_tail)
  apply clarify
  apply (erule disjE)
   apply clarify
   apply (rule assms)
   apply clarify
   apply (erule allE, erule impE)
    prefer 2
    apply (erule allE, erule mp, rule refl)
   apply simp
   apply (simp only: foldl_conv_fold add_commute fold_plus_listsum_rev)
   apply (fastforce simp add: listsum_map_remove1)
  apply clarify
  apply (rule assms)
   apply (erule allE, erule impE)
    prefer 2
    apply (erule allE, erule mp, rule refl)
   apply simp
  apply clarify
  apply (erule allE, erule impE)
   prefer 2
   apply (erule allE, erule mp, rule refl)
  apply simp
  apply (rule le_imp_less_Suc)
  apply (rule trans_le_add1)
  apply (rule trans_le_add2)
  apply (simp only: foldl_conv_fold add_commute fold_plus_listsum_rev)
  apply (simp add: member_le_listsum_nat)
  done

theorem Apps_dB_induct:
  assumes "!!n ts. \<forall>t \<in> set ts. P t ==> P (Var n \<degree>\<degree> ts)"
    and "!!u ts. [| P u; \<forall>t \<in> set ts. P t |] ==> P (Abs u \<degree>\<degree> ts)"
  shows "P t"
  apply (rule_tac t = t in lem)
    prefer 3
    apply (rule refl)
    using assms apply iprover+
  done

end

