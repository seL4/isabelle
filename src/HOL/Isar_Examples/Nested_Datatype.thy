header {* Nested datatypes *}

theory Nested_Datatype
imports Main
begin

subsection {* Terms and substitution *}

datatype_new ('a, 'b) "term" =
  Var 'a
| App 'b "('a, 'b) term list"

primrec subst_term :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term"
  and subst_term_list :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term list \<Rightarrow> ('a, 'b) term list"
where
  "subst_term f (Var a) = f a"
| "subst_term f (App b ts) = App b (subst_term_list f ts)"
| "subst_term_list f [] = []"
| "subst_term_list f (t # ts) = subst_term f t # subst_term_list f ts"

lemmas subst_simps = subst_term_subst_term_list.simps

text {* \medskip A simple lemma about composition of substitutions. *}

lemma
  "subst_term (subst_term f1 \<circ> f2) t =
    subst_term f1 (subst_term f2 t)"
  and
  "subst_term_list (subst_term f1 \<circ> f2) ts =
    subst_term_list f1 (subst_term_list f2 ts)"
  by (induct t and ts) simp_all

lemma "subst_term (subst_term f1 \<circ> f2) t =
    subst_term f1 (subst_term f2 t)"
proof -
  let "?P t" = ?thesis
  let ?Q = "\<lambda>ts. subst_term_list (subst_term f1 \<circ> f2) ts =
    subst_term_list f1 (subst_term_list f2 ts)"
  show ?thesis
  proof (induct t)
    fix a show "?P (Var a)" by simp
  next
    fix b ts assume "?Q ts"
    then show "?P (App b ts)"
      by (simp only: subst_simps)
  next
    show "?Q []" by simp
  next
    fix t ts
    assume "?P t" "?Q ts" then show "?Q (t # ts)"
      by (simp only: subst_simps)
  qed
qed


subsection {* Alternative induction *}

theorem term_induct' [case_names Var App]:
  assumes var: "\<And>a. P (Var a)"
    and app: "\<And>b ts. (\<forall>t \<in> set ts. P t) \<Longrightarrow> P (App b ts)"
  shows "P t"
proof (induct t)
  fix a show "P (Var a)" by (rule var)
next
  fix b t ts assume "\<forall>t \<in> set ts. P t"
  then show "P (App b ts)" by (rule app)
next
  show "\<forall>t \<in> set []. P t" by simp
next
  fix t ts assume "P t" "\<forall>t' \<in> set ts. P t'"
  then show "\<forall>t' \<in> set (t # ts). P t'" by simp
qed

lemma "subst_term (subst_term f1 \<circ> f2) t = subst_term f1 (subst_term f2 t)"
proof (induct t rule: term_induct')
  case (Var a)
  show ?case by (simp add: o_def)
next
  case (App b ts)
  then show ?case by (induct ts) simp_all
qed

end
