(*  Title:      HOL/Induct/Term.thy
    Author:     Stefan Berghofer,  TU Muenchen
*)

section \<open>Terms over a given alphabet\<close>

theory Term
imports Main
begin

datatype ('a, 'b) "term" =
    Var 'a
  | App 'b "('a, 'b) term list"


text \<open>\medskip Substitution function on terms\<close>

primrec subst_term :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term"
  and subst_term_list :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term list \<Rightarrow> ('a, 'b) term list"
where
  "subst_term f (Var a) = f a"
| "subst_term f (App b ts) = App b (subst_term_list f ts)"
| "subst_term_list f [] = []"
| "subst_term_list f (t # ts) = subst_term f t # subst_term_list f ts"


text \<open>\medskip A simple theorem about composition of substitutions\<close>

lemma subst_comp:
  "subst_term (subst_term f1 \<circ> f2) t =
    subst_term f1 (subst_term f2 t)"
and "subst_term_list (subst_term f1 \<circ> f2) ts =
    subst_term_list f1 (subst_term_list f2 ts)"
  by (induct t and ts rule: subst_term.induct subst_term_list.induct) simp_all


text \<open>\medskip Alternative induction rule\<close>

lemma
  assumes var: "\<And>v. P (Var v)"
    and app: "\<And>f ts. (\<forall>t \<in> set ts. P t) \<Longrightarrow> P (App f ts)"
  shows term_induct2: "P t"
    and "\<forall>t \<in> set ts. P t"
  apply (induct t and ts rule: subst_term.induct subst_term_list.induct)
     apply (rule var)
    apply (rule app)
    apply assumption
   apply simp_all
  done

end
