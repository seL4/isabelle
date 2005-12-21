
(* $Id$ *)

header {* Nested datatypes *}

theory NestedDatatype imports Main begin

subsection {* Terms and substitution *}

datatype ('a, 'b) "term" =
    Var 'a
  | App 'b "('a, 'b) term list"

consts
  subst_term :: "('a => ('a, 'b) term) => ('a, 'b) term => ('a, 'b) term"
  subst_term_list ::
    "('a => ('a, 'b) term) => ('a, 'b) term list => ('a, 'b) term list"

primrec (subst)
  "subst_term f (Var a) = f a"
  "subst_term f (App b ts) = App b (subst_term_list f ts)"
  "subst_term_list f [] = []"
  "subst_term_list f (t # ts) = subst_term f t # subst_term_list f ts"


text {*
 \medskip A simple lemma about composition of substitutions.
*}

lemma "subst_term (subst_term f1 o f2) t =
      subst_term f1 (subst_term f2 t)"
  and "subst_term_list (subst_term f1 o f2) ts =
      subst_term_list f1 (subst_term_list f2 ts)"
  by (induct t and ts) simp_all

lemma "subst_term (subst_term f1 o f2) t =
  subst_term f1 (subst_term f2 t)"
proof -
  let "?P t" = ?thesis
  let ?Q = "\<lambda>ts. subst_term_list (subst_term f1 o f2) ts =
    subst_term_list f1 (subst_term_list f2 ts)"
  show ?thesis
  proof (induct t)
    fix a show "?P (Var a)" by simp
  next
    fix b ts assume "?Q ts"
    thus "?P (App b ts)" by (simp add: o_def)
  next
    show "?Q []" by simp
  next
    fix t ts
    assume "?P t" "?Q ts" thus "?Q (t # ts)" by simp
  qed
qed


subsection {* Alternative induction *}

theorem term_induct' [case_names Var App]:
  assumes var: "!!a. P (Var a)"
    and app: "!!b ts. list_all P ts ==> P (App b ts)"
  shows "P t"
proof (induct t)
  fix a show "P (Var a)" by (rule var)
next
  fix b t ts assume "list_all P ts"
  thus "P (App b ts)" by (rule app)
next
  show "list_all P []" by simp
next
  fix t ts assume "P t" "list_all P ts"
  thus "list_all P (t # ts)" by simp
qed

lemma
  "subst_term (subst_term f1 o f2) t = subst_term f1 (subst_term f2 t)"
proof (induct t rule: term_induct')
  case (Var a)
  show ?case by (simp add: o_def)
next
  case (App b ts)
  thus ?case by (induct ts) simp_all
qed

end
