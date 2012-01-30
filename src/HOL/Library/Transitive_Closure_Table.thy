(* Author: Stefan Berghofer, Lukas Bulwahn, TU Muenchen *)

header {* A tabled implementation of the reflexive transitive closure *}

theory Transitive_Closure_Table
imports Main
begin

inductive rtrancl_path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  base: "rtrancl_path r x [] x"
| step: "r x y \<Longrightarrow> rtrancl_path r y ys z \<Longrightarrow> rtrancl_path r x (y # ys) z"

lemma rtranclp_eq_rtrancl_path: "r\<^sup>*\<^sup>* x y = (\<exists>xs. rtrancl_path r x xs y)"
proof
  assume "r\<^sup>*\<^sup>* x y"
  then show "\<exists>xs. rtrancl_path r x xs y"
  proof (induct rule: converse_rtranclp_induct)
    case base
    have "rtrancl_path r y [] y" by (rule rtrancl_path.base)
    then show ?case ..
  next
    case (step x z)
    from `\<exists>xs. rtrancl_path r z xs y`
    obtain xs where "rtrancl_path r z xs y" ..
    with `r x z` have "rtrancl_path r x (z # xs) y"
      by (rule rtrancl_path.step)
    then show ?case ..
  qed
next
  assume "\<exists>xs. rtrancl_path r x xs y"
  then obtain xs where "rtrancl_path r x xs y" ..
  then show "r\<^sup>*\<^sup>* x y"
  proof induct
    case (base x)
    show ?case by (rule rtranclp.rtrancl_refl)
  next
    case (step x y ys z)
    from `r x y` `r\<^sup>*\<^sup>* y z` show ?case
      by (rule converse_rtranclp_into_rtranclp)
  qed
qed

lemma rtrancl_path_trans:
  assumes xy: "rtrancl_path r x xs y"
  and yz: "rtrancl_path r y ys z"
  shows "rtrancl_path r x (xs @ ys) z" using xy yz
proof (induct arbitrary: z)
  case (base x)
  then show ?case by simp
next
  case (step x y xs)
  then have "rtrancl_path r y (xs @ ys) z"
    by simp
  with `r x y` have "rtrancl_path r x (y # (xs @ ys)) z"
    by (rule rtrancl_path.step)
  then show ?case by simp
qed

lemma rtrancl_path_appendE:
  assumes xz: "rtrancl_path r x (xs @ y # ys) z"
  obtains "rtrancl_path r x (xs @ [y]) y" and "rtrancl_path r y ys z" using xz
proof (induct xs arbitrary: x)
  case Nil
  then have "rtrancl_path r x (y # ys) z" by simp
  then obtain xy: "r x y" and yz: "rtrancl_path r y ys z"
    by cases auto
  from xy have "rtrancl_path r x [y] y"
    by (rule rtrancl_path.step [OF _ rtrancl_path.base])
  then have "rtrancl_path r x ([] @ [y]) y" by simp
  then show ?thesis using yz by (rule Nil)
next
  case (Cons a as)
  then have "rtrancl_path r x (a # (as @ y # ys)) z" by simp
  then obtain xa: "r x a" and az: "rtrancl_path r a (as @ y # ys) z"
    by cases auto
  show ?thesis
  proof (rule Cons(1) [OF _ az])
    assume "rtrancl_path r y ys z"
    assume "rtrancl_path r a (as @ [y]) y"
    with xa have "rtrancl_path r x (a # (as @ [y])) y"
      by (rule rtrancl_path.step)
    then have "rtrancl_path r x ((a # as) @ [y]) y"
      by simp
    then show ?thesis using `rtrancl_path r y ys z`
      by (rule Cons(2))
  qed
qed

lemma rtrancl_path_distinct:
  assumes xy: "rtrancl_path r x xs y"
  obtains xs' where "rtrancl_path r x xs' y" and "distinct (x # xs')" using xy
proof (induct xs rule: measure_induct_rule [of length])
  case (less xs)
  show ?case
  proof (cases "distinct (x # xs)")
    case True
    with `rtrancl_path r x xs y` show ?thesis by (rule less)
  next
    case False
    then have "\<exists>as bs cs a. x # xs = as @ [a] @ bs @ [a] @ cs"
      by (rule not_distinct_decomp)
    then obtain as bs cs a where xxs: "x # xs = as @ [a] @ bs @ [a] @ cs"
      by iprover
    show ?thesis
    proof (cases as)
      case Nil
      with xxs have x: "x = a" and xs: "xs = bs @ a # cs"
        by auto
      from x xs `rtrancl_path r x xs y` have cs: "rtrancl_path r x cs y"
        by (auto elim: rtrancl_path_appendE)
      from xs have "length cs < length xs" by simp
      then show ?thesis
        by (rule less(1)) (iprover intro: cs less(2))+
    next
      case (Cons d ds)
      with xxs have xs: "xs = ds @ a # (bs @ [a] @ cs)"
        by auto
      with `rtrancl_path r x xs y` obtain xa: "rtrancl_path r x (ds @ [a]) a"
        and ay: "rtrancl_path r a (bs @ a # cs) y"
        by (auto elim: rtrancl_path_appendE)
      from ay have "rtrancl_path r a cs y" by (auto elim: rtrancl_path_appendE)
      with xa have xy: "rtrancl_path r x ((ds @ [a]) @ cs) y"
        by (rule rtrancl_path_trans)
      from xs have "length ((ds @ [a]) @ cs) < length xs" by simp
      then show ?thesis
        by (rule less(1)) (iprover intro: xy less(2))+
    qed
  qed
qed

inductive rtrancl_tab :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  base: "rtrancl_tab r xs x x"
| step: "x \<notin> set xs \<Longrightarrow> r x y \<Longrightarrow> rtrancl_tab r (x # xs) y z \<Longrightarrow> rtrancl_tab r xs x z"

lemma rtrancl_path_imp_rtrancl_tab:
  assumes path: "rtrancl_path r x xs y"
  and x: "distinct (x # xs)"
  and ys: "({x} \<union> set xs) \<inter> set ys = {}"
  shows "rtrancl_tab r ys x y" using path x ys
proof (induct arbitrary: ys)
  case base
  show ?case by (rule rtrancl_tab.base)
next
  case (step x y zs z)
  then have "x \<notin> set ys" by auto
  from step have "distinct (y # zs)" by simp
  moreover from step have "({y} \<union> set zs) \<inter> set (x # ys) = {}"
    by auto
  ultimately have "rtrancl_tab r (x # ys) y z"
    by (rule step)
  with `x \<notin> set ys` `r x y`
  show ?case by (rule rtrancl_tab.step)
qed

lemma rtrancl_tab_imp_rtrancl_path:
  assumes tab: "rtrancl_tab r ys x y"
  obtains xs where "rtrancl_path r x xs y" using tab
proof induct
  case base
  from rtrancl_path.base show ?case by (rule base)
next
  case step show ?case by (iprover intro: step rtrancl_path.step)
qed

lemma rtranclp_eq_rtrancl_tab_nil: "r\<^sup>*\<^sup>* x y = rtrancl_tab r [] x y"
proof
  assume "r\<^sup>*\<^sup>* x y"
  then obtain xs where "rtrancl_path r x xs y"
    by (auto simp add: rtranclp_eq_rtrancl_path)
  then obtain xs' where xs': "rtrancl_path r x xs' y"
    and distinct: "distinct (x # xs')"
    by (rule rtrancl_path_distinct)
  have "({x} \<union> set xs') \<inter> set [] = {}" by simp
  with xs' distinct show "rtrancl_tab r [] x y"
    by (rule rtrancl_path_imp_rtrancl_tab)
next
  assume "rtrancl_tab r [] x y"
  then obtain xs where "rtrancl_path r x xs y"
    by (rule rtrancl_tab_imp_rtrancl_path)
  then show "r\<^sup>*\<^sup>* x y"
    by (auto simp add: rtranclp_eq_rtrancl_path)
qed

declare rtranclp_rtrancl_eq[code del]
declare rtranclp_eq_rtrancl_tab_nil[THEN iffD2, code_pred_intro]

code_pred rtranclp using rtranclp_eq_rtrancl_tab_nil [THEN iffD1] by fastforce

subsection {* A simple example *}

datatype ty = A | B | C

inductive test :: "ty \<Rightarrow> ty \<Rightarrow> bool"
where
  "test A B"
| "test B A"
| "test B C"

subsubsection {* Invoking with the predicate compiler and the generic code generator *}

code_pred test .

values "{x. test\<^sup>*\<^sup>* A C}"
values "{x. test\<^sup>*\<^sup>* C A}"
values "{x. test\<^sup>*\<^sup>* A x}"
values "{x. test\<^sup>*\<^sup>* x C}"

value "test\<^sup>*\<^sup>* A C"
value "test\<^sup>*\<^sup>* C A"

hide_type ty
hide_const test A B C

end