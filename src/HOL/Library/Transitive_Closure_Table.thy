(*  Author: Stefan Berghofer, Lukas Bulwahn, TU Muenchen  *)

section \<open>A table-based implementation of the reflexive transitive closure\<close>

theory Transitive_Closure_Table
imports Main
begin

inductive rtrancl_path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  base: "rtrancl_path r x [] x"
| step: "r x y \<Longrightarrow> rtrancl_path r y ys z \<Longrightarrow> rtrancl_path r x (y # ys) z"

lemma rtranclp_eq_rtrancl_path: "r\<^sup>*\<^sup>* x y \<longleftrightarrow> (\<exists>xs. rtrancl_path r x xs y)"
proof
  show "\<exists>xs. rtrancl_path r x xs y" if "r\<^sup>*\<^sup>* x y"
    using that
  proof (induct rule: converse_rtranclp_induct)
    case base
    have "rtrancl_path r y [] y" by (rule rtrancl_path.base)
    then show ?case ..
  next
    case (step x z)
    from \<open>\<exists>xs. rtrancl_path r z xs y\<close>
    obtain xs where "rtrancl_path r z xs y" ..
    with \<open>r x z\<close> have "rtrancl_path r x (z # xs) y"
      by (rule rtrancl_path.step)
    then show ?case ..
  qed
  show "r\<^sup>*\<^sup>* x y" if "\<exists>xs. rtrancl_path r x xs y"
  proof -
    from that obtain xs where "rtrancl_path r x xs y" ..
    then show ?thesis
    proof induct
      case (base x)
      show ?case
        by (rule rtranclp.rtrancl_refl)
    next
      case (step x y ys z)
      from \<open>r x y\<close> \<open>r\<^sup>*\<^sup>* y z\<close> show ?case
        by (rule converse_rtranclp_into_rtranclp)
    qed
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
  with \<open>r x y\<close> have "rtrancl_path r x (y # (xs @ ys)) z"
    by (rule rtrancl_path.step)
  then show ?case by simp
qed

lemma rtrancl_path_appendE:
  assumes xz: "rtrancl_path r x (xs @ y # ys) z"
  obtains "rtrancl_path r x (xs @ [y]) y" and "rtrancl_path r y ys z"
  using xz
proof (induct xs arbitrary: x)
  case Nil
  then have "rtrancl_path r x (y # ys) z" by simp
  then obtain xy: "r x y" and yz: "rtrancl_path r y ys z"
    by cases auto
  from xy have "rtrancl_path r x [y] y"
    by (rule rtrancl_path.step [OF _ rtrancl_path.base])
  then have "rtrancl_path r x ([] @ [y]) y" by simp
  then show thesis using yz by (rule Nil)
next
  case (Cons a as)
  then have "rtrancl_path r x (a # (as @ y # ys)) z" by simp
  then obtain xa: "r x a" and az: "rtrancl_path r a (as @ y # ys) z"
    by cases auto
  show thesis
  proof (rule Cons(1) [OF _ az])
    assume "rtrancl_path r y ys z"
    assume "rtrancl_path r a (as @ [y]) y"
    with xa have "rtrancl_path r x (a # (as @ [y])) y"
      by (rule rtrancl_path.step)
    then have "rtrancl_path r x ((a # as) @ [y]) y"
      by simp
    then show thesis using \<open>rtrancl_path r y ys z\<close>
      by (rule Cons(2))
  qed
qed

lemma rtrancl_path_distinct:
  assumes xy: "rtrancl_path r x xs y"
  obtains xs' where "rtrancl_path r x xs' y" and "distinct (x # xs')" and "set xs' \<subseteq> set xs"
  using xy
proof (induct xs rule: measure_induct_rule [of length])
  case (less xs)
  show ?case
  proof (cases "distinct (x # xs)")
    case True
    with \<open>rtrancl_path r x xs y\<close> show ?thesis by (rule less) simp
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
      from x xs \<open>rtrancl_path r x xs y\<close> have cs: "rtrancl_path r x cs y" "set cs \<subseteq> set xs"
        by (auto elim: rtrancl_path_appendE)
      from xs have "length cs < length xs" by simp
      then show ?thesis
        by (rule less(1))(blast intro: cs less(2) order_trans del: subsetI)+
    next
      case (Cons d ds)
      with xxs have xs: "xs = ds @ a # (bs @ [a] @ cs)"
        by auto
      with \<open>rtrancl_path r x xs y\<close> obtain xa: "rtrancl_path r x (ds @ [a]) a"
        and ay: "rtrancl_path r a (bs @ a # cs) y"
        by (auto elim: rtrancl_path_appendE)
      from ay have "rtrancl_path r a cs y" by (auto elim: rtrancl_path_appendE)
      with xa have xy: "rtrancl_path r x ((ds @ [a]) @ cs) y"
        by (rule rtrancl_path_trans)
      from xs have set: "set ((ds @ [a]) @ cs) \<subseteq> set xs" by auto
      from xs have "length ((ds @ [a]) @ cs) < length xs" by simp
      then show ?thesis
        by (rule less(1))(blast intro: xy less(2) set[THEN subsetD])+
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
  shows "rtrancl_tab r ys x y"
  using path x ys
proof (induct arbitrary: ys)
  case base
  show ?case
    by (rule rtrancl_tab.base)
next
  case (step x y zs z)
  then have "x \<notin> set ys"
    by auto
  from step have "distinct (y # zs)"
    by simp
  moreover from step have "({y} \<union> set zs) \<inter> set (x # ys) = {}"
    by auto
  ultimately have "rtrancl_tab r (x # ys) y z"
    by (rule step)
  with \<open>x \<notin> set ys\<close> \<open>r x y\<close> show ?case
    by (rule rtrancl_tab.step)
qed

lemma rtrancl_tab_imp_rtrancl_path:
  assumes tab: "rtrancl_tab r ys x y"
  obtains xs where "rtrancl_path r x xs y"
  using tab
proof induct
  case base
  from rtrancl_path.base show ?case
    by (rule base)
next
  case step
  show ?case
    by (iprover intro: step rtrancl_path.step)
qed

lemma rtranclp_eq_rtrancl_tab_nil: "r\<^sup>*\<^sup>* x y \<longleftrightarrow> rtrancl_tab r [] x y"
proof
  show "rtrancl_tab r [] x y" if "r\<^sup>*\<^sup>* x y"
  proof -
    from that obtain xs where "rtrancl_path r x xs y"
      by (auto simp add: rtranclp_eq_rtrancl_path)
    then obtain xs' where xs': "rtrancl_path r x xs' y" and distinct: "distinct (x # xs')"
      by (rule rtrancl_path_distinct)
    have "({x} \<union> set xs') \<inter> set [] = {}"
      by simp
    with xs' distinct show ?thesis
      by (rule rtrancl_path_imp_rtrancl_tab)
  qed
  show "r\<^sup>*\<^sup>* x y" if "rtrancl_tab r [] x y"
  proof -
    from that obtain xs where "rtrancl_path r x xs y"
      by (rule rtrancl_tab_imp_rtrancl_path)
    then show ?thesis
      by (auto simp add: rtranclp_eq_rtrancl_path)
  qed
qed

declare rtranclp_eq_rtrancl_tab_nil [code]
declare rtranclp_eq_rtrancl_tab_nil [THEN iffD2, code_pred_intro]

code_pred rtranclp
  using rtranclp_eq_rtrancl_tab_nil [THEN iffD1] by fastforce

lemma rtrancl_path_Range: "\<lbrakk> rtrancl_path R x xs y; z \<in> set xs \<rbrakk> \<Longrightarrow> Rangep R z"
by(induction rule: rtrancl_path.induct) auto

lemma rtrancl_path_Range_end: "\<lbrakk> rtrancl_path R x xs y; xs \<noteq> [] \<rbrakk> \<Longrightarrow> Rangep R y"
by(induction rule: rtrancl_path.induct)(auto elim: rtrancl_path.cases)

lemma rtrancl_path_nth:
  "\<lbrakk> rtrancl_path R x xs y; i < length xs \<rbrakk> \<Longrightarrow> R ((x # xs) ! i) (xs ! i)"
proof(induction arbitrary: i rule: rtrancl_path.induct)
  case step thus ?case by(cases i) simp_all
qed simp

lemma rtrancl_path_last: "\<lbrakk> rtrancl_path R x xs y; xs \<noteq> [] \<rbrakk> \<Longrightarrow> last xs = y"
by(induction rule: rtrancl_path.induct)(auto elim: rtrancl_path.cases)

lemma rtrancl_path_mono:
  "\<lbrakk> rtrancl_path R x p y; \<And>x y. R x y \<Longrightarrow> S x y \<rbrakk> \<Longrightarrow> rtrancl_path S x p y"
by(induction rule: rtrancl_path.induct)(auto intro: rtrancl_path.intros)

end
