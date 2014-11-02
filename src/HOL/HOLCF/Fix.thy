(*  Title:      HOL/HOLCF/Fix.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

section {* Fixed point operator and admissibility *}

theory Fix
imports Cfun
begin

default_sort pcpo

subsection {* Iteration *}

primrec iterate :: "nat \<Rightarrow> ('a::cpo \<rightarrow> 'a) \<rightarrow> ('a \<rightarrow> 'a)" where
    "iterate 0 = (\<Lambda> F x. x)"
  | "iterate (Suc n) = (\<Lambda> F x. F\<cdot>(iterate n\<cdot>F\<cdot>x))"

text {* Derive inductive properties of iterate from primitive recursion *}

lemma iterate_0 [simp]: "iterate 0\<cdot>F\<cdot>x = x"
by simp

lemma iterate_Suc [simp]: "iterate (Suc n)\<cdot>F\<cdot>x = F\<cdot>(iterate n\<cdot>F\<cdot>x)"
by simp

declare iterate.simps [simp del]

lemma iterate_Suc2: "iterate (Suc n)\<cdot>F\<cdot>x = iterate n\<cdot>F\<cdot>(F\<cdot>x)"
by (induct n) simp_all

lemma iterate_iterate:
  "iterate m\<cdot>F\<cdot>(iterate n\<cdot>F\<cdot>x) = iterate (m + n)\<cdot>F\<cdot>x"
by (induct m) simp_all

text {* The sequence of function iterations is a chain. *}

lemma chain_iterate [simp]: "chain (\<lambda>i. iterate i\<cdot>F\<cdot>\<bottom>)"
by (rule chainI, unfold iterate_Suc2, rule monofun_cfun_arg, rule minimal)


subsection {* Least fixed point operator *}

definition
  "fix" :: "('a \<rightarrow> 'a) \<rightarrow> 'a" where
  "fix = (\<Lambda> F. \<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>)"

text {* Binder syntax for @{term fix} *}

abbreviation
  fix_syn :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"  (binder "FIX " 10) where
  "fix_syn (\<lambda>x. f x) \<equiv> fix\<cdot>(\<Lambda> x. f x)"

notation (xsymbols)
  fix_syn  (binder "\<mu> " 10)

text {* Properties of @{term fix} *}

text {* direct connection between @{term fix} and iteration *}

lemma fix_def2: "fix\<cdot>F = (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>)"
unfolding fix_def by simp

lemma iterate_below_fix: "iterate n\<cdot>f\<cdot>\<bottom> \<sqsubseteq> fix\<cdot>f"
  unfolding fix_def2
  using chain_iterate by (rule is_ub_thelub)

text {*
  Kleene's fixed point theorems for continuous functions in pointed
  omega cpo's
*}

lemma fix_eq: "fix\<cdot>F = F\<cdot>(fix\<cdot>F)"
apply (simp add: fix_def2)
apply (subst lub_range_shift [of _ 1, symmetric])
apply (rule chain_iterate)
apply (subst contlub_cfun_arg)
apply (rule chain_iterate)
apply simp
done

lemma fix_least_below: "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
apply (simp add: fix_def2)
apply (rule lub_below)
apply (rule chain_iterate)
apply (induct_tac i)
apply simp
apply simp
apply (erule rev_below_trans)
apply (erule monofun_cfun_arg)
done

lemma fix_least: "F\<cdot>x = x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
by (rule fix_least_below, simp)

lemma fix_eqI:
  assumes fixed: "F\<cdot>x = x" and least: "\<And>z. F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
  shows "fix\<cdot>F = x"
apply (rule below_antisym)
apply (rule fix_least [OF fixed])
apply (rule least [OF fix_eq [symmetric]])
done

lemma fix_eq2: "f \<equiv> fix\<cdot>F \<Longrightarrow> f = F\<cdot>f"
by (simp add: fix_eq [symmetric])

lemma fix_eq3: "f \<equiv> fix\<cdot>F \<Longrightarrow> f\<cdot>x = F\<cdot>f\<cdot>x"
by (erule fix_eq2 [THEN cfun_fun_cong])

lemma fix_eq4: "f = fix\<cdot>F \<Longrightarrow> f = F\<cdot>f"
apply (erule ssubst)
apply (rule fix_eq)
done

lemma fix_eq5: "f = fix\<cdot>F \<Longrightarrow> f\<cdot>x = F\<cdot>f\<cdot>x"
by (erule fix_eq4 [THEN cfun_fun_cong])

text {* strictness of @{term fix} *}

lemma fix_bottom_iff: "(fix\<cdot>F = \<bottom>) = (F\<cdot>\<bottom> = \<bottom>)"
apply (rule iffI)
apply (erule subst)
apply (rule fix_eq [symmetric])
apply (erule fix_least [THEN bottomI])
done

lemma fix_strict: "F\<cdot>\<bottom> = \<bottom> \<Longrightarrow> fix\<cdot>F = \<bottom>"
by (simp add: fix_bottom_iff)

lemma fix_defined: "F\<cdot>\<bottom> \<noteq> \<bottom> \<Longrightarrow> fix\<cdot>F \<noteq> \<bottom>"
by (simp add: fix_bottom_iff)

text {* @{term fix} applied to identity and constant functions *}

lemma fix_id: "(\<mu> x. x) = \<bottom>"
by (simp add: fix_strict)

lemma fix_const: "(\<mu> x. c) = c"
by (subst fix_eq, simp)

subsection {* Fixed point induction *}

lemma fix_ind: "\<lbrakk>adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (fix\<cdot>F)"
unfolding fix_def2
apply (erule admD)
apply (rule chain_iterate)
apply (rule nat_induct, simp_all)
done

lemma cont_fix_ind:
  "\<lbrakk>cont F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F x)\<rbrakk> \<Longrightarrow> P (fix\<cdot>(Abs_cfun F))"
by (simp add: fix_ind)

lemma def_fix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P f"
by (simp add: fix_ind)

lemma fix_ind2:
  assumes adm: "adm P"
  assumes 0: "P \<bottom>" and 1: "P (F\<cdot>\<bottom>)"
  assumes step: "\<And>x. \<lbrakk>P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
  shows "P (fix\<cdot>F)"
unfolding fix_def2
apply (rule admD [OF adm chain_iterate])
apply (rule nat_less_induct)
apply (case_tac n)
apply (simp add: 0)
apply (case_tac nat)
apply (simp add: 1)
apply (frule_tac x=nat in spec)
apply (simp add: step)
done

lemma parallel_fix_ind:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes base: "P \<bottom> \<bottom>"
  assumes step: "\<And>x y. P x y \<Longrightarrow> P (F\<cdot>x) (G\<cdot>y)"
  shows "P (fix\<cdot>F) (fix\<cdot>G)"
proof -
  from adm have adm': "adm (split P)"
    unfolding split_def .
  have "\<And>i. P (iterate i\<cdot>F\<cdot>\<bottom>) (iterate i\<cdot>G\<cdot>\<bottom>)"
    by (induct_tac i, simp add: base, simp add: step)
  hence "\<And>i. split P (iterate i\<cdot>F\<cdot>\<bottom>, iterate i\<cdot>G\<cdot>\<bottom>)"
    by simp
  hence "split P (\<Squnion>i. (iterate i\<cdot>F\<cdot>\<bottom>, iterate i\<cdot>G\<cdot>\<bottom>))"
    by - (rule admD [OF adm'], simp, assumption)
  hence "split P (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>, \<Squnion>i. iterate i\<cdot>G\<cdot>\<bottom>)"
    by (simp add: lub_Pair)
  hence "P (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>) (\<Squnion>i. iterate i\<cdot>G\<cdot>\<bottom>)"
    by simp
  thus "P (fix\<cdot>F) (fix\<cdot>G)"
    by (simp add: fix_def2)
qed

lemma cont_parallel_fix_ind:
  assumes "cont F" and "cont G"
  assumes "adm (\<lambda>x. P (fst x) (snd x))"
  assumes "P \<bottom> \<bottom>"
  assumes "\<And>x y. P x y \<Longrightarrow> P (F x) (G y)"
  shows "P (fix\<cdot>(Abs_cfun F)) (fix\<cdot>(Abs_cfun G))"
by (rule parallel_fix_ind, simp_all add: assms)

subsection {* Fixed-points on product types *}

text {*
  Bekic's Theorem: Simultaneous fixed points over pairs
  can be written in terms of separate fixed points.
*}

lemma fix_cprod:
  "fix\<cdot>(F::'a \<times> 'b \<rightarrow> 'a \<times> 'b) =
   (\<mu> x. fst (F\<cdot>(x, \<mu> y. snd (F\<cdot>(x, y)))),
    \<mu> y. snd (F\<cdot>(\<mu> x. fst (F\<cdot>(x, \<mu> y. snd (F\<cdot>(x, y)))), y)))"
  (is "fix\<cdot>F = (?x, ?y)")
proof (rule fix_eqI)
  have 1: "fst (F\<cdot>(?x, ?y)) = ?x"
    by (rule trans [symmetric, OF fix_eq], simp)
  have 2: "snd (F\<cdot>(?x, ?y)) = ?y"
    by (rule trans [symmetric, OF fix_eq], simp)
  from 1 2 show "F\<cdot>(?x, ?y) = (?x, ?y)" by (simp add: prod_eq_iff)
next
  fix z assume F_z: "F\<cdot>z = z"
  obtain x y where z: "z = (x,y)" by (rule prod.exhaust)
  from F_z z have F_x: "fst (F\<cdot>(x, y)) = x" by simp
  from F_z z have F_y: "snd (F\<cdot>(x, y)) = y" by simp
  let ?y1 = "\<mu> y. snd (F\<cdot>(x, y))"
  have "?y1 \<sqsubseteq> y" by (rule fix_least, simp add: F_y)
  hence "fst (F\<cdot>(x, ?y1)) \<sqsubseteq> fst (F\<cdot>(x, y))"
    by (simp add: fst_monofun monofun_cfun)
  hence "fst (F\<cdot>(x, ?y1)) \<sqsubseteq> x" using F_x by simp
  hence 1: "?x \<sqsubseteq> x" by (simp add: fix_least_below)
  hence "snd (F\<cdot>(?x, y)) \<sqsubseteq> snd (F\<cdot>(x, y))"
    by (simp add: snd_monofun monofun_cfun)
  hence "snd (F\<cdot>(?x, y)) \<sqsubseteq> y" using F_y by simp
  hence 2: "?y \<sqsubseteq> y" by (simp add: fix_least_below)
  show "(?x, ?y) \<sqsubseteq> z" using z 1 2 by simp
qed

end
