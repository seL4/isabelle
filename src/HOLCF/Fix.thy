(*  Title:      HOLCF/Fix.thy
    ID:         $Id$
    Author:     Franz Regensburger

Definitions for fixed point operator and admissibility.
*)

header {* Fixed point operator and admissibility *}

theory Fix
imports Cfun Cprod Adm
begin

defaultsort pcpo

subsection {* Definitions *}

consts
  iterate :: "nat \<Rightarrow> ('a \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> 'a"
  "fix"   :: "('a \<rightarrow> 'a) \<rightarrow> 'a"

primrec
  "iterate 0 = (\<Lambda> F x. x)"
  "iterate (Suc n) = (\<Lambda> F x. F\<cdot>(iterate n\<cdot>F\<cdot>x))"

defs
  fix_def:       "fix \<equiv> \<Lambda> F. \<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>"

subsection {* Binder syntax for @{term fix} *}

syntax
  "_FIX" :: "['a, 'a] \<Rightarrow> 'a" ("(3FIX _./ _)" [1000, 10] 10)

syntax (xsymbols)
  "_FIX" :: "['a, 'a] \<Rightarrow> 'a" ("(3\<mu>_./ _)" [1000, 10] 10)

translations
  "\<mu> x. t" == "fix\<cdot>(\<Lambda> x. t)"

subsection {* Properties of @{term iterate} *}

text {* derive inductive properties of iterate from primitive recursion *}

lemma iterate_0 [simp]: "iterate 0\<cdot>F\<cdot>x = x"
by simp

lemma iterate_Suc [simp]: "iterate (Suc n)\<cdot>F\<cdot>x = F\<cdot>(iterate n\<cdot>F\<cdot>x)"
by simp

declare iterate.simps [simp del]

lemma iterate_Suc2: "iterate (Suc n)\<cdot>F\<cdot>x = iterate n\<cdot>F\<cdot>(F\<cdot>x)"
by (induct_tac n, auto)

text {*
  The sequence of function iterations is a chain.
  This property is essential since monotonicity of iterate makes no sense.
*}

lemma chain_iterate2: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> chain (\<lambda>i. iterate i\<cdot>F\<cdot>x)"
by (rule chainI, induct_tac i, auto elim: monofun_cfun_arg)

lemma chain_iterate [simp]: "chain (\<lambda>i. iterate i\<cdot>F\<cdot>\<bottom>)"
by (rule chain_iterate2 [OF minimal])

subsection {* Properties of @{term fix} *}

text {* direct connection between @{term fix} and iteration *}

lemma fix_def2: "fix\<cdot>F = (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>)"
apply (unfold fix_def)
apply (rule beta_cfun)
apply (rule cont2cont_lub)
apply (rule ch2ch_lambda)
apply (rule chain_iterate)
apply simp
done

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

lemma fix_least_less: "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
apply (simp add: fix_def2)
apply (rule is_lub_thelub)
apply (rule chain_iterate)
apply (rule ub_rangeI)
apply (induct_tac i)
apply simp
apply simp
apply (erule rev_trans_less)
apply (erule monofun_cfun_arg)
done

lemma fix_least: "F\<cdot>x = x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
by (rule fix_least_less, simp)

lemma fix_eqI: "\<lbrakk>F\<cdot>x = x; \<forall>z. F\<cdot>z = z \<longrightarrow> x \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x = fix\<cdot>F"
apply (rule antisym_less)
apply (erule allE)
apply (erule mp)
apply (rule fix_eq [symmetric])
apply (erule fix_least)
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

lemma fix_defined_iff: "(fix\<cdot>F = \<bottom>) = (F\<cdot>\<bottom> = \<bottom>)"
apply (rule iffI)
apply (erule subst)
apply (rule fix_eq [symmetric])
apply (erule fix_least [THEN UU_I])
done

lemma fix_strict: "F\<cdot>\<bottom> = \<bottom> \<Longrightarrow> fix\<cdot>F = \<bottom>"
by (simp add: fix_defined_iff)

lemma fix_defined: "F\<cdot>\<bottom> \<noteq> \<bottom> \<Longrightarrow> fix\<cdot>F \<noteq> \<bottom>"
by (simp add: fix_defined_iff)

text {* @{term fix} applied to identity and constant functions *}

lemma fix_id: "(\<mu> x. x) = \<bottom>"
by (simp add: fix_strict)

lemma fix_const: "(\<mu> x. c) = c"
by (subst fix_eq, simp)

subsection {* Fixed point induction *}

lemma fix_ind: "\<lbrakk>adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (fix\<cdot>F)"
apply (subst fix_def2)
apply (erule admD [rule_format])
apply (rule chain_iterate)
apply (induct_tac "i", simp_all)
done

lemma def_fix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P f"
by (simp add: fix_ind)

subsection {* Weak admissibility *}

constdefs
  admw :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  "admw P \<equiv> \<forall>F. (\<forall>n. P (iterate n\<cdot>F\<cdot>\<bottom>)) \<longrightarrow> P (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>)"

text {* an admissible formula is also weak admissible *}

lemma adm_impl_admw: "adm P \<Longrightarrow> admw P"
apply (unfold admw_def)
apply (intro strip)
apply (erule admD)
apply (rule chain_iterate)
apply assumption
done

text {* computational induction for weak admissible formulae *}

lemma wfix_ind: "\<lbrakk>admw P; \<forall>n. P (iterate n\<cdot>F\<cdot>\<bottom>)\<rbrakk> \<Longrightarrow> P (fix\<cdot>F)"
by (simp add: fix_def2 admw_def)

lemma def_wfix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>F; admw P; \<forall>n. P (iterate n\<cdot>F\<cdot>\<bottom>)\<rbrakk> \<Longrightarrow> P f"
by (simp, rule wfix_ind)

end
