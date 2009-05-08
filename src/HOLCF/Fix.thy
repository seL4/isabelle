(*  Title:      HOLCF/Fix.thy
    Author:     Franz Regensburger
*)

header {* Fixed point operator and admissibility *}

theory Fix
imports Cfun Cprod
begin

defaultsort pcpo

subsection {* Iteration *}

consts
  iterate :: "nat \<Rightarrow> ('a::cpo \<rightarrow> 'a) \<rightarrow> ('a \<rightarrow> 'a)"

primrec
  "iterate 0 = (\<Lambda> F x. x)"
  "iterate (Suc n) = (\<Lambda> F x. F\<cdot>(iterate n\<cdot>F\<cdot>x))"

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

text {*
  The sequence of function iterations is a chain.
  This property is essential since monotonicity of iterate makes no sense.
*}

lemma chain_iterate2: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> chain (\<lambda>i. iterate i\<cdot>F\<cdot>x)"
by (rule chainI, induct_tac i, auto elim: monofun_cfun_arg)

lemma chain_iterate [simp]: "chain (\<lambda>i. iterate i\<cdot>F\<cdot>\<bottom>)"
by (rule chain_iterate2 [OF minimal])


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

lemma fix_least_below: "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
apply (simp add: fix_def2)
apply (rule is_lub_thelub)
apply (rule chain_iterate)
apply (rule ub_rangeI)
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
unfolding fix_def2
apply (erule admD)
apply (rule chain_iterate)
apply (rule nat_induct, simp_all)
done

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

subsection {* Recursive let bindings *}

definition
  CLetrec :: "('a \<rightarrow> 'a \<times> 'b) \<rightarrow> 'b" where
  "CLetrec = (\<Lambda> F. csnd\<cdot>(F\<cdot>(\<mu> x. cfst\<cdot>(F\<cdot>x))))"

nonterminals
  recbinds recbindt recbind

syntax
  "_recbind"  :: "['a, 'a] \<Rightarrow> recbind"               ("(2_ =/ _)" 10)
  ""          :: "recbind \<Rightarrow> recbindt"               ("_")
  "_recbindt" :: "[recbind, recbindt] \<Rightarrow> recbindt"   ("_,/ _")
  ""          :: "recbindt \<Rightarrow> recbinds"              ("_")
  "_recbinds" :: "[recbindt, recbinds] \<Rightarrow> recbinds"  ("_;/ _")
  "_Letrec"   :: "[recbinds, 'a] \<Rightarrow> 'a"      ("(Letrec (_)/ in (_))" 10)

translations
  (recbindt) "x = a, \<langle>y,ys\<rangle> = \<langle>b,bs\<rangle>" == (recbindt) "\<langle>x,y,ys\<rangle> = \<langle>a,b,bs\<rangle>"
  (recbindt) "x = a, y = b"          == (recbindt) "\<langle>x,y\<rangle> = \<langle>a,b\<rangle>"

translations
  "_Letrec (_recbinds b bs) e" == "_Letrec b (_Letrec bs e)"
  "Letrec xs = a in \<langle>e,es\<rangle>"    == "CONST CLetrec\<cdot>(\<Lambda> xs. \<langle>a,e,es\<rangle>)"
  "Letrec xs = a in e"         == "CONST CLetrec\<cdot>(\<Lambda> xs. \<langle>a,e\<rangle>)"

text {*
  Bekic's Theorem: Simultaneous fixed points over pairs
  can be written in terms of separate fixed points.
*}

lemma fix_cprod:
  "fix\<cdot>(F::'a \<times> 'b \<rightarrow> 'a \<times> 'b) =
   \<langle>\<mu> x. cfst\<cdot>(F\<cdot>\<langle>x, \<mu> y. csnd\<cdot>(F\<cdot>\<langle>x, y\<rangle>)\<rangle>),
    \<mu> y. csnd\<cdot>(F\<cdot>\<langle>\<mu> x. cfst\<cdot>(F\<cdot>\<langle>x, \<mu> y. csnd\<cdot>(F\<cdot>\<langle>x, y\<rangle>)\<rangle>), y\<rangle>)\<rangle>"
  (is "fix\<cdot>F = \<langle>?x, ?y\<rangle>")
proof (rule fix_eqI)
  have 1: "cfst\<cdot>(F\<cdot>\<langle>?x, ?y\<rangle>) = ?x"
    by (rule trans [symmetric, OF fix_eq], simp)
  have 2: "csnd\<cdot>(F\<cdot>\<langle>?x, ?y\<rangle>) = ?y"
    by (rule trans [symmetric, OF fix_eq], simp)
  from 1 2 show "F\<cdot>\<langle>?x, ?y\<rangle> = \<langle>?x, ?y\<rangle>" by (simp add: eq_cprod)
next
  fix z assume F_z: "F\<cdot>z = z"
  then obtain x y where z: "z = \<langle>x,y\<rangle>" by (rule_tac p=z in cprodE)
  from F_z z have F_x: "cfst\<cdot>(F\<cdot>\<langle>x, y\<rangle>) = x" by simp
  from F_z z have F_y: "csnd\<cdot>(F\<cdot>\<langle>x, y\<rangle>) = y" by simp
  let ?y1 = "\<mu> y. csnd\<cdot>(F\<cdot>\<langle>x, y\<rangle>)"
  have "?y1 \<sqsubseteq> y" by (rule fix_least, simp add: F_y)
  hence "cfst\<cdot>(F\<cdot>\<langle>x, ?y1\<rangle>) \<sqsubseteq> cfst\<cdot>(F\<cdot>\<langle>x, y\<rangle>)" by (simp add: monofun_cfun)
  hence "cfst\<cdot>(F\<cdot>\<langle>x, ?y1\<rangle>) \<sqsubseteq> x" using F_x by simp
  hence 1: "?x \<sqsubseteq> x" by (simp add: fix_least_below)
  hence "csnd\<cdot>(F\<cdot>\<langle>?x, y\<rangle>) \<sqsubseteq> csnd\<cdot>(F\<cdot>\<langle>x, y\<rangle>)" by (simp add: monofun_cfun)
  hence "csnd\<cdot>(F\<cdot>\<langle>?x, y\<rangle>) \<sqsubseteq> y" using F_y by simp
  hence 2: "?y \<sqsubseteq> y" by (simp add: fix_least_below)
  show "\<langle>?x, ?y\<rangle> \<sqsubseteq> z" using z 1 2 by simp
qed

subsection {* Weak admissibility *}

definition
  admw :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "admw P = (\<forall>F. (\<forall>n. P (iterate n\<cdot>F\<cdot>\<bottom>)) \<longrightarrow> P (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>))"

text {* an admissible formula is also weak admissible *}

lemma adm_impl_admw: "adm P \<Longrightarrow> admw P"
apply (unfold admw_def)
apply (intro strip)
apply (erule admD)
apply (rule chain_iterate)
apply (erule spec)
done

text {* computational induction for weak admissible formulae *}

lemma wfix_ind: "\<lbrakk>admw P; \<forall>n. P (iterate n\<cdot>F\<cdot>\<bottom>)\<rbrakk> \<Longrightarrow> P (fix\<cdot>F)"
by (simp add: fix_def2 admw_def)

lemma def_wfix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>F; admw P; \<forall>n. P (iterate n\<cdot>F\<cdot>\<bottom>)\<rbrakk> \<Longrightarrow> P f"
by (simp, rule wfix_ind)

end
