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
  iterate :: "nat \<Rightarrow> ('a \<rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  Ifix    :: "('a \<rightarrow> 'a) \<Rightarrow> 'a"
  "fix"   :: "('a \<rightarrow> 'a) \<rightarrow> 'a"
  admw    :: "('a \<Rightarrow> bool) \<Rightarrow> bool"

primrec
  iterate_0:   "iterate 0 F x = x"
  iterate_Suc: "iterate (Suc n) F x  = F\<cdot>(iterate n F x)"

defs
  Ifix_def:      "Ifix \<equiv> \<lambda>F. \<Squnion>i. iterate i F \<bottom>"
  fix_def:       "fix \<equiv> \<Lambda> F. Ifix F"

  admw_def:      "admw P \<equiv> \<forall>F. (\<forall>n. P (iterate n F \<bottom>)) \<longrightarrow>
                            P (\<Squnion>i. iterate i F \<bottom>)" 

subsection {* Binder syntax for @{term fix} *}

syntax
  "@FIX" :: "('a => 'a) => 'a"  (binder "FIX " 10)
  "@FIXP" :: "[patterns, 'a] => 'a"  ("(3FIX <_>./ _)" [0, 10] 10)

syntax (xsymbols)
  "FIX " :: "[idt, 'a] => 'a"  ("(3\<mu>_./ _)" [0, 10] 10)
  "@FIXP" :: "[patterns, 'a] => 'a"  ("(3\<mu>()<_>./ _)" [0, 10] 10)

translations
  "FIX x. LAM y. t" == "fix\<cdot>(LAM x y. t)"
  "FIX x. t" == "fix\<cdot>(LAM x. t)"
  "FIX <xs>. t" == "fix\<cdot>(LAM <xs>. t)"

subsection {* Properties of @{term iterate} and @{term fix} *}

text {* derive inductive properties of iterate from primitive recursion *}

lemma iterate_Suc2: "iterate (Suc n) F x = iterate n F (F\<cdot>x)"
by (induct_tac n, auto)

text {*
  The sequence of function iterations is a chain.
  This property is essential since monotonicity of iterate makes no sense.
*}

lemma chain_iterate2: "x \<sqsubseteq> F\<cdot>x \<Longrightarrow> chain (\<lambda>i. iterate i F x)"
by (rule chainI, induct_tac i, auto elim: monofun_cfun_arg)

lemma chain_iterate: "chain (\<lambda>i. iterate i F \<bottom>)"
by (rule chain_iterate2 [OF minimal])

text {*
  Kleene's fixed point theorems for continuous functions in pointed
  omega cpo's
*}

lemma Ifix_eq: "Ifix F = F\<cdot>(Ifix F)"
apply (unfold Ifix_def)
apply (subst lub_range_shift [of _ 1, symmetric])
apply (rule chain_iterate)
apply (subst contlub_cfun_arg)
apply (rule chain_iterate)
apply simp
done

lemma Ifix_least: "F\<cdot>x = x \<Longrightarrow> Ifix F \<sqsubseteq> x"
apply (unfold Ifix_def)
apply (rule is_lub_thelub)
apply (rule chain_iterate)
apply (rule ub_rangeI)
apply (induct_tac i)
apply simp
apply simp
apply (erule subst)
apply (erule monofun_cfun_arg)
done

text {* continuity of @{term iterate} *}

lemma cont_iterate1: "cont (\<lambda>F. iterate n F x)"
by (induct_tac n, simp_all)

lemma cont_iterate2: "cont (\<lambda>x. iterate n F x)"
by (induct_tac n, simp_all)

lemma cont_iterate: "cont (iterate n)"
by (rule cont_iterate1 [THEN cont2cont_lambda])

lemmas monofun_iterate2 = cont_iterate2 [THEN cont2mono, standard]
lemmas contlub_iterate2 = cont_iterate2 [THEN cont2contlub, standard]

text {* continuity of @{term Ifix} *}

lemma cont_Ifix: "cont Ifix"
apply (unfold Ifix_def)
apply (rule cont2cont_lub)
apply (rule ch2ch_fun_rev)
apply (rule chain_iterate)
apply (rule cont_iterate1)
done

text {* propagate properties of @{term Ifix} to its continuous counterpart *}

lemma fix_eq: "fix\<cdot>F = F\<cdot>(fix\<cdot>F)"
apply (unfold fix_def)
apply (simp add: cont_Ifix)
apply (rule Ifix_eq)
done

lemma fix_least: "F\<cdot>x = x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
apply (unfold fix_def)
apply (simp add: cont_Ifix)
apply (erule Ifix_least)
done

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

text {* direct connection between @{term fix} and iteration without @{term Ifix} *}

lemma fix_def2: "fix\<cdot>F = (\<Squnion>i. iterate i F \<bottom>)"
apply (unfold fix_def)
apply (simp add: cont_Ifix)
apply (simp add: Ifix_def)
done

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
by (rule fix_eq [THEN trans], simp)

subsection {* Admissibility and fixed point induction *}

text {* an admissible formula is also weak admissible *}

lemma adm_impl_admw: "adm P \<Longrightarrow> admw P"
apply (unfold admw_def)
apply (intro strip)
apply (erule admD)
apply (rule chain_iterate)
apply assumption
done

text {* some lemmata for functions with flat/chfin domain/range types *}

lemma adm_chfindom: "adm (\<lambda>(u::'a::cpo \<rightarrow> 'b::chfin). P(u\<cdot>s))"
apply (unfold adm_def)
apply (intro strip)
apply (drule chfin_Rep_CFunR)
apply (erule_tac x = "s" in allE)
apply clarsimp
done

(* adm_flat not needed any more, since it is a special case of adm_chfindom *)

text {* fixed point induction *}

lemma fix_ind: "\<lbrakk>adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (fix\<cdot>F)"
apply (subst fix_def2)
apply (erule admD)
apply (rule chain_iterate)
apply (rule allI)
apply (induct_tac "i")
apply simp
apply simp
done

lemma def_fix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P f"
apply simp
apply (erule fix_ind)
apply assumption
apply fast
done

text {* computational induction for weak admissible formulae *}

lemma wfix_ind: "\<lbrakk>admw P; \<forall>n. P (iterate n F UU)\<rbrakk> \<Longrightarrow> P (fix\<cdot>F)"
by (simp add: fix_def2 admw_def)

lemma def_wfix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>F; admw P; \<forall>n. P (iterate n F \<bottom>)\<rbrakk> \<Longrightarrow> P f"
by (simp, rule wfix_ind)

end
