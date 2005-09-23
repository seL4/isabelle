(*  Title:      HOLCF/Lift.thy
    ID:         $Id$
    Author:     Olaf Mueller
*)

header {* Lifting types of class type to flat pcpo's *}

theory Lift
imports Discrete Up Cprod
begin

defaultsort type

pcpodef 'a lift = "UNIV :: 'a discr u set"
by simp

lemmas inst_lift_pcpo = Abs_lift_strict [symmetric]

constdefs
  Def :: "'a \<Rightarrow> 'a lift"
  "Def x \<equiv> Abs_lift (up\<cdot>(Discr x))"

subsection {* Lift as a datatype *}

lemma lift_distinct1: "\<bottom> \<noteq> Def x"
by (simp add: Def_def Abs_lift_inject lift_def inst_lift_pcpo)

lemma lift_distinct2: "Def x \<noteq> \<bottom>"
by (simp add: Def_def Abs_lift_inject lift_def inst_lift_pcpo)

lemma Def_inject: "(Def x = Def y) = (x = y)"
by (simp add: Def_def Abs_lift_inject lift_def)

lemma lift_induct: "\<lbrakk>P \<bottom>; \<And>x. P (Def x)\<rbrakk> \<Longrightarrow> P y"
apply (induct y)
apply (rule_tac p=y in upE)
apply (simp add: Abs_lift_strict)
apply (case_tac x)
apply (simp add: Def_def)
done

rep_datatype lift
  distinct lift_distinct1 lift_distinct2
  inject Def_inject
  induction lift_induct

lemma Def_not_UU: "Def a \<noteq> UU"
  by simp


text {* @{term UU} and @{term Def} *}

lemma Lift_exhaust: "x = \<bottom> \<or> (\<exists>y. x = Def y)"
  by (induct x) simp_all

lemma Lift_cases: "\<lbrakk>x = \<bottom> \<Longrightarrow> P; \<exists>a. x = Def a \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (insert Lift_exhaust) blast

lemma not_Undef_is_Def: "(x \<noteq> \<bottom>) = (\<exists>y. x = Def y)"
  by (cases x) simp_all

lemma lift_definedE: "\<lbrakk>x \<noteq> \<bottom>; \<And>a. x = Def a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (cases x) simp_all

text {*
  For @{term "x ~= UU"} in assumptions @{text def_tac} replaces @{text
  x} by @{text "Def a"} in conclusion. *}

ML {*
  local val lift_definedE = thm "lift_definedE"
  in val def_tac = SIMPSET' (fn ss =>
    etac lift_definedE THEN' asm_simp_tac ss)
  end;
*}

lemma DefE: "Def x = \<bottom> \<Longrightarrow> R"
  by simp

lemma DefE2: "\<lbrakk>x = Def s; x = \<bottom>\<rbrakk> \<Longrightarrow> R"
  by simp

lemma Def_inject_less_eq: "Def x \<sqsubseteq> Def y = (x = y)"
by (simp add: less_lift_def Def_def Abs_lift_inverse lift_def)

lemma Def_less_is_eq [simp]: "Def x \<sqsubseteq> y = (Def x = y)"
apply (induct y)
apply (simp add: eq_UU_iff)
apply (simp add: Def_inject_less_eq)
done


subsection {* Lift is flat *}

lemma less_lift: "(x::'a lift) \<sqsubseteq> y = (x = y \<or> x = \<bottom>)"
by (induct x, simp_all)

instance lift :: (type) flat
by (intro_classes, simp add: less_lift)

text {*
  \medskip Two specific lemmas for the combination of LCF and HOL
  terms.
*}

lemma cont_Rep_CFun_app: "\<lbrakk>cont g; cont f\<rbrakk> \<Longrightarrow> cont(\<lambda>x. ((f x)\<cdot>(g x)) s)"
by (rule cont2cont_Rep_CFun [THEN cont2cont_CF1L])

lemma cont_Rep_CFun_app_app: "\<lbrakk>cont g; cont f\<rbrakk> \<Longrightarrow> cont(\<lambda>x. ((f x)\<cdot>(g x)) s t)"
by (rule cont_Rep_CFun_app [THEN cont2cont_CF1L])

subsection {* Further operations *}

constdefs
  flift1 :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a lift \<rightarrow> 'b)" (binder "FLIFT " 10)
  "flift1 \<equiv> \<lambda>f. (\<Lambda> x. lift_case \<bottom> f x)"

  flift2 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lift \<rightarrow> 'b lift)"
  "flift2 f \<equiv> FLIFT x. Def (f x)"

  liftpair :: "'a lift \<times> 'b lift \<Rightarrow> ('a \<times> 'b) lift"
  "liftpair x \<equiv> csplit\<cdot>(FLIFT x y. Def (x, y))\<cdot>x"

subsection {* Continuity Proofs for flift1, flift2 *}

text {* Need the instance of @{text flat}. *}

lemma cont_lift_case1: "cont (\<lambda>f. lift_case a f x)"
apply (induct x)
apply simp
apply simp
apply (rule cont_id [THEN cont2cont_CF1L])
done

lemma cont_lift_case2: "cont (\<lambda>x. lift_case \<bottom> f x)"
apply (rule flatdom_strict2cont)
apply simp
done

lemma cont_flift1: "cont flift1"
apply (unfold flift1_def)
apply (rule cont2cont_LAM)
apply (rule cont_lift_case2)
apply (rule cont_lift_case1)
done

lemma cont2cont_flift1:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y)\<rbrakk> \<Longrightarrow> cont (\<lambda>x. FLIFT y. f x y)"
apply (rule cont_flift1 [THEN cont2cont_app3])
apply (simp add: cont2cont_lambda)
done

lemma cont2cont_lift_case:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y); cont g\<rbrakk> \<Longrightarrow> cont (\<lambda>x. lift_case UU (f x) (g x))"
apply (subgoal_tac "cont (\<lambda>x. (FLIFT y. f x y)\<cdot>(g x))")
apply (simp add: flift1_def cont_lift_case2)
apply (simp add: cont2cont_flift1)
done

text {* rewrites for @{term flift1}, @{term flift2} *}

lemma flift1_Def [simp]: "flift1 f\<cdot>(Def x) = (f x)"
by (simp add: flift1_def cont_lift_case2)

lemma flift2_Def [simp]: "flift2 f\<cdot>(Def x) = Def (f x)"
by (simp add: flift2_def)

lemma flift1_strict [simp]: "flift1 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift1_def cont_lift_case2)

lemma flift2_strict [simp]: "flift2 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift2_def)

lemma flift2_defined [simp]: "x \<noteq> \<bottom> \<Longrightarrow> (flift2 f)\<cdot>x \<noteq> \<bottom>"
by (erule lift_definedE, simp)

text {*
  \medskip Extension of @{text cont_tac} and installation of simplifier.
*}

lemmas cont_lemmas_ext [simp] =
  cont2cont_flift1 cont2cont_lift_case cont2cont_lambda
  cont_Rep_CFun_app cont_Rep_CFun_app_app cont_if

ML {*
val cont_lemmas2 = cont_lemmas1 @ thms "cont_lemmas_ext";

fun cont_tac  i = resolve_tac cont_lemmas2 i;
fun cont_tacR i = REPEAT (cont_tac i);

local val flift1_def = thm "flift1_def"
in fun cont_tacRs ss i =
  simp_tac ss i THEN
  REPEAT (cont_tac i)
end;
*}

end
