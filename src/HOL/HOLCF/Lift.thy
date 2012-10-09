(*  Title:      HOL/HOLCF/Lift.thy
    Author:     Olaf Mueller
*)

header {* Lifting types of class type to flat pcpo's *}

theory Lift
imports Discrete Up
begin

default_sort type

pcpodef 'a lift = "UNIV :: 'a discr u set"
by simp_all

lemmas inst_lift_pcpo = Abs_lift_strict [symmetric]

definition
  Def :: "'a \<Rightarrow> 'a lift" where
  "Def x = Abs_lift (up\<cdot>(Discr x))"

subsection {* Lift as a datatype *}

lemma lift_induct: "\<lbrakk>P \<bottom>; \<And>x. P (Def x)\<rbrakk> \<Longrightarrow> P y"
apply (induct y)
apply (rule_tac p=y in upE)
apply (simp add: Abs_lift_strict)
apply (case_tac x)
apply (simp add: Def_def)
done

rep_datatype "\<bottom>\<Colon>'a lift" Def
  by (erule lift_induct) (simp_all add: Def_def Abs_lift_inject inst_lift_pcpo)

text {* @{term bottom} and @{term Def} *}

lemma not_Undef_is_Def: "(x \<noteq> \<bottom>) = (\<exists>y. x = Def y)"
  by (cases x) simp_all

lemma lift_definedE: "\<lbrakk>x \<noteq> \<bottom>; \<And>a. x = Def a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (cases x) simp_all

text {*
  For @{term "x ~= \<bottom>"} in assumptions @{text defined} replaces @{text
  x} by @{text "Def a"} in conclusion. *}

method_setup defined = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (etac @{thm lift_definedE} THEN' asm_simp_tac (simpset_of ctxt)))
*}

lemma DefE: "Def x = \<bottom> \<Longrightarrow> R"
  by simp

lemma DefE2: "\<lbrakk>x = Def s; x = \<bottom>\<rbrakk> \<Longrightarrow> R"
  by simp

lemma Def_below_Def: "Def x \<sqsubseteq> Def y \<longleftrightarrow> x = y"
by (simp add: below_lift_def Def_def Abs_lift_inverse)

lemma Def_below_iff [simp]: "Def x \<sqsubseteq> y \<longleftrightarrow> Def x = y"
by (induct y, simp, simp add: Def_below_Def)


subsection {* Lift is flat *}

instance lift :: (type) flat
proof
  fix x y :: "'a lift"
  assume "x \<sqsubseteq> y" thus "x = \<bottom> \<or> x = y"
    by (induct x) auto
qed

subsection {* Continuity of @{const lift_case} *}

lemma lift_case_eq: "lift_case \<bottom> f x = fup\<cdot>(\<Lambda> y. f (undiscr y))\<cdot>(Rep_lift x)"
apply (induct x, unfold lift.cases)
apply (simp add: Rep_lift_strict)
apply (simp add: Def_def Abs_lift_inverse)
done

lemma cont2cont_lift_case [simp]:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y); cont g\<rbrakk> \<Longrightarrow> cont (\<lambda>x. lift_case \<bottom> (f x) (g x))"
unfolding lift_case_eq by (simp add: cont_Rep_lift)

subsection {* Further operations *}

definition
  flift1 :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a lift \<rightarrow> 'b)"  (binder "FLIFT " 10)  where
  "flift1 = (\<lambda>f. (\<Lambda> x. lift_case \<bottom> f x))"

translations
  "\<Lambda>(XCONST Def x). t" => "CONST flift1 (\<lambda>x. t)"
  "\<Lambda>(CONST Def x). FLIFT y. t" <= "FLIFT x y. t"
  "\<Lambda>(CONST Def x). t" <= "FLIFT x. t"

definition
  flift2 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lift \<rightarrow> 'b lift)" where
  "flift2 f = (FLIFT x. Def (f x))"

lemma flift1_Def [simp]: "flift1 f\<cdot>(Def x) = (f x)"
by (simp add: flift1_def)

lemma flift2_Def [simp]: "flift2 f\<cdot>(Def x) = Def (f x)"
by (simp add: flift2_def)

lemma flift1_strict [simp]: "flift1 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift1_def)

lemma flift2_strict [simp]: "flift2 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift2_def)

lemma flift2_defined [simp]: "x \<noteq> \<bottom> \<Longrightarrow> (flift2 f)\<cdot>x \<noteq> \<bottom>"
by (erule lift_definedE, simp)

lemma flift2_bottom_iff [simp]: "(flift2 f\<cdot>x = \<bottom>) = (x = \<bottom>)"
by (cases x, simp_all)

lemma FLIFT_mono:
  "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> (FLIFT x. f x) \<sqsubseteq> (FLIFT x. g x)"
by (rule cfun_belowI, case_tac x, simp_all)

lemma cont2cont_flift1 [simp, cont2cont]:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y)\<rbrakk> \<Longrightarrow> cont (\<lambda>x. FLIFT y. f x y)"
by (simp add: flift1_def cont2cont_LAM)

end
