(*  Title:      HOLCF/Lift.thy
    Author:     Olaf Mueller
*)

header {* Lifting types of class type to flat pcpo's *}

theory Lift
imports Discrete Up Countable
begin

default_sort type

pcpodef 'a lift = "UNIV :: 'a discr u set"
by simp_all

instance lift :: (finite) finite_po
by (rule typedef_finite_po [OF type_definition_lift])

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
  by (erule lift_induct) (simp_all add: Def_def Abs_lift_inject lift_def inst_lift_pcpo)

lemmas lift_distinct1 = lift.distinct(1)
lemmas lift_distinct2 = lift.distinct(2)
lemmas Def_not_UU = lift.distinct(2)
lemmas Def_inject = lift.inject


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
  For @{term "x ~= UU"} in assumptions @{text defined} replaces @{text
  x} by @{text "Def a"} in conclusion. *}

method_setup defined = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (etac @{thm lift_definedE} THEN' asm_simp_tac (simpset_of ctxt)))
*} ""

lemma DefE: "Def x = \<bottom> \<Longrightarrow> R"
  by simp

lemma DefE2: "\<lbrakk>x = Def s; x = \<bottom>\<rbrakk> \<Longrightarrow> R"
  by simp

lemma Def_below_Def: "Def x \<sqsubseteq> Def y \<longleftrightarrow> x = y"
by (simp add: below_lift_def Def_def Abs_lift_inverse lift_def)

lemma Def_below_iff [simp]: "Def x \<sqsubseteq> y \<longleftrightarrow> Def x = y"
by (induct y, simp, simp add: Def_below_Def)


subsection {* Lift is flat *}

instance lift :: (type) flat
proof
  fix x y :: "'a lift"
  assume "x \<sqsubseteq> y" thus "x = \<bottom> \<or> x = y"
    by (induct x) auto
qed

text {*
  \medskip Two specific lemmas for the combination of LCF and HOL
  terms.
*}

lemma cont_Rep_CFun_app [simp]: "\<lbrakk>cont g; cont f\<rbrakk> \<Longrightarrow> cont(\<lambda>x. ((f x)\<cdot>(g x)) s)"
by (rule cont2cont_Rep_CFun [THEN cont2cont_fun])

lemma cont_Rep_CFun_app_app [simp]: "\<lbrakk>cont g; cont f\<rbrakk> \<Longrightarrow> cont(\<lambda>x. ((f x)\<cdot>(g x)) s t)"
by (rule cont_Rep_CFun_app [THEN cont2cont_fun])

subsection {* Further operations *}

definition
  flift1 :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a lift \<rightarrow> 'b)"  (binder "FLIFT " 10)  where
  "flift1 = (\<lambda>f. (\<Lambda> x. lift_case \<bottom> f x))"

definition
  flift2 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lift \<rightarrow> 'b lift)" where
  "flift2 f = (FLIFT x. Def (f x))"

subsection {* Continuity Proofs for flift1, flift2 *}

text {* Need the instance of @{text flat}. *}

lemma cont_lift_case1: "cont (\<lambda>f. lift_case a f x)"
apply (induct x)
apply simp
apply simp
apply (rule cont_id [THEN cont2cont_fun])
done

lemma cont_lift_case2: "cont (\<lambda>x. lift_case \<bottom> f x)"
apply (rule flatdom_strict2cont)
apply simp
done

lemma cont_flift1: "cont flift1"
unfolding flift1_def
apply (rule cont2cont_LAM)
apply (rule cont_lift_case2)
apply (rule cont_lift_case1)
done

lemma FLIFT_mono:
  "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> (FLIFT x. f x) \<sqsubseteq> (FLIFT x. g x)"
apply (rule monofunE [where f=flift1])
apply (rule cont2mono [OF cont_flift1])
apply (simp add: below_fun_ext)
done

lemma cont2cont_flift1 [simp, cont2cont]:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y)\<rbrakk> \<Longrightarrow> cont (\<lambda>x. FLIFT y. f x y)"
apply (rule cont_flift1 [THEN cont2cont_app3])
apply simp
done

lemma cont2cont_lift_case [simp]:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y); cont g\<rbrakk> \<Longrightarrow> cont (\<lambda>x. lift_case UU (f x) (g x))"
apply (subgoal_tac "cont (\<lambda>x. (FLIFT y. f x y)\<cdot>(g x))")
apply (simp add: flift1_def cont_lift_case2)
apply simp
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

lemma flift2_defined_iff [simp]: "(flift2 f\<cdot>x = \<bottom>) = (x = \<bottom>)"
by (cases x, simp_all)


subsection {* Lifted countable types are SFP domains *}

definition
  lift_approx :: "nat \<Rightarrow> 'a::countable lift \<rightarrow> 'a lift"
where
  "lift_approx = (\<lambda>i. FLIFT x. if to_nat x < i then Def x else \<bottom>)"

lemma chain_lift_approx [simp]: "chain lift_approx"
  unfolding lift_approx_def
  by (rule chainI, simp add: FLIFT_mono)

lemma lub_lift_approx [simp]: "(\<Squnion>i. lift_approx i) = ID"
apply (rule ext_cfun)
apply (simp add: contlub_cfun_fun)
apply (simp add: lift_approx_def)
apply (case_tac x, simp)
apply (rule thelubI)
apply (rule is_lubI)
apply (rule ub_rangeI, simp)
apply (drule ub_rangeD)
apply (erule rev_below_trans)
apply simp
apply (rule lessI)
done

lemma finite_deflation_lift_approx: "finite_deflation (lift_approx i)"
proof
  fix x
  show "lift_approx i\<cdot>x \<sqsubseteq> x"
    unfolding lift_approx_def
    by (cases x, simp, simp)
  show "lift_approx i\<cdot>(lift_approx i\<cdot>x) = lift_approx i\<cdot>x"
    unfolding lift_approx_def
    by (cases x, simp, simp)
  show "finite {x::'a lift. lift_approx i\<cdot>x = x}"
  proof (rule finite_subset)
    let ?S = "insert (\<bottom>::'a lift) (Def ` to_nat -` {..<i})"
    show "{x::'a lift. lift_approx i\<cdot>x = x} \<subseteq> ?S"
      unfolding lift_approx_def
      by (rule subsetI, case_tac x, simp, simp split: split_if_asm)
    show "finite ?S"
      by (simp add: finite_vimageI)
  qed
qed

lemma lift_approx: "approx_chain lift_approx"
using chain_lift_approx lub_lift_approx finite_deflation_lift_approx
by (rule approx_chain.intro)

instantiation lift :: (countable) sfp
begin

definition
  "emb = udom_emb lift_approx"

definition
  "prj = udom_prj lift_approx"

definition
  "sfp (t::'a lift itself) =
    (\<Squnion>i. sfp_principal (Abs_fin_defl (emb oo lift_approx i oo prj)))"

instance proof
  show ep: "ep_pair emb (prj :: udom \<rightarrow> 'a lift)"
    unfolding emb_lift_def prj_lift_def
    by (rule ep_pair_udom [OF lift_approx])
  show "cast\<cdot>SFP('a lift) = emb oo (prj :: udom \<rightarrow> 'a lift)"
    unfolding sfp_lift_def
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule sfp.principal_mono)
    apply (simp add: below_fin_defl_def)
    apply (simp add: Abs_fin_defl_inverse finite_deflation_lift_approx
                     ep_pair.finite_deflation_e_d_p [OF ep])
    apply (intro monofun_cfun below_refl)
    apply (rule chainE)
    apply (rule chain_lift_approx)
    apply (subst cast_sfp_principal)
    apply (simp add: Abs_fin_defl_inverse finite_deflation_lift_approx
                     ep_pair.finite_deflation_e_d_p [OF ep] lub_distribs)
    done
qed

end

end
