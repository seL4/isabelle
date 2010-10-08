(*  Title:      HOLCF/Representable.thy
    Author:     Brian Huffman
*)

header {* Representable Types *}

theory Representable
imports Algebraic Universal Ssum One Fixrec Domain_Aux
uses
  ("Tools/repdef.ML")
  ("Tools/Domain/domain_isomorphism.ML")
begin

default_sort bifinite

subsection {* Representations of types *}

lemma emb_prj: "emb\<cdot>((prj\<cdot>x)::'a) = cast\<cdot>SFP('a)\<cdot>x"
by (simp add: cast_SFP)

lemma in_SFP_iff:
  "x ::: SFP('a) \<longleftrightarrow> emb\<cdot>((prj\<cdot>x)::'a) = x"
by (simp add: in_sfp_def cast_SFP)

lemma prj_inverse:
  "x ::: SFP('a) \<Longrightarrow> emb\<cdot>((prj\<cdot>x)::'a) = x"
by (simp only: in_SFP_iff)

lemma emb_in_SFP [simp]:
  "emb\<cdot>(x::'a) ::: SFP('a)"
by (simp add: in_SFP_iff)

subsection {* Coerce operator *}

definition coerce :: "'a \<rightarrow> 'b"
where "coerce = prj oo emb"

lemma beta_coerce: "coerce\<cdot>x = prj\<cdot>(emb\<cdot>x)"
by (simp add: coerce_def)

lemma prj_emb: "prj\<cdot>(emb\<cdot>x) = coerce\<cdot>x"
by (simp add: coerce_def)

lemma coerce_strict [simp]: "coerce\<cdot>\<bottom> = \<bottom>"
by (simp add: coerce_def)

lemma coerce_eq_ID [simp]: "(coerce :: 'a \<rightarrow> 'a) = ID"
by (rule ext_cfun, simp add: beta_coerce)

lemma emb_coerce:
  "SFP('a) \<sqsubseteq> SFP('b)
   \<Longrightarrow> emb\<cdot>((coerce::'a \<rightarrow> 'b)\<cdot>x) = emb\<cdot>x"
 apply (simp add: beta_coerce)
 apply (rule prj_inverse)
 apply (erule sfp_belowD)
 apply (rule emb_in_SFP)
done

lemma coerce_prj:
  "SFP('a) \<sqsubseteq> SFP('b)
   \<Longrightarrow> (coerce::'b \<rightarrow> 'a)\<cdot>(prj\<cdot>x) = prj\<cdot>x"
 apply (simp add: coerce_def)
 apply (rule emb_eq_iff [THEN iffD1])
 apply (simp only: emb_prj)
 apply (rule deflation_below_comp1)
   apply (rule deflation_cast)
  apply (rule deflation_cast)
 apply (erule monofun_cfun_arg)
done

lemma coerce_coerce [simp]:
  "SFP('a) \<sqsubseteq> SFP('b)
   \<Longrightarrow> coerce\<cdot>((coerce::'a \<rightarrow> 'b)\<cdot>x) = coerce\<cdot>x"
by (simp add: beta_coerce prj_inverse sfp_belowD)

lemma coerce_inverse:
  "emb\<cdot>(x::'a) ::: SFP('b) \<Longrightarrow> coerce\<cdot>(coerce\<cdot>x :: 'b) = x"
by (simp only: beta_coerce prj_inverse emb_inverse)

lemma coerce_type:
  "SFP('a) \<sqsubseteq> SFP('b)
   \<Longrightarrow> emb\<cdot>((coerce::'a \<rightarrow> 'b)\<cdot>x) ::: SFP('a)"
by (simp add: beta_coerce prj_inverse sfp_belowD)

lemma ep_pair_coerce:
  "SFP('a) \<sqsubseteq> SFP('b)
   \<Longrightarrow> ep_pair (coerce::'a \<rightarrow> 'b) (coerce::'b \<rightarrow> 'a)"
 apply (rule ep_pair.intro)
  apply simp
 apply (simp only: beta_coerce)
 apply (rule below_trans)
  apply (rule monofun_cfun_arg)
  apply (rule emb_prj_below)
 apply simp
done

text {* Isomorphism lemmas used internally by the domain package: *}

lemma domain_abs_iso:
  fixes abs and rep
  assumes SFP: "SFP('b) = SFP('a)"
  assumes abs_def: "abs \<equiv> (coerce :: 'a \<rightarrow> 'b)"
  assumes rep_def: "rep \<equiv> (coerce :: 'b \<rightarrow> 'a)"
  shows "rep\<cdot>(abs\<cdot>x) = x"
unfolding abs_def rep_def by (simp add: SFP)

lemma domain_rep_iso:
  fixes abs and rep
  assumes SFP: "SFP('b) = SFP('a)"
  assumes abs_def: "abs \<equiv> (coerce :: 'a \<rightarrow> 'b)"
  assumes rep_def: "rep \<equiv> (coerce :: 'b \<rightarrow> 'a)"
  shows "abs\<cdot>(rep\<cdot>x) = x"
unfolding abs_def rep_def by (simp add: SFP [symmetric])


subsection {* Proving a subtype is representable *}

text {*
  Temporarily relax type constraints for @{term emb}, and @{term prj}.
*}

setup {* Sign.add_const_constraint
  (@{const_name sfp}, SOME @{typ "'a::pcpo itself \<Rightarrow> sfp"}) *}

setup {* Sign.add_const_constraint
  (@{const_name emb}, SOME @{typ "'a::pcpo \<rightarrow> udom"}) *}

setup {* Sign.add_const_constraint
  (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::pcpo"}) *}

lemma typedef_rep_class:
  fixes Rep :: "'a::pcpo \<Rightarrow> udom"
  fixes Abs :: "udom \<Rightarrow> 'a::pcpo"
  fixes t :: sfp
  assumes type: "type_definition Rep Abs {x. x ::: t}"
  assumes below: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  assumes emb: "emb \<equiv> (\<Lambda> x. Rep x)"
  assumes prj: "prj \<equiv> (\<Lambda> x. Abs (cast\<cdot>t\<cdot>x))"
  assumes sfp: "sfp \<equiv> (\<lambda> a::'a itself. t)"
  shows "OFCLASS('a, bifinite_class)"
proof
  have adm: "adm (\<lambda>x. x \<in> {x. x ::: t})"
    by (simp add: adm_in_sfp)
  have emb_beta: "\<And>x. emb\<cdot>x = Rep x"
    unfolding emb
    apply (rule beta_cfun)
    apply (rule typedef_cont_Rep [OF type below adm])
    done
  have prj_beta: "\<And>y. prj\<cdot>y = Abs (cast\<cdot>t\<cdot>y)"
    unfolding prj
    apply (rule beta_cfun)
    apply (rule typedef_cont_Abs [OF type below adm])
    apply simp_all
    done
  have emb_in_sfp: "\<And>x::'a. emb\<cdot>x ::: t"
    using type_definition.Rep [OF type]
    by (simp add: emb_beta)
  have prj_emb: "\<And>x::'a. prj\<cdot>(emb\<cdot>x) = x"
    unfolding prj_beta
    apply (simp add: cast_fixed [OF emb_in_sfp])
    apply (simp add: emb_beta type_definition.Rep_inverse [OF type])
    done
  have emb_prj: "\<And>y. emb\<cdot>(prj\<cdot>y :: 'a) = cast\<cdot>t\<cdot>y"
    unfolding prj_beta emb_beta
    by (simp add: type_definition.Abs_inverse [OF type])
  show "ep_pair (emb :: 'a \<rightarrow> udom) prj"
    apply default
    apply (simp add: prj_emb)
    apply (simp add: emb_prj cast.below)
    done
  show "cast\<cdot>SFP('a) = emb oo (prj :: udom \<rightarrow> 'a)"
    by (rule ext_cfun, simp add: sfp emb_prj)
qed

lemma typedef_SFP:
  assumes "sfp \<equiv> (\<lambda>a::'a::pcpo itself. t)"
  shows "SFP('a::pcpo) = t"
unfolding assms ..

text {* Restore original typing constraints *}

setup {* Sign.add_const_constraint
  (@{const_name sfp}, SOME @{typ "'a::bifinite itself \<Rightarrow> sfp"}) *}

setup {* Sign.add_const_constraint
  (@{const_name emb}, SOME @{typ "'a::bifinite \<rightarrow> udom"}) *}

setup {* Sign.add_const_constraint
  (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::bifinite"}) *}

lemma adm_mem_Collect_in_sfp: "adm (\<lambda>x. x \<in> {x. x ::: A})"
unfolding mem_Collect_eq by (rule adm_in_sfp)

use "Tools/repdef.ML"

subsection {* Isomorphic deflations *}

definition
  isodefl :: "('a \<rightarrow> 'a) \<Rightarrow> sfp \<Rightarrow> bool"
where
  "isodefl d t \<longleftrightarrow> cast\<cdot>t = emb oo d oo prj"

lemma isodeflI: "(\<And>x. cast\<cdot>t\<cdot>x = emb\<cdot>(d\<cdot>(prj\<cdot>x))) \<Longrightarrow> isodefl d t"
unfolding isodefl_def by (simp add: ext_cfun)

lemma cast_isodefl: "isodefl d t \<Longrightarrow> cast\<cdot>t = (\<Lambda> x. emb\<cdot>(d\<cdot>(prj\<cdot>x)))"
unfolding isodefl_def by (simp add: ext_cfun)

lemma isodefl_strict: "isodefl d t \<Longrightarrow> d\<cdot>\<bottom> = \<bottom>"
unfolding isodefl_def
by (drule cfun_fun_cong [where x="\<bottom>"], simp)

lemma isodefl_imp_deflation:
  fixes d :: "'a \<rightarrow> 'a"
  assumes "isodefl d t" shows "deflation d"
proof
  note assms [unfolded isodefl_def, simp]
  fix x :: 'a
  show "d\<cdot>(d\<cdot>x) = d\<cdot>x"
    using cast.idem [of t "emb\<cdot>x"] by simp
  show "d\<cdot>x \<sqsubseteq> x"
    using cast.below [of t "emb\<cdot>x"] by simp
qed

lemma isodefl_ID_SFP: "isodefl (ID :: 'a \<rightarrow> 'a) SFP('a)"
unfolding isodefl_def by (simp add: cast_SFP)

lemma isodefl_SFP_imp_ID: "isodefl (d :: 'a \<rightarrow> 'a) SFP('a) \<Longrightarrow> d = ID"
unfolding isodefl_def
apply (simp add: cast_SFP)
apply (simp add: expand_cfun_eq)
apply (rule allI)
apply (drule_tac x="emb\<cdot>x" in spec)
apply simp
done

lemma isodefl_bottom: "isodefl \<bottom> \<bottom>"
unfolding isodefl_def by (simp add: expand_cfun_eq)

lemma adm_isodefl:
  "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. isodefl (f x) (g x))"
unfolding isodefl_def by simp

lemma isodefl_lub:
  assumes "chain d" and "chain t"
  assumes "\<And>i. isodefl (d i) (t i)"
  shows "isodefl (\<Squnion>i. d i) (\<Squnion>i. t i)"
using prems unfolding isodefl_def
by (simp add: contlub_cfun_arg contlub_cfun_fun)

lemma isodefl_fix:
  assumes "\<And>d t. isodefl d t \<Longrightarrow> isodefl (f\<cdot>d) (g\<cdot>t)"
  shows "isodefl (fix\<cdot>f) (fix\<cdot>g)"
unfolding fix_def2
apply (rule isodefl_lub, simp, simp)
apply (induct_tac i)
apply (simp add: isodefl_bottom)
apply (simp add: assms)
done

lemma isodefl_coerce:
  fixes d :: "'a \<rightarrow> 'a"
  assumes SFP: "SFP('b) = SFP('a)"
  shows "isodefl d t \<Longrightarrow> isodefl (coerce oo d oo coerce :: 'b \<rightarrow> 'b) t"
unfolding isodefl_def
apply (simp add: expand_cfun_eq)
apply (simp add: emb_coerce coerce_prj SFP)
done

lemma isodefl_abs_rep:
  fixes abs and rep and d
  assumes SFP: "SFP('b) = SFP('a)"
  assumes abs_def: "abs \<equiv> (coerce :: 'a \<rightarrow> 'b)"
  assumes rep_def: "rep \<equiv> (coerce :: 'b \<rightarrow> 'a)"
  shows "isodefl d t \<Longrightarrow> isodefl (abs oo d oo rep) t"
unfolding abs_def rep_def using SFP by (rule isodefl_coerce)

lemma isodefl_cfun:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (cfun_map\<cdot>d1\<cdot>d2) (cfun_sfp\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_cfun_sfp cast_isodefl)
apply (simp add: emb_cfun_def prj_cfun_def)
apply (simp add: cfun_map_map cfcomp1)
done

lemma isodefl_ssum:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (ssum_map\<cdot>d1\<cdot>d2) (ssum_sfp\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_ssum_sfp cast_isodefl)
apply (simp add: emb_ssum_def prj_ssum_def)
apply (simp add: ssum_map_map isodefl_strict)
done

lemma isodefl_sprod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (sprod_map\<cdot>d1\<cdot>d2) (sprod_sfp\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_sprod_sfp cast_isodefl)
apply (simp add: emb_sprod_def prj_sprod_def)
apply (simp add: sprod_map_map isodefl_strict)
done

lemma isodefl_cprod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (cprod_map\<cdot>d1\<cdot>d2) (prod_sfp\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_prod_sfp cast_isodefl)
apply (simp add: emb_prod_def prj_prod_def)
apply (simp add: cprod_map_map cfcomp1)
done

lemma isodefl_u:
  "isodefl d t \<Longrightarrow> isodefl (u_map\<cdot>d) (u_sfp\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_u_sfp cast_isodefl)
apply (simp add: emb_u_def prj_u_def)
apply (simp add: u_map_map)
done

subsection {* Constructing Domain Isomorphisms *}

use "Tools/Domain/domain_isomorphism.ML"

setup {*
  fold Domain_Isomorphism.add_type_constructor
    [(@{type_name cfun}, @{term cfun_sfp}, @{const_name cfun_map}, @{thm SFP_cfun},
        @{thm isodefl_cfun}, @{thm cfun_map_ID}, @{thm deflation_cfun_map}),

     (@{type_name ssum}, @{term ssum_sfp}, @{const_name ssum_map}, @{thm SFP_ssum},
        @{thm isodefl_ssum}, @{thm ssum_map_ID}, @{thm deflation_ssum_map}),

     (@{type_name sprod}, @{term sprod_sfp}, @{const_name sprod_map}, @{thm SFP_sprod},
        @{thm isodefl_sprod}, @{thm sprod_map_ID}, @{thm deflation_sprod_map}),

     (@{type_name prod}, @{term cprod_sfp}, @{const_name cprod_map}, @{thm SFP_prod},
        @{thm isodefl_cprod}, @{thm cprod_map_ID}, @{thm deflation_cprod_map}),

     (@{type_name "u"}, @{term u_sfp}, @{const_name u_map}, @{thm SFP_u},
        @{thm isodefl_u}, @{thm u_map_ID}, @{thm deflation_u_map})]
*}

end
