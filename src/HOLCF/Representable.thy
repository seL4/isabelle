(*  Title:      HOLCF/Representable.thy
    Author:     Brian Huffman
*)

header {* Representable Types *}

theory Representable
imports Algebraic Universal Ssum Sprod One ConvexPD
uses ("Tools/repdef.ML")
begin

subsection {* Class of representable types *}

text "Overloaded embedding and projection functions between
      a representable type and the universal domain."

class rep = bifinite +
  fixes emb :: "'a::pcpo \<rightarrow> udom"
  fixes prj :: "udom \<rightarrow> 'a::pcpo"
  assumes ep_pair_emb_prj: "ep_pair emb prj"

interpretation rep!:
  pcpo_ep_pair
    "emb :: 'a::rep \<rightarrow> udom"
    "prj :: udom \<rightarrow> 'a::rep"
  unfolding pcpo_ep_pair_def
  by (rule ep_pair_emb_prj)

lemmas emb_inverse = rep.e_inverse
lemmas emb_prj_below = rep.e_p_below
lemmas emb_eq_iff = rep.e_eq_iff
lemmas emb_strict = rep.e_strict
lemmas prj_strict = rep.p_strict


subsection {* Making @{term rep} the default class *}

text {*
  From now on, free type variables are assumed to be in class
  @{term rep}, unless specified otherwise.
*}

defaultsort rep

subsection {* Representations of types *}

text "A TypeRep is an algebraic deflation over the universe of values."

types TypeRep = "udom alg_defl"
translations "TypeRep" \<leftharpoondown> (type) "udom alg_defl"

definition
  Rep_of :: "'a::rep itself \<Rightarrow> TypeRep"
where
  "Rep_of TYPE('a::rep) =
    (\<Squnion>i. alg_defl_principal (Abs_fin_defl
      (emb oo (approx i :: 'a \<rightarrow> 'a) oo prj)))"

syntax "_REP" :: "type \<Rightarrow> TypeRep"  ("(1REP/(1'(_')))")
translations "REP(t)" \<rightleftharpoons> "CONST Rep_of TYPE(t)"

lemma cast_REP:
  "cast\<cdot>REP('a::rep) = (emb::'a \<rightarrow> udom) oo (prj::udom \<rightarrow> 'a)"
proof -
  let ?a = "\<lambda>i. emb oo approx i oo (prj::udom \<rightarrow> 'a)"
  have a: "\<And>i. finite_deflation (?a i)"
    apply (rule rep.finite_deflation_e_d_p)
    apply (rule finite_deflation_approx)
    done
  show ?thesis
    unfolding Rep_of_def
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule alg_defl.principal_mono)
    apply (rule Abs_fin_defl_mono [OF a a])
    apply (rule chainE, simp)
    apply (subst cast_alg_defl_principal)
    apply (simp add: Abs_fin_defl_inverse a)
    apply (simp add: expand_cfun_eq lub_distribs)
    done
qed

lemma emb_prj: "emb\<cdot>((prj\<cdot>x)::'a::rep) = cast\<cdot>REP('a)\<cdot>x"
by (simp add: cast_REP)

lemma in_REP_iff:
  "x ::: REP('a::rep) \<longleftrightarrow> emb\<cdot>((prj\<cdot>x)::'a) = x"
by (simp add: in_deflation_def cast_REP)

lemma prj_inverse:
  "x ::: REP('a::rep) \<Longrightarrow> emb\<cdot>((prj\<cdot>x)::'a) = x"
by (simp only: in_REP_iff)

lemma emb_in_REP [simp]:
  "emb\<cdot>(x::'a::rep) ::: REP('a)"
by (simp add: in_REP_iff)

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
  "REP('a) \<sqsubseteq> REP('b)
   \<Longrightarrow> emb\<cdot>((coerce::'a \<rightarrow> 'b)\<cdot>x) = emb\<cdot>x"
 apply (simp add: beta_coerce)
 apply (rule prj_inverse)
 apply (erule subdeflationD)
 apply (rule emb_in_REP)
done

lemma coerce_prj:
  "REP('a) \<sqsubseteq> REP('b)
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
  "REP('a) \<sqsubseteq> REP('b)
   \<Longrightarrow> coerce\<cdot>((coerce::'a \<rightarrow> 'b)\<cdot>x) = coerce\<cdot>x"
by (simp add: beta_coerce prj_inverse subdeflationD)

lemma coerce_inverse:
  "emb\<cdot>(x::'a) ::: REP('b) \<Longrightarrow> coerce\<cdot>(coerce\<cdot>x :: 'b) = x"
by (simp only: beta_coerce prj_inverse emb_inverse)

lemma coerce_type:
  "REP('a) \<sqsubseteq> REP('b)
   \<Longrightarrow> emb\<cdot>((coerce::'a \<rightarrow> 'b)\<cdot>x) ::: REP('a)"
by (simp add: beta_coerce prj_inverse subdeflationD)

lemma ep_pair_coerce:
  "REP('a) \<sqsubseteq> REP('b)
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
  assumes REP: "REP('b) = REP('a)"
  assumes abs_def: "abs \<equiv> (coerce :: 'a \<rightarrow> 'b)"
  assumes rep_def: "rep \<equiv> (coerce :: 'b \<rightarrow> 'a)"
  shows "rep\<cdot>(abs\<cdot>x) = x"
unfolding abs_def rep_def by (simp add: REP)

lemma domain_rep_iso:
  fixes abs and rep
  assumes REP: "REP('b) = REP('a)"
  assumes abs_def: "abs \<equiv> (coerce :: 'a \<rightarrow> 'b)"
  assumes rep_def: "rep \<equiv> (coerce :: 'b \<rightarrow> 'a)"
  shows "abs\<cdot>(rep\<cdot>x) = x"
unfolding abs_def rep_def by (simp add: REP [symmetric])


subsection {* Proving a subtype is representable *}

text {*
  Temporarily relax type constraints for @{term "approx"},
  @{term emb}, and @{term prj}.
*}

setup {* Sign.add_const_constraint
  (@{const_name "approx"}, SOME @{typ "nat \<Rightarrow> 'a::cpo \<rightarrow> 'a"}) *}

setup {* Sign.add_const_constraint
  (@{const_name emb}, SOME @{typ "'a::pcpo \<rightarrow> udom"}) *}

setup {* Sign.add_const_constraint
  (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::pcpo"}) *}

definition
  repdef_approx ::
    "('a::pcpo \<Rightarrow> udom) \<Rightarrow> (udom \<Rightarrow> 'a) \<Rightarrow> udom alg_defl \<Rightarrow> nat \<Rightarrow> 'a \<rightarrow> 'a"
where
  "repdef_approx Rep Abs t = (\<lambda>i. \<Lambda> x. Abs (cast\<cdot>(approx i\<cdot>t)\<cdot>(Rep x)))"

lemma typedef_rep_class:
  fixes Rep :: "'a::pcpo \<Rightarrow> udom"
  fixes Abs :: "udom \<Rightarrow> 'a::pcpo"
  fixes t :: TypeRep
  assumes type: "type_definition Rep Abs {x. x ::: t}"
  assumes below: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  assumes emb: "emb \<equiv> (\<Lambda> x. Rep x)"
  assumes prj: "prj \<equiv> (\<Lambda> x. Abs (cast\<cdot>t\<cdot>x))"
  assumes approx: "(approx :: nat \<Rightarrow> 'a \<rightarrow> 'a) \<equiv> repdef_approx Rep Abs t"
  shows "OFCLASS('a, rep_class)"
proof
  have adm: "adm (\<lambda>x. x \<in> {x. x ::: t})"
    by (simp add: adm_in_deflation)
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
  have cast_cast_approx:
    "\<And>i x. cast\<cdot>t\<cdot>(cast\<cdot>(approx i\<cdot>t)\<cdot>x) = cast\<cdot>(approx i\<cdot>t)\<cdot>x"
    apply (rule cast_fixed)
    apply (rule subdeflationD)
    apply (rule approx.below)
    apply (rule cast_in_deflation)
    done
  have approx':
    "approx = (\<lambda>i. \<Lambda>(x::'a). prj\<cdot>(cast\<cdot>(approx i\<cdot>t)\<cdot>(emb\<cdot>x)))"
    unfolding approx repdef_approx_def
    apply (subst cast_cast_approx [symmetric])
    apply (simp add: prj_beta [symmetric] emb_beta [symmetric])
    done
  have emb_in_deflation: "\<And>x::'a. emb\<cdot>x ::: t"
    using type_definition.Rep [OF type]
    by (simp add: emb_beta)
  have prj_emb: "\<And>x::'a. prj\<cdot>(emb\<cdot>x) = x"
    unfolding prj_beta
    apply (simp add: cast_fixed [OF emb_in_deflation])
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
  show "chain (approx :: nat \<Rightarrow> 'a \<rightarrow> 'a)"
    unfolding approx' by simp
  show "\<And>x::'a. (\<Squnion>i. approx i\<cdot>x) = x"
    unfolding approx'
    apply (simp add: lub_distribs)
    apply (subst cast_fixed [OF emb_in_deflation])
    apply (rule prj_emb)
    done
  show "\<And>(i::nat) (x::'a). approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    unfolding approx'
    apply simp
    apply (simp add: emb_prj)
    apply (simp add: cast_cast_approx)
    done
  show "\<And>i::nat. finite {x::'a. approx i\<cdot>x = x}"
    apply (rule_tac B="(\<lambda>x. prj\<cdot>x) ` {x. cast\<cdot>(approx i\<cdot>t)\<cdot>x = x}"
           in finite_subset)
    apply (clarsimp simp add: approx')
    apply (drule_tac f="\<lambda>x. emb\<cdot>x" in arg_cong)
    apply (rule image_eqI)
    apply (rule prj_emb [symmetric])
    apply (simp add: emb_prj)
    apply (simp add: cast_cast_approx)
    apply (rule finite_imageI)
    apply (simp add: cast_approx_fixed_iff)
    apply (simp add: Collect_conj_eq)
    apply (simp add: finite_fixes_approx)
    done
qed

text {* Restore original typing constraints *}

setup {* Sign.add_const_constraint
  (@{const_name "approx"}, SOME @{typ "nat \<Rightarrow> 'a::profinite \<rightarrow> 'a"}) *}

setup {* Sign.add_const_constraint
  (@{const_name emb}, SOME @{typ "'a::rep \<rightarrow> udom"}) *}

setup {* Sign.add_const_constraint
  (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::rep"}) *}

lemma typedef_REP:
  fixes Rep :: "'a::rep \<Rightarrow> udom"
  fixes Abs :: "udom \<Rightarrow> 'a::rep"
  fixes t :: TypeRep
  assumes type: "type_definition Rep Abs {x. x ::: t}"
  assumes below: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  assumes emb: "emb \<equiv> (\<Lambda> x. Rep x)"
  assumes prj: "prj \<equiv> (\<Lambda> x. Abs (cast\<cdot>t\<cdot>x))"
  shows "REP('a) = t"
proof -
  have adm: "adm (\<lambda>x. x \<in> {x. x ::: t})"
    by (simp add: adm_in_deflation)
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
  have emb_in_deflation: "\<And>x::'a. emb\<cdot>x ::: t"
    using type_definition.Rep [OF type]
    by (simp add: emb_beta)
  have prj_emb: "\<And>x::'a. prj\<cdot>(emb\<cdot>x) = x"
    unfolding prj_beta
    apply (simp add: cast_fixed [OF emb_in_deflation])
    apply (simp add: emb_beta type_definition.Rep_inverse [OF type])
    done
  have emb_prj: "\<And>y. emb\<cdot>(prj\<cdot>y :: 'a) = cast\<cdot>t\<cdot>y"
    unfolding prj_beta emb_beta
    by (simp add: type_definition.Abs_inverse [OF type])
  show "REP('a) = t"
    apply (rule cast_eq_imp_eq, rule ext_cfun)
    apply (simp add: cast_REP emb_prj)
    done
qed

lemma adm_mem_Collect_in_deflation: "adm (\<lambda>x. x \<in> {x. x ::: A})"
unfolding mem_Collect_eq by (rule adm_in_deflation)

use "Tools/repdef.ML"


subsection {* Instances of class @{text rep} *}

subsubsection {* Universal Domain *}

text "The Universal Domain itself is trivially representable."

instantiation udom :: rep
begin

definition emb_udom_def [simp]: "emb = (ID :: udom \<rightarrow> udom)"
definition prj_udom_def [simp]: "prj = (ID :: udom \<rightarrow> udom)"

instance
 apply (intro_classes)
 apply (simp_all add: ep_pair.intro)
done

end

subsubsection {* Lifted types *}

instantiation lift :: (countable) rep
begin

definition emb_lift_def:
  "emb = udom_emb oo (FLIFT x. Def (to_nat x))"

definition prj_lift_def:
  "prj = (FLIFT n. if (\<exists>x::'a::countable. n = to_nat x)
                    then Def (THE x::'a. n = to_nat x) else \<bottom>) oo udom_prj"

instance
 apply (intro_classes, unfold emb_lift_def prj_lift_def)
 apply (rule ep_pair_comp [OF _ ep_pair_udom])
 apply (rule ep_pair.intro)
  apply (case_tac x, simp, simp)
 apply (case_tac y, simp, clarsimp)
done

end

subsubsection {* Representable type constructors *}

text "Functions between representable types are representable."

instantiation "->" :: (rep, rep) rep
begin

definition emb_cfun_def: "emb = udom_emb oo cfun_map\<cdot>prj\<cdot>emb"
definition prj_cfun_def: "prj = cfun_map\<cdot>emb\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_cfun_def prj_cfun_def)
 apply (intro ep_pair_comp ep_pair_cfun_map ep_pair_emb_prj ep_pair_udom)
done

end

text "Strict products of representable types are representable."

instantiation "**" :: (rep, rep) rep
begin

definition emb_sprod_def: "emb = udom_emb oo sprod_map\<cdot>emb\<cdot>emb"
definition prj_sprod_def: "prj = sprod_map\<cdot>prj\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_sprod_def prj_sprod_def)
 apply (intro ep_pair_comp ep_pair_sprod_map ep_pair_emb_prj ep_pair_udom)
done

end

text "Strict sums of representable types are representable."

instantiation "++" :: (rep, rep) rep
begin

definition emb_ssum_def: "emb = udom_emb oo ssum_map\<cdot>emb\<cdot>emb"
definition prj_ssum_def: "prj = ssum_map\<cdot>prj\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_ssum_def prj_ssum_def)
 apply (intro ep_pair_comp ep_pair_ssum_map ep_pair_emb_prj ep_pair_udom)
done

end

text "Up of a representable type is representable."

instantiation "u" :: (rep) rep
begin

definition emb_u_def: "emb = udom_emb oo u_map\<cdot>emb"
definition prj_u_def: "prj = u_map\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_u_def prj_u_def)
 apply (intro ep_pair_comp ep_pair_u_map ep_pair_emb_prj ep_pair_udom)
done

end

text "Cartesian products of representable types are representable."

instantiation "*" :: (rep, rep) rep
begin

definition emb_cprod_def: "emb = udom_emb oo cprod_map\<cdot>emb\<cdot>emb"
definition prj_cprod_def: "prj = cprod_map\<cdot>prj\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_cprod_def prj_cprod_def)
 apply (intro ep_pair_comp ep_pair_cprod_map ep_pair_emb_prj ep_pair_udom)
done

end

text "Upper powerdomain of a representable type is representable."

instantiation upper_pd :: (rep) rep
begin

definition emb_upper_pd_def: "emb = udom_emb oo upper_map\<cdot>emb"
definition prj_upper_pd_def: "prj = upper_map\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_upper_pd_def prj_upper_pd_def)
 apply (intro ep_pair_comp ep_pair_upper_map ep_pair_emb_prj ep_pair_udom)
done

end

text "Lower powerdomain of a representable type is representable."

instantiation lower_pd :: (rep) rep
begin

definition emb_lower_pd_def: "emb = udom_emb oo lower_map\<cdot>emb"
definition prj_lower_pd_def: "prj = lower_map\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_lower_pd_def prj_lower_pd_def)
 apply (intro ep_pair_comp ep_pair_lower_map ep_pair_emb_prj ep_pair_udom)
done

end

text "Convex powerdomain of a representable type is representable."

instantiation convex_pd :: (rep) rep
begin

definition emb_convex_pd_def: "emb = udom_emb oo convex_map\<cdot>emb"
definition prj_convex_pd_def: "prj = convex_map\<cdot>prj oo udom_prj"

instance
 apply (intro_classes, unfold emb_convex_pd_def prj_convex_pd_def)
 apply (intro ep_pair_comp ep_pair_convex_map ep_pair_emb_prj ep_pair_udom)
done

end

subsection {* Finite deflation lemmas *}

text "TODO: move these lemmas somewhere else"

lemma finite_compact_range_imp_finite_range:
  fixes d :: "'a::profinite \<rightarrow> 'b::cpo"
  assumes "finite ((\<lambda>x. d\<cdot>x) ` {x. compact x})"
  shows "finite (range (\<lambda>x. d\<cdot>x))"
proof (rule finite_subset [OF _ prems])
  {
    fix x :: 'a
    have "range (\<lambda>i. d\<cdot>(approx i\<cdot>x)) \<subseteq> (\<lambda>x. d\<cdot>x) ` {x. compact x}"
      by auto
    hence "finite (range (\<lambda>i. d\<cdot>(approx i\<cdot>x)))"
      using prems by (rule finite_subset)
    hence "finite_chain (\<lambda>i. d\<cdot>(approx i\<cdot>x))"
      by (simp add: finite_range_imp_finch)
    hence "\<exists>i. (\<Squnion>i. d\<cdot>(approx i\<cdot>x)) = d\<cdot>(approx i\<cdot>x)"
      by (simp add: finite_chain_def maxinch_is_thelub)
    hence "\<exists>i. d\<cdot>x = d\<cdot>(approx i\<cdot>x)"
      by (simp add: lub_distribs)
    hence "d\<cdot>x \<in> (\<lambda>x. d\<cdot>x) ` {x. compact x}"
      by auto
  }
  thus "range (\<lambda>x. d\<cdot>x) \<subseteq> (\<lambda>x. d\<cdot>x) ` {x. compact x}"
    by clarsimp
qed

lemma finite_deflation_upper_map:
  assumes "finite_deflation d" shows "finite_deflation (upper_map\<cdot>d)"
proof (intro finite_deflation.intro finite_deflation_axioms.intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (upper_map\<cdot>d)" by (rule deflation_upper_map)
  have "finite (range (\<lambda>x. d\<cdot>x))" by (rule d.finite_range)
  hence "finite (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_compact_basis_inject)
  hence "finite (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x)))" by simp
  hence "finite (Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_pd_basis_inject)
  hence "finite (upper_principal ` Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))" by simp
  hence "finite ((\<lambda>xs. upper_map\<cdot>d\<cdot>xs) ` range upper_principal)"
    apply (rule finite_subset [COMP swap_prems_rl])
    apply (clarsimp, rename_tac t)
    apply (induct_tac t rule: pd_basis_induct)
    apply (simp only: upper_unit_Rep_compact_basis [symmetric] upper_map_unit)
    apply (subgoal_tac "\<exists>b. d\<cdot>(Rep_compact_basis a) = Rep_compact_basis b")
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDUnit)
    apply (rule image_eqI)
    apply (erule sym)
    apply simp
    apply (rule exI)
    apply (rule Abs_compact_basis_inverse [symmetric])
    apply (simp add: d.compact)
    apply (simp only: upper_plus_principal [symmetric] upper_map_plus)
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDPlus)
    done
  moreover have "{xs::'a upper_pd. compact xs} = range upper_principal"
    by (auto dest: upper_pd.compact_imp_principal)
  ultimately have "finite ((\<lambda>xs. upper_map\<cdot>d\<cdot>xs) ` {xs::'a upper_pd. compact xs})"
    by simp
  hence "finite (range (\<lambda>xs. upper_map\<cdot>d\<cdot>xs))"
    by (rule finite_compact_range_imp_finite_range)
  thus "finite {xs. upper_map\<cdot>d\<cdot>xs = xs}"
    by (rule finite_range_imp_finite_fixes)
qed

lemma finite_deflation_lower_map:
  assumes "finite_deflation d" shows "finite_deflation (lower_map\<cdot>d)"
proof (intro finite_deflation.intro finite_deflation_axioms.intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (lower_map\<cdot>d)" by (rule deflation_lower_map)
  have "finite (range (\<lambda>x. d\<cdot>x))" by (rule d.finite_range)
  hence "finite (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_compact_basis_inject)
  hence "finite (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x)))" by simp
  hence "finite (Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_pd_basis_inject)
  hence "finite (lower_principal ` Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))" by simp
  hence "finite ((\<lambda>xs. lower_map\<cdot>d\<cdot>xs) ` range lower_principal)"
    apply (rule finite_subset [COMP swap_prems_rl])
    apply (clarsimp, rename_tac t)
    apply (induct_tac t rule: pd_basis_induct)
    apply (simp only: lower_unit_Rep_compact_basis [symmetric] lower_map_unit)
    apply (subgoal_tac "\<exists>b. d\<cdot>(Rep_compact_basis a) = Rep_compact_basis b")
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDUnit)
    apply (rule image_eqI)
    apply (erule sym)
    apply simp
    apply (rule exI)
    apply (rule Abs_compact_basis_inverse [symmetric])
    apply (simp add: d.compact)
    apply (simp only: lower_plus_principal [symmetric] lower_map_plus)
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDPlus)
    done
  moreover have "{xs::'a lower_pd. compact xs} = range lower_principal"
    by (auto dest: lower_pd.compact_imp_principal)
  ultimately have "finite ((\<lambda>xs. lower_map\<cdot>d\<cdot>xs) ` {xs::'a lower_pd. compact xs})"
    by simp
  hence "finite (range (\<lambda>xs. lower_map\<cdot>d\<cdot>xs))"
    by (rule finite_compact_range_imp_finite_range)
  thus "finite {xs. lower_map\<cdot>d\<cdot>xs = xs}"
    by (rule finite_range_imp_finite_fixes)
qed

lemma finite_deflation_convex_map:
  assumes "finite_deflation d" shows "finite_deflation (convex_map\<cdot>d)"
proof (intro finite_deflation.intro finite_deflation_axioms.intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (convex_map\<cdot>d)" by (rule deflation_convex_map)
  have "finite (range (\<lambda>x. d\<cdot>x))" by (rule d.finite_range)
  hence "finite (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_compact_basis_inject)
  hence "finite (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x)))" by simp
  hence "finite (Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))"
    by (rule finite_vimageI, simp add: inj_on_def Rep_pd_basis_inject)
  hence "finite (convex_principal ` Rep_pd_basis -` (Pow (Rep_compact_basis -` range (\<lambda>x. d\<cdot>x))))" by simp
  hence "finite ((\<lambda>xs. convex_map\<cdot>d\<cdot>xs) ` range convex_principal)"
    apply (rule finite_subset [COMP swap_prems_rl])
    apply (clarsimp, rename_tac t)
    apply (induct_tac t rule: pd_basis_induct)
    apply (simp only: convex_unit_Rep_compact_basis [symmetric] convex_map_unit)
    apply (subgoal_tac "\<exists>b. d\<cdot>(Rep_compact_basis a) = Rep_compact_basis b")
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDUnit)
    apply (rule image_eqI)
    apply (erule sym)
    apply simp
    apply (rule exI)
    apply (rule Abs_compact_basis_inverse [symmetric])
    apply (simp add: d.compact)
    apply (simp only: convex_plus_principal [symmetric] convex_map_plus)
    apply clarsimp
    apply (rule imageI)
    apply (rule vimageI2)
    apply (simp add: Rep_PDPlus)
    done
  moreover have "{xs::'a convex_pd. compact xs} = range convex_principal"
    by (auto dest: convex_pd.compact_imp_principal)
  ultimately have "finite ((\<lambda>xs. convex_map\<cdot>d\<cdot>xs) ` {xs::'a convex_pd. compact xs})"
    by simp
  hence "finite (range (\<lambda>xs. convex_map\<cdot>d\<cdot>xs))"
    by (rule finite_compact_range_imp_finite_range)
  thus "finite {xs. convex_map\<cdot>d\<cdot>xs = xs}"
    by (rule finite_range_imp_finite_fixes)
qed

subsection {* Type combinators *}

definition
  TypeRep_fun1 ::
    "((udom \<rightarrow> udom) \<rightarrow> ('a \<rightarrow> 'a))
      \<Rightarrow> (TypeRep \<rightarrow> TypeRep)"
where
  "TypeRep_fun1 f =
    alg_defl.basis_fun (\<lambda>a.
      alg_defl_principal (
        Abs_fin_defl (udom_emb oo f\<cdot>(Rep_fin_defl a) oo udom_prj)))"

definition
  TypeRep_fun2 ::
    "((udom \<rightarrow> udom) \<rightarrow> (udom \<rightarrow> udom) \<rightarrow> ('a \<rightarrow> 'a))
      \<Rightarrow> (TypeRep \<rightarrow> TypeRep \<rightarrow> TypeRep)"
where
  "TypeRep_fun2 f =
    alg_defl.basis_fun (\<lambda>a.
      alg_defl.basis_fun (\<lambda>b.
        alg_defl_principal (
          Abs_fin_defl (udom_emb oo
            f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo udom_prj))))"

definition "cfun_defl = TypeRep_fun2 cfun_map"
definition "ssum_defl = TypeRep_fun2 ssum_map"
definition "sprod_defl = TypeRep_fun2 sprod_map"
definition "cprod_defl = TypeRep_fun2 cprod_map"
definition "u_defl = TypeRep_fun1 u_map"
definition "upper_defl = TypeRep_fun1 upper_map"
definition "lower_defl = TypeRep_fun1 lower_map"
definition "convex_defl = TypeRep_fun1 convex_map"

lemma Rep_fin_defl_mono: "a \<sqsubseteq> b \<Longrightarrow> Rep_fin_defl a \<sqsubseteq> Rep_fin_defl b"
unfolding below_fin_defl_def .

lemma cast_TypeRep_fun1:
  assumes f: "\<And>a. finite_deflation a \<Longrightarrow> finite_deflation (f\<cdot>a)"
  shows "cast\<cdot>(TypeRep_fun1 f\<cdot>A) = udom_emb oo f\<cdot>(cast\<cdot>A) oo udom_prj"
proof -
  have 1: "\<And>a. finite_deflation (udom_emb oo f\<cdot>(Rep_fin_defl a) oo udom_prj)"
    apply (rule ep_pair.finite_deflation_e_d_p [OF ep_pair_udom])
    apply (rule f, rule finite_deflation_Rep_fin_defl)
    done
  show ?thesis
    by (induct A rule: alg_defl.principal_induct, simp)
       (simp only: TypeRep_fun1_def
                   alg_defl.basis_fun_principal
                   alg_defl.basis_fun_mono
                   alg_defl.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_alg_defl_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

lemma cast_TypeRep_fun2:
  assumes f: "\<And>a b. finite_deflation a \<Longrightarrow> finite_deflation b \<Longrightarrow>
                finite_deflation (f\<cdot>a\<cdot>b)"
  shows "cast\<cdot>(TypeRep_fun2 f\<cdot>A\<cdot>B) = udom_emb oo f\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj"
proof -
  have 1: "\<And>a b. finite_deflation
           (udom_emb oo f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo udom_prj)"
    apply (rule ep_pair.finite_deflation_e_d_p [OF ep_pair_udom])
    apply (rule f, (rule finite_deflation_Rep_fin_defl)+)
    done
  show ?thesis
    by (induct A B rule: alg_defl.principal_induct2, simp, simp)
       (simp only: TypeRep_fun2_def
                   alg_defl.basis_fun_principal
                   alg_defl.basis_fun_mono
                   alg_defl.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_alg_defl_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

lemma cast_cfun_defl:
  "cast\<cdot>(cfun_defl\<cdot>A\<cdot>B) = udom_emb oo cfun_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj"
unfolding cfun_defl_def
apply (rule cast_TypeRep_fun2)
apply (erule (1) finite_deflation_cfun_map)
done

lemma cast_ssum_defl:
  "cast\<cdot>(ssum_defl\<cdot>A\<cdot>B) = udom_emb oo ssum_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj"
unfolding ssum_defl_def
apply (rule cast_TypeRep_fun2)
apply (erule (1) finite_deflation_ssum_map)
done

lemma cast_sprod_defl:
  "cast\<cdot>(sprod_defl\<cdot>A\<cdot>B) = udom_emb oo sprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj"
unfolding sprod_defl_def
apply (rule cast_TypeRep_fun2)
apply (erule (1) finite_deflation_sprod_map)
done

lemma cast_cprod_defl:
  "cast\<cdot>(cprod_defl\<cdot>A\<cdot>B) = udom_emb oo cprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj"
unfolding cprod_defl_def
apply (rule cast_TypeRep_fun2)
apply (erule (1) finite_deflation_cprod_map)
done

lemma cast_u_defl:
  "cast\<cdot>(u_defl\<cdot>A) = udom_emb oo u_map\<cdot>(cast\<cdot>A) oo udom_prj"
unfolding u_defl_def
apply (rule cast_TypeRep_fun1)
apply (erule finite_deflation_u_map)
done

lemma cast_upper_defl:
  "cast\<cdot>(upper_defl\<cdot>A) = udom_emb oo upper_map\<cdot>(cast\<cdot>A) oo udom_prj"
unfolding upper_defl_def
apply (rule cast_TypeRep_fun1)
apply (erule finite_deflation_upper_map)
done

lemma cast_lower_defl:
  "cast\<cdot>(lower_defl\<cdot>A) = udom_emb oo lower_map\<cdot>(cast\<cdot>A) oo udom_prj"
unfolding lower_defl_def
apply (rule cast_TypeRep_fun1)
apply (erule finite_deflation_lower_map)
done

lemma cast_convex_defl:
  "cast\<cdot>(convex_defl\<cdot>A) = udom_emb oo convex_map\<cdot>(cast\<cdot>A) oo udom_prj"
unfolding convex_defl_def
apply (rule cast_TypeRep_fun1)
apply (erule finite_deflation_convex_map)
done

text {* REP of type constructor = type combinator *}

lemma REP_cfun: "REP('a \<rightarrow> 'b) = cfun_defl\<cdot>REP('a)\<cdot>REP('b)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_cfun_defl)
apply (simp add: cfun_map_def)
apply (simp only: prj_cfun_def emb_cfun_def)
apply (simp add: expand_cfun_eq ep_pair.e_eq_iff [OF ep_pair_udom])
done


lemma REP_ssum: "REP('a \<oplus> 'b) = ssum_defl\<cdot>REP('a)\<cdot>REP('b)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_ssum_defl)
apply (simp add: prj_ssum_def)
apply (simp add: emb_ssum_def)
apply (simp add: ssum_map_map cfcomp1)
done

lemma REP_sprod: "REP('a \<otimes> 'b) = sprod_defl\<cdot>REP('a)\<cdot>REP('b)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_sprod_defl)
apply (simp add: prj_sprod_def)
apply (simp add: emb_sprod_def)
apply (simp add: sprod_map_map cfcomp1)
done

lemma REP_cprod: "REP('a \<times> 'b) = cprod_defl\<cdot>REP('a)\<cdot>REP('b)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_cprod_defl)
apply (simp add: prj_cprod_def)
apply (simp add: emb_cprod_def)
apply (simp add: cprod_map_map cfcomp1)
done

lemma REP_up: "REP('a u) = u_defl\<cdot>REP('a)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_u_defl)
apply (simp add: prj_u_def)
apply (simp add: emb_u_def)
apply (simp add: u_map_map cfcomp1)
done

lemma REP_upper: "REP('a upper_pd) = upper_defl\<cdot>REP('a)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_upper_defl)
apply (simp add: prj_upper_pd_def)
apply (simp add: emb_upper_pd_def)
apply (simp add: upper_map_map cfcomp1)
done

lemma REP_lower: "REP('a lower_pd) = lower_defl\<cdot>REP('a)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_lower_defl)
apply (simp add: prj_lower_pd_def)
apply (simp add: emb_lower_pd_def)
apply (simp add: lower_map_map cfcomp1)
done

lemma REP_convex: "REP('a convex_pd) = convex_defl\<cdot>REP('a)"
apply (rule cast_eq_imp_eq, rule ext_cfun)
apply (simp add: cast_REP cast_convex_defl)
apply (simp add: prj_convex_pd_def)
apply (simp add: emb_convex_pd_def)
apply (simp add: convex_map_map cfcomp1)
done

lemmas REP_simps =
  REP_cfun
  REP_ssum
  REP_sprod
  REP_cprod
  REP_up
  REP_upper
  REP_lower
  REP_convex

subsection {* Isomorphic deflations *}

definition
  isodefl :: "('a::rep \<rightarrow> 'a) \<Rightarrow> udom alg_defl \<Rightarrow> bool"
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
  fixes d :: "'a::rep \<rightarrow> 'a"
  assumes "isodefl d t" shows "deflation d"
proof
  note prems [unfolded isodefl_def, simp]
  fix x :: 'a
  show "d\<cdot>(d\<cdot>x) = d\<cdot>x"
    using cast.idem [of t "emb\<cdot>x"] by simp
  show "d\<cdot>x \<sqsubseteq> x"
    using cast.below [of t "emb\<cdot>x"] by simp
qed

lemma isodefl_ID_REP: "isodefl (ID :: 'a \<rightarrow> 'a) REP('a)"
unfolding isodefl_def by (simp add: cast_REP)

lemma isodefl_REP_imp_ID: "isodefl (d :: 'a \<rightarrow> 'a) REP('a) \<Longrightarrow> d = ID"
unfolding isodefl_def
apply (simp add: cast_REP)
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
apply (simp add: prems)
done

lemma isodefl_coerce:
  fixes d :: "'a \<rightarrow> 'a"
  assumes REP: "REP('b) = REP('a)"
  shows "isodefl d t \<Longrightarrow> isodefl (coerce oo d oo coerce :: 'b \<rightarrow> 'b) t"
unfolding isodefl_def
apply (simp add: expand_cfun_eq)
apply (simp add: emb_coerce coerce_prj REP)
done

lemma isodefl_abs_rep:
  fixes abs and rep and d
  assumes REP: "REP('b) = REP('a)"
  assumes abs_def: "abs \<equiv> (coerce :: 'a \<rightarrow> 'b)"
  assumes rep_def: "rep \<equiv> (coerce :: 'b \<rightarrow> 'a)"
  shows "isodefl d t \<Longrightarrow> isodefl (abs oo d oo rep) t"
unfolding abs_def rep_def using REP by (rule isodefl_coerce)

lemma isodefl_cfun:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (cfun_map\<cdot>d1\<cdot>d2) (cfun_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_cfun_defl cast_isodefl)
apply (simp add: emb_cfun_def prj_cfun_def)
apply (simp add: cfun_map_map cfcomp1)
done

lemma isodefl_ssum:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (ssum_map\<cdot>d1\<cdot>d2) (ssum_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_ssum_defl cast_isodefl)
apply (simp add: emb_ssum_def prj_ssum_def)
apply (simp add: ssum_map_map isodefl_strict)
done

lemma isodefl_sprod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (sprod_map\<cdot>d1\<cdot>d2) (sprod_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_sprod_defl cast_isodefl)
apply (simp add: emb_sprod_def prj_sprod_def)
apply (simp add: sprod_map_map isodefl_strict)
done

lemma isodefl_cprod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (cprod_map\<cdot>d1\<cdot>d2) (cprod_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_cprod_defl cast_isodefl)
apply (simp add: emb_cprod_def prj_cprod_def)
apply (simp add: cprod_map_map cfcomp1)
done

lemma isodefl_u:
  "isodefl d t \<Longrightarrow> isodefl (u_map\<cdot>d) (u_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_u_defl cast_isodefl)
apply (simp add: emb_u_def prj_u_def)
apply (simp add: u_map_map)
done

lemma isodefl_upper:
  "isodefl d t \<Longrightarrow> isodefl (upper_map\<cdot>d) (upper_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_upper_defl cast_isodefl)
apply (simp add: emb_upper_pd_def prj_upper_pd_def)
apply (simp add: upper_map_map)
done

lemma isodefl_lower:
  "isodefl d t \<Longrightarrow> isodefl (lower_map\<cdot>d) (lower_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_lower_defl cast_isodefl)
apply (simp add: emb_lower_pd_def prj_lower_pd_def)
apply (simp add: lower_map_map)
done

lemma isodefl_convex:
  "isodefl d t \<Longrightarrow> isodefl (convex_map\<cdot>d) (convex_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_convex_defl cast_isodefl)
apply (simp add: emb_convex_pd_def prj_convex_pd_def)
apply (simp add: convex_map_map)
done

end
