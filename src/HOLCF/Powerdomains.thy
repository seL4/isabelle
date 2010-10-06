(*  Title:      HOLCF/Powerdomains.thy
    Author:     Brian Huffman
*)

header {* Powerdomains *}

theory Powerdomains
imports Representable ConvexPD
begin

subsection {* Powerdomains are representable *}

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
proof (rule finite_deflation_intro)
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
proof (rule finite_deflation_intro)
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
proof (rule finite_deflation_intro)
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

subsection {* Deflation combinators *}

definition "upper_defl = TypeRep_fun1 upper_map"
definition "lower_defl = TypeRep_fun1 lower_map"
definition "convex_defl = TypeRep_fun1 convex_map"

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

subsection {* Domain package setup for powerdomains *}

setup {*
  fold Domain_Isomorphism.add_type_constructor
    [(@{type_name "upper_pd"}, @{term upper_defl}, @{const_name upper_map},
        @{thm REP_upper}, @{thm isodefl_upper}, @{thm upper_map_ID},
          @{thm deflation_upper_map}),

     (@{type_name "lower_pd"}, @{term lower_defl}, @{const_name lower_map},
        @{thm REP_lower}, @{thm isodefl_lower}, @{thm lower_map_ID},
          @{thm deflation_lower_map}),

     (@{type_name "convex_pd"}, @{term convex_defl}, @{const_name convex_map},
        @{thm REP_convex}, @{thm isodefl_convex}, @{thm convex_map_ID},
          @{thm deflation_convex_map})]
*}

end
