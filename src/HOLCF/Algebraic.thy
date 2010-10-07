(*  Title:      HOLCF/Algebraic.thy
    Author:     Brian Huffman
*)

header {* Algebraic deflations *}

theory Algebraic
imports Universal
begin

subsection {* Type constructor for finite deflations *}

typedef (open) fin_defl = "{d::udom \<rightarrow> udom. finite_deflation d}"
by (fast intro: finite_deflation_UU)

instantiation fin_defl :: below
begin

definition below_fin_defl_def:
    "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep_fin_defl x \<sqsubseteq> Rep_fin_defl y"

instance ..
end

instance fin_defl :: po
using type_definition_fin_defl below_fin_defl_def
by (rule typedef_po)

lemma finite_deflation_Rep_fin_defl: "finite_deflation (Rep_fin_defl d)"
using Rep_fin_defl by simp

lemma deflation_Rep_fin_defl: "deflation (Rep_fin_defl d)"
using finite_deflation_Rep_fin_defl
by (rule finite_deflation_imp_deflation)

interpretation Rep_fin_defl: finite_deflation "Rep_fin_defl d"
by (rule finite_deflation_Rep_fin_defl)

lemma fin_defl_belowI:
  "(\<And>x. Rep_fin_defl a\<cdot>x = x \<Longrightarrow> Rep_fin_defl b\<cdot>x = x) \<Longrightarrow> a \<sqsubseteq> b"
unfolding below_fin_defl_def
by (rule Rep_fin_defl.belowI)

lemma fin_defl_belowD:
  "\<lbrakk>a \<sqsubseteq> b; Rep_fin_defl a\<cdot>x = x\<rbrakk> \<Longrightarrow> Rep_fin_defl b\<cdot>x = x"
unfolding below_fin_defl_def
by (rule Rep_fin_defl.belowD)

lemma fin_defl_eqI:
  "(\<And>x. Rep_fin_defl a\<cdot>x = x \<longleftrightarrow> Rep_fin_defl b\<cdot>x = x) \<Longrightarrow> a = b"
apply (rule below_antisym)
apply (rule fin_defl_belowI, simp)
apply (rule fin_defl_belowI, simp)
done

lemma Rep_fin_defl_mono: "a \<sqsubseteq> b \<Longrightarrow> Rep_fin_defl a \<sqsubseteq> Rep_fin_defl b"
unfolding below_fin_defl_def .

lemma Abs_fin_defl_mono:
  "\<lbrakk>finite_deflation a; finite_deflation b; a \<sqsubseteq> b\<rbrakk>
    \<Longrightarrow> Abs_fin_defl a \<sqsubseteq> Abs_fin_defl b"
unfolding below_fin_defl_def
by (simp add: Abs_fin_defl_inverse)

lemma (in finite_deflation) compact_belowI:
  assumes "\<And>x. compact x \<Longrightarrow> d\<cdot>x = x \<Longrightarrow> f\<cdot>x = x" shows "d \<sqsubseteq> f"
by (rule belowI, rule assms, erule subst, rule compact)

lemma compact_Rep_fin_defl [simp]: "compact (Rep_fin_defl a)"
using finite_deflation_Rep_fin_defl
by (rule finite_deflation_imp_compact)

subsection {* Defining algebraic deflations by ideal completion *}

text {*
  An SFP domain is one that can be represented as the limit of a
  sequence of finite posets.  Here we use omega-algebraic deflations
  (i.e. countable ideals of finite deflations) to model sequences of
  finite posets.
*}

typedef (open) sfp = "{S::fin_defl set. below.ideal S}"
by (fast intro: below.ideal_principal)

instantiation sfp :: below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_sfp x \<subseteq> Rep_sfp y"

instance ..
end

instance sfp :: po
using type_definition_sfp below_sfp_def
by (rule below.typedef_ideal_po)

instance sfp :: cpo
using type_definition_sfp below_sfp_def
by (rule below.typedef_ideal_cpo)

definition
  sfp_principal :: "fin_defl \<Rightarrow> sfp" where
  "sfp_principal t = Abs_sfp {u. u \<sqsubseteq> t}"

lemma fin_defl_countable: "\<exists>f::fin_defl \<Rightarrow> nat. inj f"
proof
  have *: "\<And>d. finite (approx_chain.place udom_approx `
               Rep_compact_basis -` {x. Rep_fin_defl d\<cdot>x = x})"
    apply (rule finite_imageI)
    apply (rule finite_vimageI)
    apply (rule Rep_fin_defl.finite_fixes)
    apply (simp add: inj_on_def Rep_compact_basis_inject)
    done
  have range_eq: "range Rep_compact_basis = {x. compact x}"
    using type_definition_compact_basis by (rule type_definition.Rep_range)
  show "inj (\<lambda>d. set_encode
    (approx_chain.place udom_approx ` Rep_compact_basis -` {x. Rep_fin_defl d\<cdot>x = x}))"
    apply (rule inj_onI)
    apply (simp only: set_encode_eq *)
    apply (simp only: inj_image_eq_iff approx_chain.inj_place [OF udom_approx])
    apply (drule_tac f="image Rep_compact_basis" in arg_cong)
    apply (simp del: vimage_Collect_eq add: range_eq set_eq_iff)
    apply (rule Rep_fin_defl_inject [THEN iffD1])
    apply (rule below_antisym)
    apply (rule Rep_fin_defl.compact_belowI, rename_tac z)
    apply (drule_tac x=z in spec, simp)
    apply (rule Rep_fin_defl.compact_belowI, rename_tac z)
    apply (drule_tac x=z in spec, simp)
    done
qed

interpretation sfp: ideal_completion below sfp_principal Rep_sfp
using type_definition_sfp below_sfp_def
using sfp_principal_def fin_defl_countable
by (rule below.typedef_ideal_completion)

text {* Algebraic deflations are pointed *}

lemma sfp_minimal: "sfp_principal (Abs_fin_defl \<bottom>) \<sqsubseteq> x"
apply (induct x rule: sfp.principal_induct, simp)
apply (rule sfp.principal_mono)
apply (simp add: below_fin_defl_def)
apply (simp add: Abs_fin_defl_inverse finite_deflation_UU)
done

instance sfp :: pcpo
by intro_classes (fast intro: sfp_minimal)

lemma inst_sfp_pcpo: "\<bottom> = sfp_principal (Abs_fin_defl \<bottom>)"
by (rule sfp_minimal [THEN UU_I, symmetric])

subsection {* Applying algebraic deflations *}

definition
  cast :: "sfp \<rightarrow> udom \<rightarrow> udom"
where
  "cast = sfp.basis_fun Rep_fin_defl"

lemma cast_sfp_principal:
  "cast\<cdot>(sfp_principal a) = Rep_fin_defl a"
unfolding cast_def
apply (rule sfp.basis_fun_principal)
apply (simp only: below_fin_defl_def)
done

lemma deflation_cast: "deflation (cast\<cdot>d)"
apply (induct d rule: sfp.principal_induct)
apply (rule adm_subst [OF _ adm_deflation], simp)
apply (simp add: cast_sfp_principal)
apply (rule finite_deflation_imp_deflation)
apply (rule finite_deflation_Rep_fin_defl)
done

lemma finite_deflation_cast:
  "compact d \<Longrightarrow> finite_deflation (cast\<cdot>d)"
apply (drule sfp.compact_imp_principal, clarify)
apply (simp add: cast_sfp_principal)
apply (rule finite_deflation_Rep_fin_defl)
done

interpretation cast: deflation "cast\<cdot>d"
by (rule deflation_cast)

declare cast.idem [simp]

lemma compact_cast [simp]: "compact d \<Longrightarrow> compact (cast\<cdot>d)"
apply (rule finite_deflation_imp_compact)
apply (erule finite_deflation_cast)
done

lemma cast_below_cast: "cast\<cdot>A \<sqsubseteq> cast\<cdot>B \<longleftrightarrow> A \<sqsubseteq> B"
apply (induct A rule: sfp.principal_induct, simp)
apply (induct B rule: sfp.principal_induct, simp)
apply (simp add: cast_sfp_principal below_fin_defl_def)
done

lemma compact_cast_iff: "compact (cast\<cdot>d) \<longleftrightarrow> compact d"
apply (rule iffI)
apply (simp only: compact_def cast_below_cast [symmetric])
apply (erule adm_subst [OF cont_Rep_CFun2])
apply (erule compact_cast)
done

lemma cast_below_imp_below: "cast\<cdot>A \<sqsubseteq> cast\<cdot>B \<Longrightarrow> A \<sqsubseteq> B"
by (simp only: cast_below_cast)

lemma cast_eq_imp_eq: "cast\<cdot>A = cast\<cdot>B \<Longrightarrow> A = B"
by (simp add: below_antisym cast_below_imp_below)

lemma cast_strict1 [simp]: "cast\<cdot>\<bottom> = \<bottom>"
apply (subst inst_sfp_pcpo)
apply (subst cast_sfp_principal)
apply (rule Abs_fin_defl_inverse)
apply (simp add: finite_deflation_UU)
done

lemma cast_strict2 [simp]: "cast\<cdot>A\<cdot>\<bottom> = \<bottom>"
by (rule cast.below [THEN UU_I])

subsection {* Deflation membership relation *}

definition
  in_sfp :: "udom \<Rightarrow> sfp \<Rightarrow> bool" (infixl ":::" 50)
where
  "x ::: A \<longleftrightarrow> cast\<cdot>A\<cdot>x = x"

lemma adm_in_sfp: "adm (\<lambda>x. x ::: A)"
unfolding in_sfp_def by simp

lemma in_sfpI: "cast\<cdot>A\<cdot>x = x \<Longrightarrow> x ::: A"
unfolding in_sfp_def .

lemma cast_fixed: "x ::: A \<Longrightarrow> cast\<cdot>A\<cdot>x = x"
unfolding in_sfp_def .

lemma cast_in_sfp [simp]: "cast\<cdot>A\<cdot>x ::: A"
unfolding in_sfp_def by (rule cast.idem)

lemma bottom_in_sfp [simp]: "\<bottom> ::: A"
unfolding in_sfp_def by (rule cast_strict2)

lemma sfp_belowD: "A \<sqsubseteq> B \<Longrightarrow> x ::: A \<Longrightarrow> x ::: B"
unfolding in_sfp_def
 apply (rule deflation.belowD)
   apply (rule deflation_cast)
  apply (erule monofun_cfun_arg)
 apply assumption
done

lemma rev_sfp_belowD: "x ::: A \<Longrightarrow> A \<sqsubseteq> B \<Longrightarrow> x ::: B"
by (rule sfp_belowD)

lemma sfp_belowI: "(\<And>x. x ::: A \<Longrightarrow> x ::: B) \<Longrightarrow> A \<sqsubseteq> B"
apply (rule cast_below_imp_below)
apply (rule cast.belowI)
apply (simp add: in_sfp_def)
done

end
