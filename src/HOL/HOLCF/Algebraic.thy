(*  Title:      HOL/HOLCF/Algebraic.thy
    Author:     Brian Huffman
*)

header {* Algebraic deflations *}

theory Algebraic
imports Universal Map_Functions
begin

default_sort bifinite

subsection {* Type constructor for finite deflations *}

typedef 'a fin_defl = "{d::'a \<rightarrow> 'a. finite_deflation d}"
by (fast intro: finite_deflation_bottom)

instantiation fin_defl :: (bifinite) below
begin

definition below_fin_defl_def:
  "below \<equiv> \<lambda>x y. Rep_fin_defl x \<sqsubseteq> Rep_fin_defl y"

instance ..
end

instance fin_defl :: (bifinite) po
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

typedef 'a defl = "{S::'a fin_defl set. below.ideal S}"
by (rule below.ex_ideal)

instantiation defl :: (bifinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_defl x \<subseteq> Rep_defl y"

instance ..
end

instance defl :: (bifinite) po
using type_definition_defl below_defl_def
by (rule below.typedef_ideal_po)

instance defl :: (bifinite) cpo
using type_definition_defl below_defl_def
by (rule below.typedef_ideal_cpo)

definition
  defl_principal :: "'a fin_defl \<Rightarrow> 'a defl" where
  "defl_principal t = Abs_defl {u. u \<sqsubseteq> t}"

lemma fin_defl_countable: "\<exists>f::'a fin_defl \<Rightarrow> nat. inj f"
proof -
  obtain f :: "'a compact_basis \<Rightarrow> nat" where inj_f: "inj f"
    using compact_basis.countable ..
  have *: "\<And>d. finite (f ` Rep_compact_basis -` {x. Rep_fin_defl d\<cdot>x = x})"
    apply (rule finite_imageI)
    apply (rule finite_vimageI)
    apply (rule Rep_fin_defl.finite_fixes)
    apply (simp add: inj_on_def Rep_compact_basis_inject)
    done
  have range_eq: "range Rep_compact_basis = {x. compact x}"
    using type_definition_compact_basis by (rule type_definition.Rep_range)
  have "inj (\<lambda>d. set_encode
    (f ` Rep_compact_basis -` {x. Rep_fin_defl d\<cdot>x = x}))"
    apply (rule inj_onI)
    apply (simp only: set_encode_eq *)
    apply (simp only: inj_image_eq_iff inj_f)
    apply (drule_tac f="image Rep_compact_basis" in arg_cong)
    apply (simp del: vimage_Collect_eq add: range_eq set_eq_iff)
    apply (rule Rep_fin_defl_inject [THEN iffD1])
    apply (rule below_antisym)
    apply (rule Rep_fin_defl.compact_belowI, rename_tac z)
    apply (drule_tac x=z in spec, simp)
    apply (rule Rep_fin_defl.compact_belowI, rename_tac z)
    apply (drule_tac x=z in spec, simp)
    done
  thus ?thesis by - (rule exI)
qed

interpretation defl: ideal_completion below defl_principal Rep_defl
using type_definition_defl below_defl_def
using defl_principal_def fin_defl_countable
by (rule below.typedef_ideal_completion)

text {* Algebraic deflations are pointed *}

lemma defl_minimal: "defl_principal (Abs_fin_defl \<bottom>) \<sqsubseteq> x"
apply (induct x rule: defl.principal_induct, simp)
apply (rule defl.principal_mono)
apply (simp add: below_fin_defl_def)
apply (simp add: Abs_fin_defl_inverse finite_deflation_bottom)
done

instance defl :: (bifinite) pcpo
by intro_classes (fast intro: defl_minimal)

lemma inst_defl_pcpo: "\<bottom> = defl_principal (Abs_fin_defl \<bottom>)"
by (rule defl_minimal [THEN bottomI, symmetric])

subsection {* Applying algebraic deflations *}

definition
  cast :: "'a defl \<rightarrow> 'a \<rightarrow> 'a"
where
  "cast = defl.extension Rep_fin_defl"

lemma cast_defl_principal:
  "cast\<cdot>(defl_principal a) = Rep_fin_defl a"
unfolding cast_def
apply (rule defl.extension_principal)
apply (simp only: below_fin_defl_def)
done

lemma deflation_cast: "deflation (cast\<cdot>d)"
apply (induct d rule: defl.principal_induct)
apply (rule adm_subst [OF _ adm_deflation], simp)
apply (simp add: cast_defl_principal)
apply (rule finite_deflation_imp_deflation)
apply (rule finite_deflation_Rep_fin_defl)
done

lemma finite_deflation_cast:
  "compact d \<Longrightarrow> finite_deflation (cast\<cdot>d)"
apply (drule defl.compact_imp_principal, clarify)
apply (simp add: cast_defl_principal)
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
apply (induct A rule: defl.principal_induct, simp)
apply (induct B rule: defl.principal_induct, simp)
apply (simp add: cast_defl_principal below_fin_defl_def)
done

lemma compact_cast_iff: "compact (cast\<cdot>d) \<longleftrightarrow> compact d"
apply (rule iffI)
apply (simp only: compact_def cast_below_cast [symmetric])
apply (erule adm_subst [OF cont_Rep_cfun2])
apply (erule compact_cast)
done

lemma cast_below_imp_below: "cast\<cdot>A \<sqsubseteq> cast\<cdot>B \<Longrightarrow> A \<sqsubseteq> B"
by (simp only: cast_below_cast)

lemma cast_eq_imp_eq: "cast\<cdot>A = cast\<cdot>B \<Longrightarrow> A = B"
by (simp add: below_antisym cast_below_imp_below)

lemma cast_strict1 [simp]: "cast\<cdot>\<bottom> = \<bottom>"
apply (subst inst_defl_pcpo)
apply (subst cast_defl_principal)
apply (rule Abs_fin_defl_inverse)
apply (simp add: finite_deflation_bottom)
done

lemma cast_strict2 [simp]: "cast\<cdot>A\<cdot>\<bottom> = \<bottom>"
by (rule cast.below [THEN bottomI])

subsection {* Deflation combinators *}

definition
  "defl_fun1 e p f =
    defl.extension (\<lambda>a.
      defl_principal (Abs_fin_defl
        (e oo f\<cdot>(Rep_fin_defl a) oo p)))"

definition
  "defl_fun2 e p f =
    defl.extension (\<lambda>a.
      defl.extension (\<lambda>b.
        defl_principal (Abs_fin_defl
          (e oo f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo p))))"

lemma cast_defl_fun1:
  assumes ep: "ep_pair e p"
  assumes f: "\<And>a. finite_deflation a \<Longrightarrow> finite_deflation (f\<cdot>a)"
  shows "cast\<cdot>(defl_fun1 e p f\<cdot>A) = e oo f\<cdot>(cast\<cdot>A) oo p"
proof -
  have 1: "\<And>a. finite_deflation (e oo f\<cdot>(Rep_fin_defl a) oo p)"
    apply (rule ep_pair.finite_deflation_e_d_p [OF ep])
    apply (rule f, rule finite_deflation_Rep_fin_defl)
    done
  show ?thesis
    by (induct A rule: defl.principal_induct, simp)
       (simp only: defl_fun1_def
                   defl.extension_principal
                   defl.extension_mono
                   defl.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_defl_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

lemma cast_defl_fun2:
  assumes ep: "ep_pair e p"
  assumes f: "\<And>a b. finite_deflation a \<Longrightarrow> finite_deflation b \<Longrightarrow>
                finite_deflation (f\<cdot>a\<cdot>b)"
  shows "cast\<cdot>(defl_fun2 e p f\<cdot>A\<cdot>B) = e oo f\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo p"
proof -
  have 1: "\<And>a b. finite_deflation
      (e oo f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo p)"
    apply (rule ep_pair.finite_deflation_e_d_p [OF ep])
    apply (rule f, (rule finite_deflation_Rep_fin_defl)+)
    done
  show ?thesis
    apply (induct A rule: defl.principal_induct, simp)
    apply (induct B rule: defl.principal_induct, simp)
    by (simp only: defl_fun2_def
                   defl.extension_principal
                   defl.extension_mono
                   defl.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_defl_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

end
