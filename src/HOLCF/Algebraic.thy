(*  Title:      HOLCF/Algebraic.thy
    Author:     Brian Huffman
*)

header {* Algebraic deflations and SFP domains *}

theory Algebraic
imports Universal Bifinite
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

lemma Rep_sfp_lub:
  "chain Y \<Longrightarrow> Rep_sfp (\<Squnion>i. Y i) = (\<Union>i. Rep_sfp (Y i))"
using type_definition_sfp below_sfp_def
by (rule below.typedef_ideal_rep_contlub)

lemma ideal_Rep_sfp: "below.ideal (Rep_sfp xs)"
by (rule Rep_sfp [unfolded mem_Collect_eq])

definition
  sfp_principal :: "fin_defl \<Rightarrow> sfp" where
  "sfp_principal t = Abs_sfp {u. u \<sqsubseteq> t}"

lemma Rep_sfp_principal:
  "Rep_sfp (sfp_principal t) = {u. u \<sqsubseteq> t}"
unfolding sfp_principal_def
by (simp add: Abs_sfp_inverse below.ideal_principal)

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
apply default
apply (rule ideal_Rep_sfp)
apply (erule Rep_sfp_lub)
apply (rule Rep_sfp_principal)
apply (simp only: below_sfp_def)
apply (rule fin_defl_countable)
done

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

subsection {* Class of SFP domains *}

text {*
  We define a SFP domain as a pcpo that is isomorphic to some
  algebraic deflation over the universal domain.
*}

class sfp = pcpo +
  fixes emb :: "'a::pcpo \<rightarrow> udom"
  fixes prj :: "udom \<rightarrow> 'a::pcpo"
  fixes sfp :: "'a itself \<Rightarrow> sfp"
  assumes ep_pair_emb_prj: "ep_pair emb prj"
  assumes cast_SFP: "cast\<cdot>(sfp TYPE('a)) = emb oo prj"

syntax "_SFP" :: "type \<Rightarrow> sfp"  ("(1SFP/(1'(_')))")
translations "SFP('t)" \<rightleftharpoons> "CONST sfp TYPE('t)"

interpretation sfp:
  pcpo_ep_pair "emb :: 'a::sfp \<rightarrow> udom" "prj :: udom \<rightarrow> 'a::sfp"
  unfolding pcpo_ep_pair_def
  by (rule ep_pair_emb_prj)

lemmas emb_inverse = sfp.e_inverse
lemmas emb_prj_below = sfp.e_p_below
lemmas emb_eq_iff = sfp.e_eq_iff
lemmas emb_strict = sfp.e_strict
lemmas prj_strict = sfp.p_strict

subsection {* SFP domains have a countable compact basis *}

text {*
  Eventually it should be possible to generalize this to an unpointed
  variant of the sfp class.
*}

interpretation compact_basis:
  ideal_completion below Rep_compact_basis "approximants::'a::sfp \<Rightarrow> _"
proof -
  obtain Y where Y: "\<forall>i. Y i \<sqsubseteq> Y (Suc i)"
  and SFP: "SFP('a) = (\<Squnion>i. sfp_principal (Y i))"
    by (rule sfp.obtain_principal_chain)
  def approx \<equiv> "\<lambda>i. (prj oo cast\<cdot>(sfp_principal (Y i)) oo emb) :: 'a \<rightarrow> 'a"
  interpret sfp_approx: approx_chain approx
  proof (rule approx_chain.intro)
    show "chain (\<lambda>i. approx i)"
      unfolding approx_def by (simp add: Y)
    show "(\<Squnion>i. approx i) = ID"
      unfolding approx_def
      by (simp add: lub_distribs Y SFP [symmetric] cast_SFP expand_cfun_eq)
    show "\<And>i. finite_deflation (approx i)"
      unfolding approx_def
      apply (rule sfp.finite_deflation_p_d_e)
      apply (rule finite_deflation_cast)
      apply (rule sfp.compact_principal)
      apply (rule below_trans [OF monofun_cfun_fun])
      apply (rule is_ub_thelub, simp add: Y)
      apply (simp add: lub_distribs Y SFP [symmetric] cast_SFP)
      done
  qed
  (* FIXME: why does show ?thesis fail here? *)
  show "ideal_completion below Rep_compact_basis (approximants::'a \<Rightarrow> _)" ..
qed

subsection {* Type combinators *}

definition
  sfp_fun1 ::
    "(nat \<Rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> ((udom \<rightarrow> udom) \<rightarrow> ('a \<rightarrow> 'a)) \<Rightarrow> (sfp \<rightarrow> sfp)"
where
  "sfp_fun1 approx f =
    sfp.basis_fun (\<lambda>a.
      sfp_principal (Abs_fin_defl
        (udom_emb approx oo f\<cdot>(Rep_fin_defl a) oo udom_prj approx)))"

definition
  sfp_fun2 ::
    "(nat \<Rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> ((udom \<rightarrow> udom) \<rightarrow> (udom \<rightarrow> udom) \<rightarrow> ('a \<rightarrow> 'a))
      \<Rightarrow> (sfp \<rightarrow> sfp \<rightarrow> sfp)"
where
  "sfp_fun2 approx f =
    sfp.basis_fun (\<lambda>a.
      sfp.basis_fun (\<lambda>b.
        sfp_principal (Abs_fin_defl
          (udom_emb approx oo
            f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo udom_prj approx))))"

lemma cast_sfp_fun1:
  assumes approx: "approx_chain approx"
  assumes f: "\<And>a. finite_deflation a \<Longrightarrow> finite_deflation (f\<cdot>a)"
  shows "cast\<cdot>(sfp_fun1 approx f\<cdot>A) = udom_emb approx oo f\<cdot>(cast\<cdot>A) oo udom_prj approx"
proof -
  have 1: "\<And>a. finite_deflation
        (udom_emb approx oo f\<cdot>(Rep_fin_defl a) oo udom_prj approx)"
    apply (rule ep_pair.finite_deflation_e_d_p)
    apply (rule approx_chain.ep_pair_udom [OF approx])
    apply (rule f, rule finite_deflation_Rep_fin_defl)
    done
  show ?thesis
    by (induct A rule: sfp.principal_induct, simp)
       (simp only: sfp_fun1_def
                   sfp.basis_fun_principal
                   sfp.basis_fun_mono
                   sfp.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_sfp_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

lemma cast_sfp_fun2:
  assumes approx: "approx_chain approx"
  assumes f: "\<And>a b. finite_deflation a \<Longrightarrow> finite_deflation b \<Longrightarrow>
                finite_deflation (f\<cdot>a\<cdot>b)"
  shows "cast\<cdot>(sfp_fun2 approx f\<cdot>A\<cdot>B) =
    udom_emb approx oo f\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj approx"
proof -
  have 1: "\<And>a b. finite_deflation (udom_emb approx oo
      f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo udom_prj approx)"
    apply (rule ep_pair.finite_deflation_e_d_p)
    apply (rule ep_pair_udom [OF approx])
    apply (rule f, (rule finite_deflation_Rep_fin_defl)+)
    done
  show ?thesis
    by (induct A B rule: sfp.principal_induct2, simp, simp)
       (simp only: sfp_fun2_def
                   sfp.basis_fun_principal
                   sfp.basis_fun_mono
                   sfp.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_sfp_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

subsection {* Instance for universal domain type *}

instantiation udom :: sfp
begin

definition [simp]:
  "emb = (ID :: udom \<rightarrow> udom)"

definition [simp]:
  "prj = (ID :: udom \<rightarrow> udom)"

definition
  "sfp (t::udom itself) = (\<Squnion>i. sfp_principal (Abs_fin_defl (udom_approx i)))"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> udom)"
    by (simp add: ep_pair.intro)
next
  show "cast\<cdot>SFP(udom) = emb oo (prj :: udom \<rightarrow> udom)"
    unfolding sfp_udom_def
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule sfp.principal_mono)
    apply (simp add: below_fin_defl_def)
    apply (simp add: Abs_fin_defl_inverse finite_deflation_udom_approx)
    apply (rule chainE)
    apply (rule chain_udom_approx)
    apply (subst cast_sfp_principal)
    apply (simp add: Abs_fin_defl_inverse finite_deflation_udom_approx)
    done
qed

end

subsection {* Instance for continuous function space *}

definition
  cfun_approx :: "nat \<Rightarrow> (udom \<rightarrow> udom) \<rightarrow> (udom \<rightarrow> udom)"
where
  "cfun_approx = (\<lambda>i. cfun_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma cfun_approx: "approx_chain cfun_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. cfun_approx i)"
    unfolding cfun_approx_def by simp
  show "(\<Squnion>i. cfun_approx i) = ID"
    unfolding cfun_approx_def
    by (simp add: lub_distribs cfun_map_ID)
  show "\<And>i. finite_deflation (cfun_approx i)"
    unfolding cfun_approx_def
    by (intro finite_deflation_cfun_map finite_deflation_udom_approx)
qed

definition cfun_sfp :: "sfp \<rightarrow> sfp \<rightarrow> sfp"
where "cfun_sfp = sfp_fun2 cfun_approx cfun_map"

lemma cast_cfun_sfp:
  "cast\<cdot>(cfun_sfp\<cdot>A\<cdot>B) =
    udom_emb cfun_approx oo cfun_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj cfun_approx"
unfolding cfun_sfp_def
apply (rule cast_sfp_fun2 [OF cfun_approx])
apply (erule (1) finite_deflation_cfun_map)
done

instantiation cfun :: (sfp, sfp) sfp
begin

definition
  "emb = udom_emb cfun_approx oo cfun_map\<cdot>prj\<cdot>emb"

definition
  "prj = cfun_map\<cdot>emb\<cdot>prj oo udom_prj cfun_approx"

definition
  "sfp (t::('a \<rightarrow> 'b) itself) = cfun_sfp\<cdot>SFP('a)\<cdot>SFP('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<rightarrow> 'b)"
    unfolding emb_cfun_def prj_cfun_def
    using ep_pair_udom [OF cfun_approx]
    by (intro ep_pair_comp ep_pair_cfun_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a \<rightarrow> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<rightarrow> 'b)"
    unfolding emb_cfun_def prj_cfun_def sfp_cfun_def cast_cfun_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq cfun_map_map)
qed

end

lemma SFP_cfun: "SFP('a::sfp \<rightarrow> 'b::sfp) = cfun_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_cfun_def)

end
