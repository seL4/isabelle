(*  Title:      HOLCF/Bifinite.thy
    Author:     Brian Huffman
*)

header {* Bifinite domains *}

theory Bifinite
imports Algebraic
begin

subsection {* Class of bifinite domains *}

text {*
  We define a bifinite domain as a pcpo that is isomorphic to some
  algebraic deflation over the universal domain.
*}

class bifinite = pcpo +
  fixes emb :: "'a::pcpo \<rightarrow> udom"
  fixes prj :: "udom \<rightarrow> 'a::pcpo"
  fixes sfp :: "'a itself \<Rightarrow> sfp"
  assumes ep_pair_emb_prj: "ep_pair emb prj"
  assumes cast_SFP: "cast\<cdot>(sfp TYPE('a)) = emb oo prj"

syntax "_SFP" :: "type \<Rightarrow> sfp"  ("(1SFP/(1'(_')))")
translations "SFP('t)" \<rightleftharpoons> "CONST sfp TYPE('t)"

interpretation bifinite:
  pcpo_ep_pair "emb :: 'a::bifinite \<rightarrow> udom" "prj :: udom \<rightarrow> 'a::bifinite"
  unfolding pcpo_ep_pair_def
  by (rule ep_pair_emb_prj)

lemmas emb_inverse = bifinite.e_inverse
lemmas emb_prj_below = bifinite.e_p_below
lemmas emb_eq_iff = bifinite.e_eq_iff
lemmas emb_strict = bifinite.e_strict
lemmas prj_strict = bifinite.p_strict

subsection {* Bifinite domains have a countable compact basis *}

text {*
  Eventually it should be possible to generalize this to an unpointed
  variant of the bifinite class.
*}

interpretation compact_basis:
  ideal_completion below Rep_compact_basis "approximants::'a::bifinite \<Rightarrow> _"
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
      apply (rule bifinite.finite_deflation_p_d_e)
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

instantiation udom :: bifinite
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

instantiation cfun :: (bifinite, bifinite) bifinite
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

lemma SFP_cfun:
  "SFP('a::bifinite \<rightarrow> 'b::bifinite) = cfun_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_cfun_def)

end
