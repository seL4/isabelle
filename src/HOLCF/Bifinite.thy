(*  Title:      HOLCF/Bifinite.thy
    Author:     Brian Huffman
*)

header {* Bifinite domains *}

theory Bifinite
imports Algebraic Cprod Sprod Ssum Up Lift One Tr
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

subsection {* The universal domain is bifinite *}

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

subsection {* Continuous function space is a bifinite domain *}

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

subsection {* Cartesian product is a bifinite domain *}

definition
  prod_approx :: "nat \<Rightarrow> udom \<times> udom \<rightarrow> udom \<times> udom"
where
  "prod_approx = (\<lambda>i. cprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma prod_approx: "approx_chain prod_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. prod_approx i)"
    unfolding prod_approx_def by simp
  show "(\<Squnion>i. prod_approx i) = ID"
    unfolding prod_approx_def
    by (simp add: lub_distribs cprod_map_ID)
  show "\<And>i. finite_deflation (prod_approx i)"
    unfolding prod_approx_def
    by (intro finite_deflation_cprod_map finite_deflation_udom_approx)
qed

definition prod_sfp :: "sfp \<rightarrow> sfp \<rightarrow> sfp"
where "prod_sfp = sfp_fun2 prod_approx cprod_map"

lemma cast_prod_sfp:
  "cast\<cdot>(prod_sfp\<cdot>A\<cdot>B) = udom_emb prod_approx oo
    cprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj prod_approx"
unfolding prod_sfp_def
apply (rule cast_sfp_fun2 [OF prod_approx])
apply (erule (1) finite_deflation_cprod_map)
done

instantiation prod :: (bifinite, bifinite) bifinite
begin

definition
  "emb = udom_emb prod_approx oo cprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = cprod_map\<cdot>prj\<cdot>prj oo udom_prj prod_approx"

definition
  "sfp (t::('a \<times> 'b) itself) = prod_sfp\<cdot>SFP('a)\<cdot>SFP('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def
    using ep_pair_udom [OF prod_approx]
    by (intro ep_pair_comp ep_pair_cprod_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a \<times> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def sfp_prod_def cast_prod_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq cprod_map_map)
qed

end

lemma SFP_prod:
  "SFP('a::bifinite \<times> 'b::bifinite) = prod_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_prod_def)

subsection {* Strict product is a bifinite domain *}

definition
  sprod_approx :: "nat \<Rightarrow> udom \<otimes> udom \<rightarrow> udom \<otimes> udom"
where
  "sprod_approx = (\<lambda>i. sprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma sprod_approx: "approx_chain sprod_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. sprod_approx i)"
    unfolding sprod_approx_def by simp
  show "(\<Squnion>i. sprod_approx i) = ID"
    unfolding sprod_approx_def
    by (simp add: lub_distribs sprod_map_ID)
  show "\<And>i. finite_deflation (sprod_approx i)"
    unfolding sprod_approx_def
    by (intro finite_deflation_sprod_map finite_deflation_udom_approx)
qed

definition sprod_sfp :: "sfp \<rightarrow> sfp \<rightarrow> sfp"
where "sprod_sfp = sfp_fun2 sprod_approx sprod_map"

lemma cast_sprod_sfp:
  "cast\<cdot>(sprod_sfp\<cdot>A\<cdot>B) =
    udom_emb sprod_approx oo
      sprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo
        udom_prj sprod_approx"
unfolding sprod_sfp_def
apply (rule cast_sfp_fun2 [OF sprod_approx])
apply (erule (1) finite_deflation_sprod_map)
done

instantiation sprod :: (bifinite, bifinite) bifinite
begin

definition
  "emb = udom_emb sprod_approx oo sprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = sprod_map\<cdot>prj\<cdot>prj oo udom_prj sprod_approx"

definition
  "sfp (t::('a \<otimes> 'b) itself) = sprod_sfp\<cdot>SFP('a)\<cdot>SFP('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<otimes> 'b)"
    unfolding emb_sprod_def prj_sprod_def
    using ep_pair_udom [OF sprod_approx]
    by (intro ep_pair_comp ep_pair_sprod_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a \<otimes> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<otimes> 'b)"
    unfolding emb_sprod_def prj_sprod_def sfp_sprod_def cast_sprod_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq sprod_map_map)
qed

end

lemma SFP_sprod:
  "SFP('a::bifinite \<otimes> 'b::bifinite) = sprod_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_sprod_def)

subsection {* Lifted cpo is a bifinite domain *}

definition u_approx :: "nat \<Rightarrow> udom\<^sub>\<bottom> \<rightarrow> udom\<^sub>\<bottom>"
where "u_approx = (\<lambda>i. u_map\<cdot>(udom_approx i))"

lemma u_approx: "approx_chain u_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. u_approx i)"
    unfolding u_approx_def by simp
  show "(\<Squnion>i. u_approx i) = ID"
    unfolding u_approx_def
    by (simp add: lub_distribs u_map_ID)
  show "\<And>i. finite_deflation (u_approx i)"
    unfolding u_approx_def
    by (intro finite_deflation_u_map finite_deflation_udom_approx)
qed

definition u_sfp :: "sfp \<rightarrow> sfp"
where "u_sfp = sfp_fun1 u_approx u_map"

lemma cast_u_sfp:
  "cast\<cdot>(u_sfp\<cdot>A) =
    udom_emb u_approx oo u_map\<cdot>(cast\<cdot>A) oo udom_prj u_approx"
unfolding u_sfp_def
apply (rule cast_sfp_fun1 [OF u_approx])
apply (erule finite_deflation_u_map)
done

instantiation u :: (bifinite) bifinite
begin

definition
  "emb = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "prj = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "sfp (t::'a u itself) = u_sfp\<cdot>SFP('a)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a u)"
    unfolding emb_u_def prj_u_def
    using ep_pair_udom [OF u_approx]
    by (intro ep_pair_comp ep_pair_u_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a u) = emb oo (prj :: udom \<rightarrow> 'a u)"
    unfolding emb_u_def prj_u_def sfp_u_def cast_u_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq u_map_map)
qed

end

lemma SFP_u: "SFP('a::bifinite u) = u_sfp\<cdot>SFP('a)"
by (rule sfp_u_def)

subsection {* Lifted countable types are bifinite domains *}

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

instantiation lift :: (countable) bifinite
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

subsection {* Strict sum is a bifinite domain *}

definition
  ssum_approx :: "nat \<Rightarrow> udom \<oplus> udom \<rightarrow> udom \<oplus> udom"
where
  "ssum_approx = (\<lambda>i. ssum_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma ssum_approx: "approx_chain ssum_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. ssum_approx i)"
    unfolding ssum_approx_def by simp
  show "(\<Squnion>i. ssum_approx i) = ID"
    unfolding ssum_approx_def
    by (simp add: lub_distribs ssum_map_ID)
  show "\<And>i. finite_deflation (ssum_approx i)"
    unfolding ssum_approx_def
    by (intro finite_deflation_ssum_map finite_deflation_udom_approx)
qed

definition ssum_sfp :: "sfp \<rightarrow> sfp \<rightarrow> sfp"
where "ssum_sfp = sfp_fun2 ssum_approx ssum_map"

lemma cast_ssum_sfp:
  "cast\<cdot>(ssum_sfp\<cdot>A\<cdot>B) =
    udom_emb ssum_approx oo ssum_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj ssum_approx"
unfolding ssum_sfp_def
apply (rule cast_sfp_fun2 [OF ssum_approx])
apply (erule (1) finite_deflation_ssum_map)
done

instantiation ssum :: (bifinite, bifinite) bifinite
begin

definition
  "emb = udom_emb ssum_approx oo ssum_map\<cdot>emb\<cdot>emb"

definition
  "prj = ssum_map\<cdot>prj\<cdot>prj oo udom_prj ssum_approx"

definition
  "sfp (t::('a \<oplus> 'b) itself) = ssum_sfp\<cdot>SFP('a)\<cdot>SFP('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def
    using ep_pair_udom [OF ssum_approx]
    by (intro ep_pair_comp ep_pair_ssum_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a \<oplus> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def sfp_ssum_def cast_ssum_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq ssum_map_map)
qed

end

lemma SFP_ssum:
  "SFP('a::bifinite \<oplus> 'b::bifinite) = ssum_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_ssum_def)

end
