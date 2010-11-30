(*  Title:      HOLCF/Bifinite.thy
    Author:     Brian Huffman
*)

header {* Bifinite domains *}

theory Bifinite
imports Algebraic Map_Functions Countable
begin

subsection {* Class of bifinite domains *}

text {*
  We define a ``domain'' as a pcpo that is isomorphic to some
  algebraic deflation over the universal domain; this is equivalent
  to being omega-bifinite.

  A predomain is a cpo that, when lifted, becomes a domain.
*}

class predomain = cpo +
  fixes liftdefl :: "('a::cpo) itself \<Rightarrow> defl"
  fixes liftemb :: "'a\<^sub>\<bottom> \<rightarrow> udom"
  fixes liftprj :: "udom \<rightarrow> 'a\<^sub>\<bottom>"
  assumes predomain_ep: "ep_pair liftemb liftprj"
  assumes cast_liftdefl: "cast\<cdot>(liftdefl TYPE('a::cpo)) = liftemb oo liftprj"

syntax "_LIFTDEFL" :: "type \<Rightarrow> logic"  ("(1LIFTDEFL/(1'(_')))")
translations "LIFTDEFL('t)" \<rightleftharpoons> "CONST liftdefl TYPE('t)"

class "domain" = predomain + pcpo +
  fixes emb :: "'a::cpo \<rightarrow> udom"
  fixes prj :: "udom \<rightarrow> 'a::cpo"
  fixes defl :: "'a itself \<Rightarrow> defl"
  assumes ep_pair_emb_prj: "ep_pair emb prj"
  assumes cast_DEFL: "cast\<cdot>(defl TYPE('a)) = emb oo prj"

syntax "_DEFL" :: "type \<Rightarrow> defl"  ("(1DEFL/(1'(_')))")
translations "DEFL('t)" \<rightleftharpoons> "CONST defl TYPE('t)"

interpretation "domain": pcpo_ep_pair emb prj
  unfolding pcpo_ep_pair_def
  by (rule ep_pair_emb_prj)

lemmas emb_inverse = domain.e_inverse
lemmas emb_prj_below = domain.e_p_below
lemmas emb_eq_iff = domain.e_eq_iff
lemmas emb_strict = domain.e_strict
lemmas prj_strict = domain.p_strict

subsection {* Domains have a countable compact basis *}

text {*
  Eventually it should be possible to generalize this to an unpointed
  variant of the domain class.
*}

interpretation compact_basis:
  ideal_completion below Rep_compact_basis "approximants::'a::domain \<Rightarrow> _"
proof -
  obtain Y where Y: "\<forall>i. Y i \<sqsubseteq> Y (Suc i)"
  and DEFL: "DEFL('a) = (\<Squnion>i. defl_principal (Y i))"
    by (rule defl.obtain_principal_chain)
  def approx \<equiv> "\<lambda>i. (prj oo cast\<cdot>(defl_principal (Y i)) oo emb) :: 'a \<rightarrow> 'a"
  interpret defl_approx: approx_chain approx
  proof (rule approx_chain.intro)
    show "chain (\<lambda>i. approx i)"
      unfolding approx_def by (simp add: Y)
    show "(\<Squnion>i. approx i) = ID"
      unfolding approx_def
      by (simp add: lub_distribs Y DEFL [symmetric] cast_DEFL cfun_eq_iff)
    show "\<And>i. finite_deflation (approx i)"
      unfolding approx_def
      apply (rule domain.finite_deflation_p_d_e)
      apply (rule finite_deflation_cast)
      apply (rule defl.compact_principal)
      apply (rule below_trans [OF monofun_cfun_fun])
      apply (rule is_ub_thelub, simp add: Y)
      apply (simp add: lub_distribs Y DEFL [symmetric] cast_DEFL)
      done
  qed
  (* FIXME: why does show ?thesis fail here? *)
  show "ideal_completion below Rep_compact_basis (approximants::'a \<Rightarrow> _)" ..
qed

subsection {* Chains of approx functions *}

definition u_approx :: "nat \<Rightarrow> udom\<^sub>\<bottom> \<rightarrow> udom\<^sub>\<bottom>"
  where "u_approx = (\<lambda>i. u_map\<cdot>(udom_approx i))"

definition sfun_approx :: "nat \<Rightarrow> (udom \<rightarrow>! udom) \<rightarrow> (udom \<rightarrow>! udom)"
  where "sfun_approx = (\<lambda>i. sfun_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

definition prod_approx :: "nat \<Rightarrow> udom \<times> udom \<rightarrow> udom \<times> udom"
  where "prod_approx = (\<lambda>i. cprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

definition sprod_approx :: "nat \<Rightarrow> udom \<otimes> udom \<rightarrow> udom \<otimes> udom"
  where "sprod_approx = (\<lambda>i. sprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

definition ssum_approx :: "nat \<Rightarrow> udom \<oplus> udom \<rightarrow> udom \<oplus> udom"
  where "ssum_approx = (\<lambda>i. ssum_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma approx_chain_lemma1:
  assumes "m\<cdot>ID = ID"
  assumes "\<And>d. finite_deflation d \<Longrightarrow> finite_deflation (m\<cdot>d)"
  shows "approx_chain (\<lambda>i. m\<cdot>(udom_approx i))"
by (rule approx_chain.intro)
   (simp_all add: lub_distribs finite_deflation_udom_approx assms)

lemma approx_chain_lemma2:
  assumes "m\<cdot>ID\<cdot>ID = ID"
  assumes "\<And>a b. \<lbrakk>finite_deflation a; finite_deflation b\<rbrakk>
    \<Longrightarrow> finite_deflation (m\<cdot>a\<cdot>b)"
  shows "approx_chain (\<lambda>i. m\<cdot>(udom_approx i)\<cdot>(udom_approx i))"
by (rule approx_chain.intro)
   (simp_all add: lub_distribs finite_deflation_udom_approx assms)

lemma u_approx: "approx_chain u_approx"
using u_map_ID finite_deflation_u_map
unfolding u_approx_def by (rule approx_chain_lemma1)

lemma sfun_approx: "approx_chain sfun_approx"
using sfun_map_ID finite_deflation_sfun_map
unfolding sfun_approx_def by (rule approx_chain_lemma2)

lemma prod_approx: "approx_chain prod_approx"
using cprod_map_ID finite_deflation_cprod_map
unfolding prod_approx_def by (rule approx_chain_lemma2)

lemma sprod_approx: "approx_chain sprod_approx"
using sprod_map_ID finite_deflation_sprod_map
unfolding sprod_approx_def by (rule approx_chain_lemma2)

lemma ssum_approx: "approx_chain ssum_approx"
using ssum_map_ID finite_deflation_ssum_map
unfolding ssum_approx_def by (rule approx_chain_lemma2)

subsection {* Type combinators *}

definition
  defl_fun1 ::
    "(nat \<Rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> ((udom \<rightarrow> udom) \<rightarrow> ('a \<rightarrow> 'a)) \<Rightarrow> (defl \<rightarrow> defl)"
where
  "defl_fun1 approx f =
    defl.basis_fun (\<lambda>a.
      defl_principal (Abs_fin_defl
        (udom_emb approx oo f\<cdot>(Rep_fin_defl a) oo udom_prj approx)))"

definition
  defl_fun2 ::
    "(nat \<Rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> ((udom \<rightarrow> udom) \<rightarrow> (udom \<rightarrow> udom) \<rightarrow> ('a \<rightarrow> 'a))
      \<Rightarrow> (defl \<rightarrow> defl \<rightarrow> defl)"
where
  "defl_fun2 approx f =
    defl.basis_fun (\<lambda>a.
      defl.basis_fun (\<lambda>b.
        defl_principal (Abs_fin_defl
          (udom_emb approx oo
            f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo udom_prj approx))))"

lemma cast_defl_fun1:
  assumes approx: "approx_chain approx"
  assumes f: "\<And>a. finite_deflation a \<Longrightarrow> finite_deflation (f\<cdot>a)"
  shows "cast\<cdot>(defl_fun1 approx f\<cdot>A) = udom_emb approx oo f\<cdot>(cast\<cdot>A) oo udom_prj approx"
proof -
  have 1: "\<And>a. finite_deflation
        (udom_emb approx oo f\<cdot>(Rep_fin_defl a) oo udom_prj approx)"
    apply (rule ep_pair.finite_deflation_e_d_p)
    apply (rule approx_chain.ep_pair_udom [OF approx])
    apply (rule f, rule finite_deflation_Rep_fin_defl)
    done
  show ?thesis
    by (induct A rule: defl.principal_induct, simp)
       (simp only: defl_fun1_def
                   defl.basis_fun_principal
                   defl.basis_fun_mono
                   defl.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_defl_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

lemma cast_defl_fun2:
  assumes approx: "approx_chain approx"
  assumes f: "\<And>a b. finite_deflation a \<Longrightarrow> finite_deflation b \<Longrightarrow>
                finite_deflation (f\<cdot>a\<cdot>b)"
  shows "cast\<cdot>(defl_fun2 approx f\<cdot>A\<cdot>B) =
    udom_emb approx oo f\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj approx"
proof -
  have 1: "\<And>a b. finite_deflation (udom_emb approx oo
      f\<cdot>(Rep_fin_defl a)\<cdot>(Rep_fin_defl b) oo udom_prj approx)"
    apply (rule ep_pair.finite_deflation_e_d_p)
    apply (rule ep_pair_udom [OF approx])
    apply (rule f, (rule finite_deflation_Rep_fin_defl)+)
    done
  show ?thesis
    by (induct A B rule: defl.principal_induct2, simp, simp)
       (simp only: defl_fun2_def
                   defl.basis_fun_principal
                   defl.basis_fun_mono
                   defl.principal_mono
                   Abs_fin_defl_mono [OF 1 1]
                   monofun_cfun below_refl
                   Rep_fin_defl_mono
                   cast_defl_principal
                   Abs_fin_defl_inverse [unfolded mem_Collect_eq, OF 1])
qed

definition u_defl :: "defl \<rightarrow> defl"
  where "u_defl = defl_fun1 u_approx u_map"

definition sfun_defl :: "defl \<rightarrow> defl \<rightarrow> defl"
  where "sfun_defl = defl_fun2 sfun_approx sfun_map"

definition prod_defl :: "defl \<rightarrow> defl \<rightarrow> defl"
  where "prod_defl = defl_fun2 prod_approx cprod_map"

definition sprod_defl :: "defl \<rightarrow> defl \<rightarrow> defl"
  where "sprod_defl = defl_fun2 sprod_approx sprod_map"

definition ssum_defl :: "defl \<rightarrow> defl \<rightarrow> defl"
where "ssum_defl = defl_fun2 ssum_approx ssum_map"

lemma cast_u_defl:
  "cast\<cdot>(u_defl\<cdot>A) =
    udom_emb u_approx oo u_map\<cdot>(cast\<cdot>A) oo udom_prj u_approx"
using u_approx finite_deflation_u_map
unfolding u_defl_def by (rule cast_defl_fun1)

lemma cast_sfun_defl:
  "cast\<cdot>(sfun_defl\<cdot>A\<cdot>B) =
    udom_emb sfun_approx oo sfun_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj sfun_approx"
using sfun_approx finite_deflation_sfun_map
unfolding sfun_defl_def by (rule cast_defl_fun2)

lemma cast_prod_defl:
  "cast\<cdot>(prod_defl\<cdot>A\<cdot>B) = udom_emb prod_approx oo
    cprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj prod_approx"
using prod_approx finite_deflation_cprod_map
unfolding prod_defl_def by (rule cast_defl_fun2)

lemma cast_sprod_defl:
  "cast\<cdot>(sprod_defl\<cdot>A\<cdot>B) =
    udom_emb sprod_approx oo
      sprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo
        udom_prj sprod_approx"
using sprod_approx finite_deflation_sprod_map
unfolding sprod_defl_def by (rule cast_defl_fun2)

lemma cast_ssum_defl:
  "cast\<cdot>(ssum_defl\<cdot>A\<cdot>B) =
    udom_emb ssum_approx oo ssum_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj ssum_approx"
using ssum_approx finite_deflation_ssum_map
unfolding ssum_defl_def by (rule cast_defl_fun2)

subsection {* Lemma for proving domain instances *}

text {*
  A class of domains where @{const liftemb}, @{const liftprj},
  and @{const liftdefl} are all defined in the standard way.
*}

class liftdomain = "domain" +
  assumes liftemb_eq: "liftemb = udom_emb u_approx oo u_map\<cdot>emb"
  assumes liftprj_eq: "liftprj = u_map\<cdot>prj oo udom_prj u_approx"
  assumes liftdefl_eq: "liftdefl TYPE('a::cpo) = u_defl\<cdot>DEFL('a)"

text {* Temporarily relax type constraints. *}

setup {*
  fold Sign.add_const_constraint
  [ (@{const_name defl}, SOME @{typ "'a::pcpo itself \<Rightarrow> defl"})
  , (@{const_name emb}, SOME @{typ "'a::pcpo \<rightarrow> udom"})
  , (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::pcpo"})
  , (@{const_name liftdefl}, SOME @{typ "'a::pcpo itself \<Rightarrow> defl"})
  , (@{const_name liftemb}, SOME @{typ "'a::pcpo u \<rightarrow> udom"})
  , (@{const_name liftprj}, SOME @{typ "udom \<rightarrow> 'a::pcpo u"}) ]
*}

lemma liftdomain_class_intro:
  assumes liftemb: "(liftemb :: 'a u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"
  assumes liftprj: "(liftprj :: udom \<rightarrow> 'a u) = u_map\<cdot>prj oo udom_prj u_approx"
  assumes liftdefl: "liftdefl TYPE('a) = u_defl\<cdot>DEFL('a)"
  assumes ep_pair: "ep_pair emb (prj :: udom \<rightarrow> 'a)"
  assumes cast_defl: "cast\<cdot>DEFL('a) = emb oo (prj :: udom \<rightarrow> 'a)"
  shows "OFCLASS('a, liftdomain_class)"
proof
  show "ep_pair liftemb (liftprj :: udom \<rightarrow> 'a u)"
    unfolding liftemb liftprj
    by (intro ep_pair_comp ep_pair_u_map ep_pair ep_pair_udom u_approx)
  show "cast\<cdot>LIFTDEFL('a) = liftemb oo (liftprj :: udom \<rightarrow> 'a u)"
    unfolding liftemb liftprj liftdefl
    by (simp add: cfcomp1 cast_u_defl cast_defl u_map_map)
next
qed fact+

text {* Restore original type constraints. *}

setup {*
  fold Sign.add_const_constraint
  [ (@{const_name defl}, SOME @{typ "'a::domain itself \<Rightarrow> defl"})
  , (@{const_name emb}, SOME @{typ "'a::domain \<rightarrow> udom"})
  , (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::domain"})
  , (@{const_name liftdefl}, SOME @{typ "'a::predomain itself \<Rightarrow> defl"})
  , (@{const_name liftemb}, SOME @{typ "'a::predomain u \<rightarrow> udom"})
  , (@{const_name liftprj}, SOME @{typ "udom \<rightarrow> 'a::predomain u"}) ]
*}

subsection {* Class instance proofs *}

subsubsection {* Universal domain *}

instantiation udom :: liftdomain
begin

definition [simp]:
  "emb = (ID :: udom \<rightarrow> udom)"

definition [simp]:
  "prj = (ID :: udom \<rightarrow> udom)"

definition
  "defl (t::udom itself) = (\<Squnion>i. defl_principal (Abs_fin_defl (udom_approx i)))"

definition
  "(liftemb :: udom u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> udom u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::udom itself) = u_defl\<cdot>DEFL(udom)"

instance
using liftemb_udom_def liftprj_udom_def liftdefl_udom_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> udom)"
    by (simp add: ep_pair.intro)
  show "cast\<cdot>DEFL(udom) = emb oo (prj :: udom \<rightarrow> udom)"
    unfolding defl_udom_def
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule defl.principal_mono)
    apply (simp add: below_fin_defl_def)
    apply (simp add: Abs_fin_defl_inverse finite_deflation_udom_approx)
    apply (rule chainE)
    apply (rule chain_udom_approx)
    apply (subst cast_defl_principal)
    apply (simp add: Abs_fin_defl_inverse finite_deflation_udom_approx)
    done
qed

end

subsubsection {* Lifted cpo *}

instantiation u :: (predomain) liftdomain
begin

definition
  "emb = liftemb"

definition
  "prj = liftprj"

definition
  "defl (t::'a u itself) = LIFTDEFL('a)"

definition
  "(liftemb :: 'a u u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> 'a u u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::'a u itself) = u_defl\<cdot>DEFL('a u)"

instance
using liftemb_u_def liftprj_u_def liftdefl_u_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a u)"
    unfolding emb_u_def prj_u_def
    by (rule predomain_ep)
  show "cast\<cdot>DEFL('a u) = emb oo (prj :: udom \<rightarrow> 'a u)"
    unfolding emb_u_def prj_u_def defl_u_def
    by (rule cast_liftdefl)
qed

end

lemma DEFL_u: "DEFL('a::predomain u) = LIFTDEFL('a)"
by (rule defl_u_def)

subsubsection {* Strict function space *}

instantiation sfun :: ("domain", "domain") liftdomain
begin

definition
  "emb = udom_emb sfun_approx oo sfun_map\<cdot>prj\<cdot>emb"

definition
  "prj = sfun_map\<cdot>emb\<cdot>prj oo udom_prj sfun_approx"

definition
  "defl (t::('a \<rightarrow>! 'b) itself) = sfun_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<rightarrow>! 'b) u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<rightarrow>! 'b) u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::('a \<rightarrow>! 'b) itself) = u_defl\<cdot>DEFL('a \<rightarrow>! 'b)"

instance
using liftemb_sfun_def liftprj_sfun_def liftdefl_sfun_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def
    using ep_pair_udom [OF sfun_approx]
    by (intro ep_pair_comp ep_pair_sfun_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a \<rightarrow>! 'b) = emb oo (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def defl_sfun_def cast_sfun_defl
    by (simp add: cast_DEFL oo_def sfun_eq_iff sfun_map_map)
qed

end

lemma DEFL_sfun:
  "DEFL('a::domain \<rightarrow>! 'b::domain) = sfun_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_sfun_def)

subsubsection {* Continuous function space *}

text {*
  Types @{typ "'a \<rightarrow> 'b"} and @{typ "'a u \<rightarrow>! 'b"} are isomorphic.
*}

definition
  "encode_cfun = (\<Lambda> f. sfun_abs\<cdot>(fup\<cdot>f))"

definition
  "decode_cfun = (\<Lambda> g x. sfun_rep\<cdot>g\<cdot>(up\<cdot>x))"

lemma decode_encode_cfun [simp]: "decode_cfun\<cdot>(encode_cfun\<cdot>x) = x"
unfolding encode_cfun_def decode_cfun_def
by (simp add: eta_cfun)

lemma encode_decode_cfun [simp]: "encode_cfun\<cdot>(decode_cfun\<cdot>y) = y"
unfolding encode_cfun_def decode_cfun_def
apply (simp add: sfun_eq_iff strictify_cancel)
apply (rule cfun_eqI, case_tac x, simp_all)
done

instantiation cfun :: (predomain, "domain") liftdomain
begin

definition
  "emb = emb oo encode_cfun"

definition
  "prj = decode_cfun oo prj"

definition
  "defl (t::('a \<rightarrow> 'b) itself) = DEFL('a u \<rightarrow>! 'b)"

definition
  "(liftemb :: ('a \<rightarrow> 'b) u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<rightarrow> 'b) u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::('a \<rightarrow> 'b) itself) = u_defl\<cdot>DEFL('a \<rightarrow> 'b)"

instance
using liftemb_cfun_def liftprj_cfun_def liftdefl_cfun_def
proof (rule liftdomain_class_intro)
  have "ep_pair encode_cfun decode_cfun"
    by (rule ep_pair.intro, simp_all)
  thus "ep_pair emb (prj :: udom \<rightarrow> 'a \<rightarrow> 'b)"
    unfolding emb_cfun_def prj_cfun_def
    using ep_pair_emb_prj by (rule ep_pair_comp)
  show "cast\<cdot>DEFL('a \<rightarrow> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<rightarrow> 'b)"
    unfolding emb_cfun_def prj_cfun_def defl_cfun_def
    by (simp add: cast_DEFL cfcomp1)
qed

end

lemma DEFL_cfun:
  "DEFL('a::predomain \<rightarrow> 'b::domain) = DEFL('a u \<rightarrow>! 'b)"
by (rule defl_cfun_def)

subsubsection {* Strict product *}

instantiation sprod :: ("domain", "domain") liftdomain
begin

definition
  "emb = udom_emb sprod_approx oo sprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = sprod_map\<cdot>prj\<cdot>prj oo udom_prj sprod_approx"

definition
  "defl (t::('a \<otimes> 'b) itself) = sprod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<otimes> 'b) u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<otimes> 'b) u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::('a \<otimes> 'b) itself) = u_defl\<cdot>DEFL('a \<otimes> 'b)"

instance
using liftemb_sprod_def liftprj_sprod_def liftdefl_sprod_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<otimes> 'b)"
    unfolding emb_sprod_def prj_sprod_def
    using ep_pair_udom [OF sprod_approx]
    by (intro ep_pair_comp ep_pair_sprod_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a \<otimes> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<otimes> 'b)"
    unfolding emb_sprod_def prj_sprod_def defl_sprod_def cast_sprod_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff sprod_map_map)
qed

end

lemma DEFL_sprod:
  "DEFL('a::domain \<otimes> 'b::domain) = sprod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_sprod_def)

subsubsection {* Cartesian product *}

text {*
  Types @{typ "('a * 'b) u"} and @{typ "'a u \<otimes> 'b u"} are isomorphic.
*}

definition
  "encode_prod_u = (\<Lambda>(up\<cdot>(x, y)). (:up\<cdot>x, up\<cdot>y:))"

definition
  "decode_prod_u = (\<Lambda>(:up\<cdot>x, up\<cdot>y:). up\<cdot>(x, y))"

lemma decode_encode_prod_u [simp]: "decode_prod_u\<cdot>(encode_prod_u\<cdot>x) = x"
unfolding encode_prod_u_def decode_prod_u_def
by (case_tac x, simp, rename_tac y, case_tac y, simp)

lemma encode_decode_prod_u [simp]: "encode_prod_u\<cdot>(decode_prod_u\<cdot>y) = y"
unfolding encode_prod_u_def decode_prod_u_def
apply (case_tac y, simp, rename_tac a b)
apply (case_tac a, simp, case_tac b, simp, simp)
done

instantiation prod :: (predomain, predomain) predomain
begin

definition
  "liftemb = emb oo encode_prod_u"

definition
  "liftprj = decode_prod_u oo prj"

definition
  "liftdefl (t::('a \<times> 'b) itself) = DEFL('a\<^sub>\<bottom> \<otimes> 'b\<^sub>\<bottom>)"

instance proof
  have "ep_pair encode_prod_u decode_prod_u"
    by (rule ep_pair.intro, simp_all)
  thus "ep_pair liftemb (liftprj :: udom \<rightarrow> ('a \<times> 'b) u)"
    unfolding liftemb_prod_def liftprj_prod_def
    using ep_pair_emb_prj by (rule ep_pair_comp)
  show "cast\<cdot>LIFTDEFL('a \<times> 'b) = liftemb oo (liftprj :: udom \<rightarrow> ('a \<times> 'b) u)"
    unfolding liftemb_prod_def liftprj_prod_def liftdefl_prod_def
    by (simp add: cast_DEFL cfcomp1)
qed

end

instantiation prod :: ("domain", "domain") "domain"
begin

definition
  "emb = udom_emb prod_approx oo cprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = cprod_map\<cdot>prj\<cdot>prj oo udom_prj prod_approx"

definition
  "defl (t::('a \<times> 'b) itself) = prod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def
    using ep_pair_udom [OF prod_approx]
    by (intro ep_pair_comp ep_pair_cprod_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a \<times> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def defl_prod_def cast_prod_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff cprod_map_map)
qed

end

lemma DEFL_prod:
  "DEFL('a::domain \<times> 'b::domain) = prod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_prod_def)

lemma LIFTDEFL_prod:
  "LIFTDEFL('a::predomain \<times> 'b::predomain) = DEFL('a u \<otimes> 'b u)"
by (rule liftdefl_prod_def)

subsubsection {* Discrete cpo *}

definition discr_approx :: "nat \<Rightarrow> 'a::countable discr u \<rightarrow> 'a discr u"
  where "discr_approx = (\<lambda>i. \<Lambda>(up\<cdot>x). if to_nat (undiscr x) < i then up\<cdot>x else \<bottom>)"

lemma chain_discr_approx [simp]: "chain discr_approx"
unfolding discr_approx_def
by (rule chainI, simp add: monofun_cfun monofun_LAM)

lemma lub_discr_approx [simp]: "(\<Squnion>i. discr_approx i) = ID"
apply (rule cfun_eqI)
apply (simp add: contlub_cfun_fun)
apply (simp add: discr_approx_def)
apply (case_tac x, simp)
apply (rule lub_eqI)
apply (rule is_lubI)
apply (rule ub_rangeI, simp)
apply (drule ub_rangeD)
apply (erule rev_below_trans)
apply simp
apply (rule lessI)
done

lemma inj_on_undiscr [simp]: "inj_on undiscr A"
using Discr_undiscr by (rule inj_on_inverseI)

lemma finite_deflation_discr_approx: "finite_deflation (discr_approx i)"
proof
  fix x :: "'a discr u"
  show "discr_approx i\<cdot>x \<sqsubseteq> x"
    unfolding discr_approx_def
    by (cases x, simp, simp)
  show "discr_approx i\<cdot>(discr_approx i\<cdot>x) = discr_approx i\<cdot>x"
    unfolding discr_approx_def
    by (cases x, simp, simp)
  show "finite {x::'a discr u. discr_approx i\<cdot>x = x}"
  proof (rule finite_subset)
    let ?S = "insert (\<bottom>::'a discr u) ((\<lambda>x. up\<cdot>x) ` undiscr -` to_nat -` {..<i})"
    show "{x::'a discr u. discr_approx i\<cdot>x = x} \<subseteq> ?S"
      unfolding discr_approx_def
      by (rule subsetI, case_tac x, simp, simp split: split_if_asm)
    show "finite ?S"
      by (simp add: finite_vimageI)
  qed
qed

lemma discr_approx: "approx_chain discr_approx"
using chain_discr_approx lub_discr_approx finite_deflation_discr_approx
by (rule approx_chain.intro)

instantiation discr :: (countable) predomain
begin

definition
  "liftemb = udom_emb discr_approx"

definition
  "liftprj = udom_prj discr_approx"

definition
  "liftdefl (t::'a discr itself) =
    (\<Squnion>i. defl_principal (Abs_fin_defl (liftemb oo discr_approx i oo liftprj)))"

instance proof
  show "ep_pair liftemb (liftprj :: udom \<rightarrow> 'a discr u)"
    unfolding liftemb_discr_def liftprj_discr_def
    by (rule ep_pair_udom [OF discr_approx])
  show "cast\<cdot>LIFTDEFL('a discr) = liftemb oo (liftprj :: udom \<rightarrow> 'a discr u)"
    unfolding liftemb_discr_def liftprj_discr_def liftdefl_discr_def
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule defl.principal_mono)
    apply (simp add: below_fin_defl_def)
    apply (simp add: Abs_fin_defl_inverse
        ep_pair.finite_deflation_e_d_p [OF ep_pair_udom [OF discr_approx]]
        approx_chain.finite_deflation_approx [OF discr_approx])
    apply (intro monofun_cfun below_refl)
    apply (rule chainE)
    apply (rule chain_discr_approx)
    apply (subst cast_defl_principal)
    apply (simp add: Abs_fin_defl_inverse
        ep_pair.finite_deflation_e_d_p [OF ep_pair_udom [OF discr_approx]]
        approx_chain.finite_deflation_approx [OF discr_approx])
    apply (simp add: lub_distribs)
    done
qed

end

subsubsection {* Strict sum *}

instantiation ssum :: ("domain", "domain") liftdomain
begin

definition
  "emb = udom_emb ssum_approx oo ssum_map\<cdot>emb\<cdot>emb"

definition
  "prj = ssum_map\<cdot>prj\<cdot>prj oo udom_prj ssum_approx"

definition
  "defl (t::('a \<oplus> 'b) itself) = ssum_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<oplus> 'b) u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<oplus> 'b) u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::('a \<oplus> 'b) itself) = u_defl\<cdot>DEFL('a \<oplus> 'b)"

instance
using liftemb_ssum_def liftprj_ssum_def liftdefl_ssum_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def
    using ep_pair_udom [OF ssum_approx]
    by (intro ep_pair_comp ep_pair_ssum_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a \<oplus> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def defl_ssum_def cast_ssum_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff ssum_map_map)
qed

end

lemma DEFL_ssum:
  "DEFL('a::domain \<oplus> 'b::domain) = ssum_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_ssum_def)

subsubsection {* Lifted HOL type *}

instantiation lift :: (countable) liftdomain
begin

definition
  "emb = emb oo (\<Lambda> x. Rep_lift x)"

definition
  "prj = (\<Lambda> y. Abs_lift y) oo prj"

definition
  "defl (t::'a lift itself) = DEFL('a discr u)"

definition
  "(liftemb :: 'a lift u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> 'a lift u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::'a lift itself) = u_defl\<cdot>DEFL('a lift)"

instance
using liftemb_lift_def liftprj_lift_def liftdefl_lift_def
proof (rule liftdomain_class_intro)
  note [simp] = cont_Rep_lift cont_Abs_lift Rep_lift_inverse Abs_lift_inverse
  have "ep_pair (\<Lambda>(x::'a lift). Rep_lift x) (\<Lambda> y. Abs_lift y)"
    by (simp add: ep_pair_def)
  thus "ep_pair emb (prj :: udom \<rightarrow> 'a lift)"
    unfolding emb_lift_def prj_lift_def
    using ep_pair_emb_prj by (rule ep_pair_comp)
  show "cast\<cdot>DEFL('a lift) = emb oo (prj :: udom \<rightarrow> 'a lift)"
    unfolding emb_lift_def prj_lift_def defl_lift_def cast_DEFL
    by (simp add: cfcomp1)
qed

end

end
