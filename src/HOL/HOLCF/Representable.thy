(*  Title:      HOLCF/Representable.thy
    Author:     Brian Huffman
*)

header {* Representable domains *}

theory Representable
imports Algebraic Map_Functions Countable
begin

subsection {* Class of representable domains *}

text {*
  We define a ``domain'' as a pcpo that is isomorphic to some
  algebraic deflation over the universal domain; this is equivalent
  to being omega-bifinite.

  A predomain is a cpo that, when lifted, becomes a domain.
*}

class predomain = cpo +
  fixes liftdefl :: "('a::cpo) itself \<Rightarrow> udom defl"
  fixes liftemb :: "'a\<^sub>\<bottom> \<rightarrow> udom"
  fixes liftprj :: "udom \<rightarrow> 'a\<^sub>\<bottom>"
  assumes predomain_ep: "ep_pair liftemb liftprj"
  assumes cast_liftdefl: "cast\<cdot>(liftdefl TYPE('a::cpo)) = liftemb oo liftprj"

syntax "_LIFTDEFL" :: "type \<Rightarrow> logic"  ("(1LIFTDEFL/(1'(_')))")
translations "LIFTDEFL('t)" \<rightleftharpoons> "CONST liftdefl TYPE('t)"

class "domain" = predomain + pcpo +
  fixes emb :: "'a::cpo \<rightarrow> udom"
  fixes prj :: "udom \<rightarrow> 'a::cpo"
  fixes defl :: "'a itself \<Rightarrow> udom defl"
  assumes ep_pair_emb_prj: "ep_pair emb prj"
  assumes cast_DEFL: "cast\<cdot>(defl TYPE('a)) = emb oo prj"

syntax "_DEFL" :: "type \<Rightarrow> logic"  ("(1DEFL/(1'(_')))")
translations "DEFL('t)" \<rightleftharpoons> "CONST defl TYPE('t)"

interpretation "domain": pcpo_ep_pair emb prj
  unfolding pcpo_ep_pair_def
  by (rule ep_pair_emb_prj)

lemmas emb_inverse = domain.e_inverse
lemmas emb_prj_below = domain.e_p_below
lemmas emb_eq_iff = domain.e_eq_iff
lemmas emb_strict = domain.e_strict
lemmas prj_strict = domain.p_strict

subsection {* Domains are bifinite *}

lemma approx_chain_ep_cast:
  assumes ep: "ep_pair (e::'a::pcpo \<rightarrow> udom) (p::udom \<rightarrow> 'a)"
  assumes cast_t: "cast\<cdot>t = e oo p"
  shows "\<exists>(a::nat \<Rightarrow> 'a::pcpo \<rightarrow> 'a). approx_chain a"
proof -
  interpret ep_pair e p by fact
  obtain Y where Y: "\<forall>i. Y i \<sqsubseteq> Y (Suc i)"
  and t: "t = (\<Squnion>i. defl_principal (Y i))"
    by (rule defl.obtain_principal_chain)
  def approx \<equiv> "\<lambda>i. (p oo cast\<cdot>(defl_principal (Y i)) oo e) :: 'a \<rightarrow> 'a"
  have "approx_chain approx"
  proof (rule approx_chain.intro)
    show "chain (\<lambda>i. approx i)"
      unfolding approx_def by (simp add: Y)
    show "(\<Squnion>i. approx i) = ID"
      unfolding approx_def
      by (simp add: lub_distribs Y t [symmetric] cast_t cfun_eq_iff)
    show "\<And>i. finite_deflation (approx i)"
      unfolding approx_def
      apply (rule finite_deflation_p_d_e)
      apply (rule finite_deflation_cast)
      apply (rule defl.compact_principal)
      apply (rule below_trans [OF monofun_cfun_fun])
      apply (rule is_ub_thelub, simp add: Y)
      apply (simp add: lub_distribs Y t [symmetric] cast_t)
      done
  qed
  thus "\<exists>(a::nat \<Rightarrow> 'a \<rightarrow> 'a). approx_chain a" by - (rule exI)
qed

instance "domain" \<subseteq> bifinite
by default (rule approx_chain_ep_cast [OF ep_pair_emb_prj cast_DEFL])

instance predomain \<subseteq> profinite
by default (rule approx_chain_ep_cast [OF predomain_ep cast_liftdefl])

subsection {* Universal domain ep-pairs *}

definition "u_emb = udom_emb (\<lambda>i. u_map\<cdot>(udom_approx i))"
definition "u_prj = udom_prj (\<lambda>i. u_map\<cdot>(udom_approx i))"

definition "prod_emb = udom_emb (\<lambda>i. cprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"
definition "prod_prj = udom_prj (\<lambda>i. cprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

definition "sprod_emb = udom_emb (\<lambda>i. sprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"
definition "sprod_prj = udom_prj (\<lambda>i. sprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

definition "ssum_emb = udom_emb (\<lambda>i. ssum_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"
definition "ssum_prj = udom_prj (\<lambda>i. ssum_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

definition "sfun_emb = udom_emb (\<lambda>i. sfun_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"
definition "sfun_prj = udom_prj (\<lambda>i. sfun_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma ep_pair_u: "ep_pair u_emb u_prj"
  unfolding u_emb_def u_prj_def
  by (simp add: ep_pair_udom approx_chain_u_map)

lemma ep_pair_prod: "ep_pair prod_emb prod_prj"
  unfolding prod_emb_def prod_prj_def
  by (simp add: ep_pair_udom approx_chain_cprod_map)

lemma ep_pair_sprod: "ep_pair sprod_emb sprod_prj"
  unfolding sprod_emb_def sprod_prj_def
  by (simp add: ep_pair_udom approx_chain_sprod_map)

lemma ep_pair_ssum: "ep_pair ssum_emb ssum_prj"
  unfolding ssum_emb_def ssum_prj_def
  by (simp add: ep_pair_udom approx_chain_ssum_map)

lemma ep_pair_sfun: "ep_pair sfun_emb sfun_prj"
  unfolding sfun_emb_def sfun_prj_def
  by (simp add: ep_pair_udom approx_chain_sfun_map)

subsection {* Type combinators *}

definition u_defl :: "udom defl \<rightarrow> udom defl"
  where "u_defl = defl_fun1 u_emb u_prj u_map"

definition prod_defl :: "udom defl \<rightarrow> udom defl \<rightarrow> udom defl"
  where "prod_defl = defl_fun2 prod_emb prod_prj cprod_map"

definition sprod_defl :: "udom defl \<rightarrow> udom defl \<rightarrow> udom defl"
  where "sprod_defl = defl_fun2 sprod_emb sprod_prj sprod_map"

definition ssum_defl :: "udom defl \<rightarrow> udom defl \<rightarrow> udom defl"
where "ssum_defl = defl_fun2 ssum_emb ssum_prj ssum_map"

definition sfun_defl :: "udom defl \<rightarrow> udom defl \<rightarrow> udom defl"
  where "sfun_defl = defl_fun2 sfun_emb sfun_prj sfun_map"

lemma cast_u_defl:
  "cast\<cdot>(u_defl\<cdot>A) = u_emb oo u_map\<cdot>(cast\<cdot>A) oo u_prj"
using ep_pair_u finite_deflation_u_map
unfolding u_defl_def by (rule cast_defl_fun1)

lemma cast_prod_defl:
  "cast\<cdot>(prod_defl\<cdot>A\<cdot>B) =
    prod_emb oo cprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo prod_prj"
using ep_pair_prod finite_deflation_cprod_map
unfolding prod_defl_def by (rule cast_defl_fun2)

lemma cast_sprod_defl:
  "cast\<cdot>(sprod_defl\<cdot>A\<cdot>B) =
    sprod_emb oo sprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo sprod_prj"
using ep_pair_sprod finite_deflation_sprod_map
unfolding sprod_defl_def by (rule cast_defl_fun2)

lemma cast_ssum_defl:
  "cast\<cdot>(ssum_defl\<cdot>A\<cdot>B) =
    ssum_emb oo ssum_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo ssum_prj"
using ep_pair_ssum finite_deflation_ssum_map
unfolding ssum_defl_def by (rule cast_defl_fun2)

lemma cast_sfun_defl:
  "cast\<cdot>(sfun_defl\<cdot>A\<cdot>B) =
    sfun_emb oo sfun_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo sfun_prj"
using ep_pair_sfun finite_deflation_sfun_map
unfolding sfun_defl_def by (rule cast_defl_fun2)

subsection {* Lemma for proving domain instances *}

text {*
  A class of domains where @{const liftemb}, @{const liftprj},
  and @{const liftdefl} are all defined in the standard way.
*}

class liftdomain = "domain" +
  assumes liftemb_eq: "liftemb = u_emb oo u_map\<cdot>emb"
  assumes liftprj_eq: "liftprj = u_map\<cdot>prj oo u_prj"
  assumes liftdefl_eq: "liftdefl TYPE('a::cpo) = u_defl\<cdot>DEFL('a)"

text {* Temporarily relax type constraints. *}

setup {*
  fold Sign.add_const_constraint
  [ (@{const_name defl}, SOME @{typ "'a::pcpo itself \<Rightarrow> udom defl"})
  , (@{const_name emb}, SOME @{typ "'a::pcpo \<rightarrow> udom"})
  , (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::pcpo"})
  , (@{const_name liftdefl}, SOME @{typ "'a::pcpo itself \<Rightarrow> udom defl"})
  , (@{const_name liftemb}, SOME @{typ "'a::pcpo u \<rightarrow> udom"})
  , (@{const_name liftprj}, SOME @{typ "udom \<rightarrow> 'a::pcpo u"}) ]
*}

default_sort pcpo

lemma liftdomain_class_intro:
  assumes liftemb: "(liftemb :: 'a u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"
  assumes liftprj: "(liftprj :: udom \<rightarrow> 'a u) = u_map\<cdot>prj oo u_prj"
  assumes liftdefl: "liftdefl TYPE('a) = u_defl\<cdot>DEFL('a)"
  assumes ep_pair: "ep_pair emb (prj :: udom \<rightarrow> 'a)"
  assumes cast_defl: "cast\<cdot>DEFL('a) = emb oo (prj :: udom \<rightarrow> 'a)"
  shows "OFCLASS('a, liftdomain_class)"
proof
  show "ep_pair liftemb (liftprj :: udom \<rightarrow> 'a u)"
    unfolding liftemb liftprj
    by (intro ep_pair_comp ep_pair_u_map ep_pair ep_pair_u)
  show "cast\<cdot>LIFTDEFL('a) = liftemb oo (liftprj :: udom \<rightarrow> 'a u)"
    unfolding liftemb liftprj liftdefl
    by (simp add: cfcomp1 cast_u_defl cast_defl u_map_map)
next
qed fact+

text {* Restore original type constraints. *}

setup {*
  fold Sign.add_const_constraint
  [ (@{const_name defl}, SOME @{typ "'a::domain itself \<Rightarrow> udom defl"})
  , (@{const_name emb}, SOME @{typ "'a::domain \<rightarrow> udom"})
  , (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::domain"})
  , (@{const_name liftdefl}, SOME @{typ "'a::predomain itself \<Rightarrow> udom defl"})
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
  "(liftemb :: udom u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> udom u) = u_map\<cdot>prj oo u_prj"

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
  "(liftemb :: 'a u u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> 'a u u) = u_map\<cdot>prj oo u_prj"

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
  "emb = sfun_emb oo sfun_map\<cdot>prj\<cdot>emb"

definition
  "prj = sfun_map\<cdot>emb\<cdot>prj oo sfun_prj"

definition
  "defl (t::('a \<rightarrow>! 'b) itself) = sfun_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<rightarrow>! 'b) u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<rightarrow>! 'b) u) = u_map\<cdot>prj oo u_prj"

definition
  "liftdefl (t::('a \<rightarrow>! 'b) itself) = u_defl\<cdot>DEFL('a \<rightarrow>! 'b)"

instance
using liftemb_sfun_def liftprj_sfun_def liftdefl_sfun_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def
    by (intro ep_pair_comp ep_pair_sfun ep_pair_sfun_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a \<rightarrow>! 'b) = emb oo (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def defl_sfun_def cast_sfun_defl
    by (simp add: cast_DEFL oo_def sfun_eq_iff sfun_map_map)
qed

end

lemma DEFL_sfun:
  "DEFL('a::domain \<rightarrow>! 'b::domain) = sfun_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_sfun_def)

subsubsection {* Continuous function space *}

instantiation cfun :: (predomain, "domain") liftdomain
begin

definition
  "emb = emb oo encode_cfun"

definition
  "prj = decode_cfun oo prj"

definition
  "defl (t::('a \<rightarrow> 'b) itself) = DEFL('a u \<rightarrow>! 'b)"

definition
  "(liftemb :: ('a \<rightarrow> 'b) u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<rightarrow> 'b) u) = u_map\<cdot>prj oo u_prj"

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
  "emb = sprod_emb oo sprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = sprod_map\<cdot>prj\<cdot>prj oo sprod_prj"

definition
  "defl (t::('a \<otimes> 'b) itself) = sprod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<otimes> 'b) u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<otimes> 'b) u) = u_map\<cdot>prj oo u_prj"

definition
  "liftdefl (t::('a \<otimes> 'b) itself) = u_defl\<cdot>DEFL('a \<otimes> 'b)"

instance
using liftemb_sprod_def liftprj_sprod_def liftdefl_sprod_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<otimes> 'b)"
    unfolding emb_sprod_def prj_sprod_def
    by (intro ep_pair_comp ep_pair_sprod ep_pair_sprod_map ep_pair_emb_prj)
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
  "emb = prod_emb oo cprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = cprod_map\<cdot>prj\<cdot>prj oo prod_prj"

definition
  "defl (t::('a \<times> 'b) itself) = prod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def
    by (intro ep_pair_comp ep_pair_prod ep_pair_cprod_map ep_pair_emb_prj)
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

subsubsection {* Unit type *}

instantiation unit :: liftdomain
begin

definition
  "emb = (\<bottom> :: unit \<rightarrow> udom)"

definition
  "prj = (\<bottom> :: udom \<rightarrow> unit)"

definition
  "defl (t::unit itself) = \<bottom>"

definition
  "(liftemb :: unit u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> unit u) = u_map\<cdot>prj oo u_prj"

definition
  "liftdefl (t::unit itself) = u_defl\<cdot>DEFL(unit)"

instance
using liftemb_unit_def liftprj_unit_def liftdefl_unit_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> unit)"
    unfolding emb_unit_def prj_unit_def
    by (simp add: ep_pair.intro)
next
  show "cast\<cdot>DEFL(unit) = emb oo (prj :: udom \<rightarrow> unit)"
    unfolding emb_unit_def prj_unit_def defl_unit_def by simp
qed

end

subsubsection {* Discrete cpo *}

instantiation discr :: (countable) predomain
begin

definition
  "(liftemb :: 'a discr u \<rightarrow> udom) = udom_emb discr_approx"

definition
  "(liftprj :: udom \<rightarrow> 'a discr u) = udom_prj discr_approx"

definition
  "liftdefl (t::'a discr itself) =
    (\<Squnion>i. defl_principal (Abs_fin_defl (liftemb oo discr_approx i oo (liftprj::udom \<rightarrow> 'a discr u))))"

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
  "emb = ssum_emb oo ssum_map\<cdot>emb\<cdot>emb"

definition
  "prj = ssum_map\<cdot>prj\<cdot>prj oo ssum_prj"

definition
  "defl (t::('a \<oplus> 'b) itself) = ssum_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<oplus> 'b) u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> ('a \<oplus> 'b) u) = u_map\<cdot>prj oo u_prj"

definition
  "liftdefl (t::('a \<oplus> 'b) itself) = u_defl\<cdot>DEFL('a \<oplus> 'b)"

instance
using liftemb_ssum_def liftprj_ssum_def liftdefl_ssum_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def
    by (intro ep_pair_comp ep_pair_ssum ep_pair_ssum_map ep_pair_emb_prj)
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
  "(liftemb :: 'a lift u \<rightarrow> udom) = u_emb oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> 'a lift u) = u_map\<cdot>prj oo u_prj"

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
