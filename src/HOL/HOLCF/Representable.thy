(*  Title:      HOL/HOLCF/Representable.thy
    Author:     Brian Huffman
*)

section \<open>Representable domains\<close>

theory Representable
imports Algebraic Map_Functions "HOL-Library.Countable"
begin

default_sort cpo


subsection \<open>Class of representable domains\<close>

text \<open>
  We define a ``domain'' as a pcpo that is isomorphic to some
  algebraic deflation over the universal domain; this is equivalent
  to being omega-bifinite.

  A predomain is a cpo that, when lifted, becomes a domain.
  Predomains are represented by deflations over a lifted universal
  domain type.
\<close>

class predomain_syn = cpo +
  fixes liftemb :: "'a\<^sub>\<bottom> \<rightarrow> udom\<^sub>\<bottom>"
  fixes liftprj :: "udom\<^sub>\<bottom> \<rightarrow> 'a\<^sub>\<bottom>"
  fixes liftdefl :: "'a itself \<Rightarrow> udom u defl"

class predomain = predomain_syn +
  assumes predomain_ep: "ep_pair liftemb liftprj"
  assumes cast_liftdefl: "cast\<cdot>(liftdefl TYPE('a)) = liftemb oo liftprj"

syntax "_LIFTDEFL" :: "type \<Rightarrow> logic"  (\<open>(1LIFTDEFL/(1'(_')))\<close>)
syntax_consts "_LIFTDEFL" \<rightleftharpoons> liftdefl
translations "LIFTDEFL('t)" \<rightleftharpoons> "CONST liftdefl TYPE('t)"

definition liftdefl_of :: "udom defl \<rightarrow> udom u defl"
  where "liftdefl_of = defl_fun1 ID ID u_map"

lemma cast_liftdefl_of: "cast\<cdot>(liftdefl_of\<cdot>t) = u_map\<cdot>(cast\<cdot>t)"
by (simp add: liftdefl_of_def cast_defl_fun1 ep_pair_def finite_deflation_u_map)

class "domain" = predomain_syn + pcpo +
  fixes emb :: "'a \<rightarrow> udom"
  fixes prj :: "udom \<rightarrow> 'a"
  fixes defl :: "'a itself \<Rightarrow> udom defl"
  assumes ep_pair_emb_prj: "ep_pair emb prj"
  assumes cast_DEFL: "cast\<cdot>(defl TYPE('a)) = emb oo prj"
  assumes liftemb_eq: "liftemb = u_map\<cdot>emb"
  assumes liftprj_eq: "liftprj = u_map\<cdot>prj"
  assumes liftdefl_eq: "liftdefl TYPE('a) = liftdefl_of\<cdot>(defl TYPE('a))"

syntax "_DEFL" :: "type \<Rightarrow> logic"  (\<open>(1DEFL/(1'(_')))\<close>)
syntax_consts "_DEFL" \<rightleftharpoons> defl
translations "DEFL('t)" \<rightleftharpoons> "CONST defl TYPE('t)"

instance "domain" \<subseteq> predomain
proof
  show "ep_pair liftemb (liftprj::udom\<^sub>\<bottom> \<rightarrow> 'a\<^sub>\<bottom>)"
    unfolding liftemb_eq liftprj_eq
    by (intro ep_pair_u_map ep_pair_emb_prj)
  show "cast\<cdot>LIFTDEFL('a) = liftemb oo (liftprj::udom\<^sub>\<bottom> \<rightarrow> 'a\<^sub>\<bottom>)"
    unfolding liftemb_eq liftprj_eq liftdefl_eq
    by (simp add: cast_liftdefl_of cast_DEFL u_map_oo)
qed

text \<open>
  Constants \<^const>\<open>liftemb\<close> and \<^const>\<open>liftprj\<close> imply class predomain.
\<close>

setup \<open>
  fold Sign.add_const_constraint
  [(\<^const_name>\<open>liftemb\<close>, SOME \<^typ>\<open>'a::predomain u \<rightarrow> udom u\<close>),
   (\<^const_name>\<open>liftprj\<close>, SOME \<^typ>\<open>udom u \<rightarrow> 'a::predomain u\<close>),
   (\<^const_name>\<open>liftdefl\<close>, SOME \<^typ>\<open>'a::predomain itself \<Rightarrow> udom u defl\<close>)]
\<close>

interpretation predomain: pcpo_ep_pair liftemb liftprj
  unfolding pcpo_ep_pair_def by (rule predomain_ep)

interpretation "domain": pcpo_ep_pair emb prj
  unfolding pcpo_ep_pair_def by (rule ep_pair_emb_prj)

lemmas emb_inverse = domain.e_inverse
lemmas emb_prj_below = domain.e_p_below
lemmas emb_eq_iff = domain.e_eq_iff
lemmas emb_strict = domain.e_strict
lemmas prj_strict = domain.p_strict


subsection \<open>Domains are bifinite\<close>

lemma approx_chain_ep_cast:
  assumes ep: "ep_pair (e::'a::pcpo \<rightarrow> 'b::bifinite) (p::'b \<rightarrow> 'a)"
  assumes cast_t: "cast\<cdot>t = e oo p"
  shows "\<exists>(a::nat \<Rightarrow> 'a::pcpo \<rightarrow> 'a). approx_chain a"
proof -
  interpret ep_pair e p by fact
  obtain Y where Y: "\<forall>i. Y i \<sqsubseteq> Y (Suc i)"
  and t: "t = (\<Squnion>i. defl_principal (Y i))"
    by (rule defl.obtain_principal_chain)
  define approx where "approx i = (p oo cast\<cdot>(defl_principal (Y i)) oo e)" for i
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
by standard (rule approx_chain_ep_cast [OF ep_pair_emb_prj cast_DEFL])

instance predomain \<subseteq> profinite
by standard (rule approx_chain_ep_cast [OF predomain_ep cast_liftdefl])


subsection \<open>Universal domain ep-pairs\<close>

definition "u_emb = udom_emb (\<lambda>i. u_map\<cdot>(udom_approx i))"
definition "u_prj = udom_prj (\<lambda>i. u_map\<cdot>(udom_approx i))"

definition "prod_emb = udom_emb (\<lambda>i. prod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"
definition "prod_prj = udom_prj (\<lambda>i. prod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

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
  by (simp add: ep_pair_udom approx_chain_prod_map)

lemma ep_pair_sprod: "ep_pair sprod_emb sprod_prj"
  unfolding sprod_emb_def sprod_prj_def
  by (simp add: ep_pair_udom approx_chain_sprod_map)

lemma ep_pair_ssum: "ep_pair ssum_emb ssum_prj"
  unfolding ssum_emb_def ssum_prj_def
  by (simp add: ep_pair_udom approx_chain_ssum_map)

lemma ep_pair_sfun: "ep_pair sfun_emb sfun_prj"
  unfolding sfun_emb_def sfun_prj_def
  by (simp add: ep_pair_udom approx_chain_sfun_map)


subsection \<open>Type combinators\<close>

definition u_defl :: "udom defl \<rightarrow> udom defl"
  where "u_defl = defl_fun1 u_emb u_prj u_map"

definition prod_defl :: "udom defl \<rightarrow> udom defl \<rightarrow> udom defl"
  where "prod_defl = defl_fun2 prod_emb prod_prj prod_map"

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
    prod_emb oo prod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo prod_prj"
using ep_pair_prod finite_deflation_prod_map
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

text \<open>Special deflation combinator for unpointed types.\<close>

definition u_liftdefl :: "udom u defl \<rightarrow> udom defl"
  where "u_liftdefl = defl_fun1 u_emb u_prj ID"

lemma cast_u_liftdefl:
  "cast\<cdot>(u_liftdefl\<cdot>A) = u_emb oo cast\<cdot>A oo u_prj"
unfolding u_liftdefl_def by (simp add: cast_defl_fun1 ep_pair_u)

lemma u_liftdefl_liftdefl_of:
  "u_liftdefl\<cdot>(liftdefl_of\<cdot>A) = u_defl\<cdot>A"
by (rule cast_eq_imp_eq)
   (simp add: cast_u_liftdefl cast_liftdefl_of cast_u_defl)


subsection \<open>Class instance proofs\<close>

subsubsection \<open>Universal domain\<close>

instantiation udom :: "domain"
begin

definition [simp]:
  "emb = (ID :: udom \<rightarrow> udom)"

definition [simp]:
  "prj = (ID :: udom \<rightarrow> udom)"

definition
  "defl (t::udom itself) = (\<Squnion>i. defl_principal (Abs_fin_defl (udom_approx i)))"

definition
  "(liftemb :: udom u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> udom u) = u_map\<cdot>prj"

definition
  "liftdefl (t::udom itself) = liftdefl_of\<cdot>DEFL(udom)"

instance proof
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
qed (fact liftemb_udom_def liftprj_udom_def liftdefl_udom_def)+

end


subsubsection \<open>Lifted cpo\<close>

instantiation u :: (predomain) "domain"
begin

definition
  "emb = u_emb oo liftemb"

definition
  "prj = liftprj oo u_prj"

definition
  "defl (t::'a u itself) = u_liftdefl\<cdot>LIFTDEFL('a)"

definition
  "(liftemb :: 'a u u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> 'a u u) = u_map\<cdot>prj"

definition
  "liftdefl (t::'a u itself) = liftdefl_of\<cdot>DEFL('a u)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a u)"
    unfolding emb_u_def prj_u_def
    by (intro ep_pair_comp ep_pair_u predomain_ep)
  show "cast\<cdot>DEFL('a u) = emb oo (prj :: udom \<rightarrow> 'a u)"
    unfolding emb_u_def prj_u_def defl_u_def
    by (simp add: cast_u_liftdefl cast_liftdefl assoc_oo)
qed (fact liftemb_u_def liftprj_u_def liftdefl_u_def)+

end

lemma DEFL_u: "DEFL('a::predomain u) = u_liftdefl\<cdot>LIFTDEFL('a)"
by (rule defl_u_def)


subsubsection \<open>Strict function space\<close>

instantiation sfun :: ("domain", "domain") "domain"
begin

definition
  "emb = sfun_emb oo sfun_map\<cdot>prj\<cdot>emb"

definition
  "prj = sfun_map\<cdot>emb\<cdot>prj oo sfun_prj"

definition
  "defl (t::('a \<rightarrow>! 'b) itself) = sfun_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<rightarrow>! 'b) u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> ('a \<rightarrow>! 'b) u) = u_map\<cdot>prj"

definition
  "liftdefl (t::('a \<rightarrow>! 'b) itself) = liftdefl_of\<cdot>DEFL('a \<rightarrow>! 'b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def
    by (intro ep_pair_comp ep_pair_sfun ep_pair_sfun_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a \<rightarrow>! 'b) = emb oo (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def defl_sfun_def cast_sfun_defl
    by (simp add: cast_DEFL oo_def sfun_eq_iff sfun_map_map)
qed (fact liftemb_sfun_def liftprj_sfun_def liftdefl_sfun_def)+

end

lemma DEFL_sfun:
  "DEFL('a::domain \<rightarrow>! 'b::domain) = sfun_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_sfun_def)


subsubsection \<open>Continuous function space\<close>

instantiation cfun :: (predomain, "domain") "domain"
begin

definition
  "emb = emb oo encode_cfun"

definition
  "prj = decode_cfun oo prj"

definition
  "defl (t::('a \<rightarrow> 'b) itself) = DEFL('a u \<rightarrow>! 'b)"

definition
  "(liftemb :: ('a \<rightarrow> 'b) u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> ('a \<rightarrow> 'b) u) = u_map\<cdot>prj"

definition
  "liftdefl (t::('a \<rightarrow> 'b) itself) = liftdefl_of\<cdot>DEFL('a \<rightarrow> 'b)"

instance proof
  have "ep_pair encode_cfun decode_cfun"
    by (rule ep_pair.intro, simp_all)
  thus "ep_pair emb (prj :: udom \<rightarrow> 'a \<rightarrow> 'b)"
    unfolding emb_cfun_def prj_cfun_def
    using ep_pair_emb_prj by (rule ep_pair_comp)
  show "cast\<cdot>DEFL('a \<rightarrow> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<rightarrow> 'b)"
    unfolding emb_cfun_def prj_cfun_def defl_cfun_def
    by (simp add: cast_DEFL cfcomp1)
qed (fact liftemb_cfun_def liftprj_cfun_def liftdefl_cfun_def)+

end

lemma DEFL_cfun:
  "DEFL('a::predomain \<rightarrow> 'b::domain) = DEFL('a u \<rightarrow>! 'b)"
by (rule defl_cfun_def)


subsubsection \<open>Strict product\<close>

instantiation sprod :: ("domain", "domain") "domain"
begin

definition
  "emb = sprod_emb oo sprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = sprod_map\<cdot>prj\<cdot>prj oo sprod_prj"

definition
  "defl (t::('a \<otimes> 'b) itself) = sprod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<otimes> 'b) u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> ('a \<otimes> 'b) u) = u_map\<cdot>prj"

definition
  "liftdefl (t::('a \<otimes> 'b) itself) = liftdefl_of\<cdot>DEFL('a \<otimes> 'b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<otimes> 'b)"
    unfolding emb_sprod_def prj_sprod_def
    by (intro ep_pair_comp ep_pair_sprod ep_pair_sprod_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a \<otimes> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<otimes> 'b)"
    unfolding emb_sprod_def prj_sprod_def defl_sprod_def cast_sprod_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff sprod_map_map)
qed (fact liftemb_sprod_def liftprj_sprod_def liftdefl_sprod_def)+

end

lemma DEFL_sprod:
  "DEFL('a::domain \<otimes> 'b::domain) = sprod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_sprod_def)


subsubsection \<open>Cartesian product\<close>

definition prod_liftdefl :: "udom u defl \<rightarrow> udom u defl \<rightarrow> udom u defl"
  where "prod_liftdefl = defl_fun2 (u_map\<cdot>prod_emb oo decode_prod_u)
    (encode_prod_u oo u_map\<cdot>prod_prj) sprod_map"

lemma cast_prod_liftdefl:
  "cast\<cdot>(prod_liftdefl\<cdot>a\<cdot>b) =
    (u_map\<cdot>prod_emb oo decode_prod_u) oo sprod_map\<cdot>(cast\<cdot>a)\<cdot>(cast\<cdot>b) oo
      (encode_prod_u oo u_map\<cdot>prod_prj)"
unfolding prod_liftdefl_def
apply (rule cast_defl_fun2)
apply (intro ep_pair_comp ep_pair_u_map ep_pair_prod)
apply (simp add: ep_pair.intro)
apply (erule (1) finite_deflation_sprod_map)
done

instantiation prod :: (predomain, predomain) predomain
begin

definition
  "liftemb = (u_map\<cdot>prod_emb oo decode_prod_u) oo
    (sprod_map\<cdot>liftemb\<cdot>liftemb oo encode_prod_u)"

definition
  "liftprj = (decode_prod_u oo sprod_map\<cdot>liftprj\<cdot>liftprj) oo
    (encode_prod_u oo u_map\<cdot>prod_prj)"

definition
  "liftdefl (t::('a \<times> 'b) itself) = prod_liftdefl\<cdot>LIFTDEFL('a)\<cdot>LIFTDEFL('b)"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> ('a \<times> 'b) u)"
    unfolding liftemb_prod_def liftprj_prod_def
    by (intro ep_pair_comp ep_pair_sprod_map ep_pair_u_map
       ep_pair_prod predomain_ep, simp_all add: ep_pair.intro)
  show "cast\<cdot>LIFTDEFL('a \<times> 'b) = liftemb oo (liftprj :: udom u \<rightarrow> ('a \<times> 'b) u)"
    unfolding liftemb_prod_def liftprj_prod_def liftdefl_prod_def
    by (simp add: cast_prod_liftdefl cast_liftdefl cfcomp1 sprod_map_map)
qed

end

instantiation prod :: ("domain", "domain") "domain"
begin

definition
  "emb = prod_emb oo prod_map\<cdot>emb\<cdot>emb"

definition
  "prj = prod_map\<cdot>prj\<cdot>prj oo prod_prj"

definition
  "defl (t::('a \<times> 'b) itself) = prod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

instance proof
  show 1: "ep_pair emb (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def
    by (intro ep_pair_comp ep_pair_prod ep_pair_prod_map ep_pair_emb_prj)
  show 2: "cast\<cdot>DEFL('a \<times> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def defl_prod_def cast_prod_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff prod_map_map)
  show 3: "liftemb = u_map\<cdot>(emb :: 'a \<times> 'b \<rightarrow> udom)"
    unfolding emb_prod_def liftemb_prod_def liftemb_eq
    unfolding encode_prod_u_def decode_prod_u_def
    by (rule cfun_eqI, case_tac x, simp, clarsimp)
  show 4: "liftprj = u_map\<cdot>(prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding prj_prod_def liftprj_prod_def liftprj_eq
    unfolding encode_prod_u_def decode_prod_u_def
    apply (rule cfun_eqI, case_tac x, simp)
    apply (rename_tac y, case_tac "prod_prj\<cdot>y", simp)
    done
  show 5: "LIFTDEFL('a \<times> 'b) = liftdefl_of\<cdot>DEFL('a \<times> 'b)"
    by (rule cast_eq_imp_eq)
      (simp add: cast_liftdefl cast_liftdefl_of cast_DEFL 2 3 4 u_map_oo)
qed

end

lemma DEFL_prod:
  "DEFL('a::domain \<times> 'b::domain) = prod_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_prod_def)

lemma LIFTDEFL_prod:
  "LIFTDEFL('a::predomain \<times> 'b::predomain) =
    prod_liftdefl\<cdot>LIFTDEFL('a)\<cdot>LIFTDEFL('b)"
by (rule liftdefl_prod_def)


subsubsection \<open>Unit type\<close>

instantiation unit :: "domain"
begin

definition
  "emb = (\<bottom> :: unit \<rightarrow> udom)"

definition
  "prj = (\<bottom> :: udom \<rightarrow> unit)"

definition
  "defl (t::unit itself) = \<bottom>"

definition
  "(liftemb :: unit u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> unit u) = u_map\<cdot>prj"

definition
  "liftdefl (t::unit itself) = liftdefl_of\<cdot>DEFL(unit)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> unit)"
    unfolding emb_unit_def prj_unit_def
    by (simp add: ep_pair.intro)
  show "cast\<cdot>DEFL(unit) = emb oo (prj :: udom \<rightarrow> unit)"
    unfolding emb_unit_def prj_unit_def defl_unit_def by simp
qed (fact liftemb_unit_def liftprj_unit_def liftdefl_unit_def)+

end


subsubsection \<open>Discrete cpo\<close>

instantiation discr :: (countable) predomain
begin

definition
  "(liftemb :: 'a discr u \<rightarrow> udom u) = strictify\<cdot>up oo udom_emb discr_approx"

definition
  "(liftprj :: udom u \<rightarrow> 'a discr u) = udom_prj discr_approx oo fup\<cdot>ID"

definition
  "liftdefl (t::'a discr itself) =
    (\<Squnion>i. defl_principal (Abs_fin_defl (liftemb oo discr_approx i oo (liftprj::udom u \<rightarrow> 'a discr u))))"

instance proof
  show 1: "ep_pair liftemb (liftprj :: udom u \<rightarrow> 'a discr u)"
    unfolding liftemb_discr_def liftprj_discr_def
    apply (intro ep_pair_comp ep_pair_udom [OF discr_approx])
    apply (rule ep_pair.intro)
    apply (simp add: strictify_conv_if)
    apply (case_tac y, simp, simp add: strictify_conv_if)
    done
  show "cast\<cdot>LIFTDEFL('a discr) = liftemb oo (liftprj :: udom u \<rightarrow> 'a discr u)"
    unfolding liftdefl_discr_def
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule defl.principal_mono)
    apply (simp add: below_fin_defl_def)
    apply (simp add: Abs_fin_defl_inverse
        ep_pair.finite_deflation_e_d_p [OF 1]
        approx_chain.finite_deflation_approx [OF discr_approx])
    apply (intro monofun_cfun below_refl)
    apply (rule chainE)
    apply (rule chain_discr_approx)
    apply (subst cast_defl_principal)
    apply (simp add: Abs_fin_defl_inverse
        ep_pair.finite_deflation_e_d_p [OF 1]
        approx_chain.finite_deflation_approx [OF discr_approx])
    apply (simp add: lub_distribs)
    done
qed

end


subsubsection \<open>Strict sum\<close>

instantiation ssum :: ("domain", "domain") "domain"
begin

definition
  "emb = ssum_emb oo ssum_map\<cdot>emb\<cdot>emb"

definition
  "prj = ssum_map\<cdot>prj\<cdot>prj oo ssum_prj"

definition
  "defl (t::('a \<oplus> 'b) itself) = ssum_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"

definition
  "(liftemb :: ('a \<oplus> 'b) u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> ('a \<oplus> 'b) u) = u_map\<cdot>prj"

definition
  "liftdefl (t::('a \<oplus> 'b) itself) = liftdefl_of\<cdot>DEFL('a \<oplus> 'b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def
    by (intro ep_pair_comp ep_pair_ssum ep_pair_ssum_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a \<oplus> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def defl_ssum_def cast_ssum_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff ssum_map_map)
qed (fact liftemb_ssum_def liftprj_ssum_def liftdefl_ssum_def)+

end

lemma DEFL_ssum:
  "DEFL('a::domain \<oplus> 'b::domain) = ssum_defl\<cdot>DEFL('a)\<cdot>DEFL('b)"
by (rule defl_ssum_def)


subsubsection \<open>Lifted HOL type\<close>

instantiation lift :: (countable) "domain"
begin

definition
  "emb = emb oo (\<Lambda> x. Rep_lift x)"

definition
  "prj = (\<Lambda> y. Abs_lift y) oo prj"

definition
  "defl (t::'a lift itself) = DEFL('a discr u)"

definition
  "(liftemb :: 'a lift u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> 'a lift u) = u_map\<cdot>prj"

definition
  "liftdefl (t::'a lift itself) = liftdefl_of\<cdot>DEFL('a lift)"

instance proof
  note [simp] = cont_Rep_lift cont_Abs_lift Rep_lift_inverse Abs_lift_inverse
  have "ep_pair (\<Lambda>(x::'a lift). Rep_lift x) (\<Lambda> y. Abs_lift y)"
    by (simp add: ep_pair_def)
  thus "ep_pair emb (prj :: udom \<rightarrow> 'a lift)"
    unfolding emb_lift_def prj_lift_def
    using ep_pair_emb_prj by (rule ep_pair_comp)
  show "cast\<cdot>DEFL('a lift) = emb oo (prj :: udom \<rightarrow> 'a lift)"
    unfolding emb_lift_def prj_lift_def defl_lift_def cast_DEFL
    by (simp add: cfcomp1)
qed (fact liftemb_lift_def liftprj_lift_def liftdefl_lift_def)+

end

end
