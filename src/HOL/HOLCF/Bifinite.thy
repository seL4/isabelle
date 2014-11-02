(*  Title:      HOL/HOLCF/Bifinite.thy
    Author:     Brian Huffman
*)

section {* Profinite and bifinite cpos *}

theory Bifinite
imports Map_Functions "~~/src/HOL/Library/Countable"
begin

default_sort cpo

subsection {* Chains of finite deflations *}

locale approx_chain =
  fixes approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  assumes chain_approx [simp]: "chain (\<lambda>i. approx i)"
  assumes lub_approx [simp]: "(\<Squnion>i. approx i) = ID"
  assumes finite_deflation_approx [simp]: "\<And>i. finite_deflation (approx i)"
begin

lemma deflation_approx: "deflation (approx i)"
using finite_deflation_approx by (rule finite_deflation_imp_deflation)

lemma approx_idem: "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
using deflation_approx by (rule deflation.idem)

lemma approx_below: "approx i\<cdot>x \<sqsubseteq> x"
using deflation_approx by (rule deflation.below)

lemma finite_range_approx: "finite (range (\<lambda>x. approx i\<cdot>x))"
apply (rule finite_deflation.finite_range)
apply (rule finite_deflation_approx)
done

lemma compact_approx [simp]: "compact (approx n\<cdot>x)"
apply (rule finite_deflation.compact)
apply (rule finite_deflation_approx)
done

lemma compact_eq_approx: "compact x \<Longrightarrow> \<exists>i. approx i\<cdot>x = x"
by (rule admD2, simp_all)

end

subsection {* Omega-profinite and bifinite domains *}

class bifinite = pcpo +
  assumes bifinite: "\<exists>(a::nat \<Rightarrow> 'a \<rightarrow> 'a). approx_chain a"

class profinite = cpo +
  assumes profinite: "\<exists>(a::nat \<Rightarrow> 'a\<^sub>\<bottom> \<rightarrow> 'a\<^sub>\<bottom>). approx_chain a"

subsection {* Building approx chains *}

lemma approx_chain_iso:
  assumes a: "approx_chain a"
  assumes [simp]: "\<And>x. f\<cdot>(g\<cdot>x) = x"
  assumes [simp]: "\<And>y. g\<cdot>(f\<cdot>y) = y"
  shows "approx_chain (\<lambda>i. f oo a i oo g)"
proof -
  have 1: "f oo g = ID" by (simp add: cfun_eqI)
  have 2: "ep_pair f g" by (simp add: ep_pair_def)
  from 1 2 show ?thesis
    using a unfolding approx_chain_def
    by (simp add: lub_APP ep_pair.finite_deflation_e_d_p)
qed

lemma approx_chain_u_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. u_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP u_map_ID finite_deflation_u_map)

lemma approx_chain_sfun_map:
  assumes "approx_chain a" and "approx_chain b"
  shows "approx_chain (\<lambda>i. sfun_map\<cdot>(a i)\<cdot>(b i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP sfun_map_ID finite_deflation_sfun_map)

lemma approx_chain_sprod_map:
  assumes "approx_chain a" and "approx_chain b"
  shows "approx_chain (\<lambda>i. sprod_map\<cdot>(a i)\<cdot>(b i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP sprod_map_ID finite_deflation_sprod_map)

lemma approx_chain_ssum_map:
  assumes "approx_chain a" and "approx_chain b"
  shows "approx_chain (\<lambda>i. ssum_map\<cdot>(a i)\<cdot>(b i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP ssum_map_ID finite_deflation_ssum_map)

lemma approx_chain_cfun_map:
  assumes "approx_chain a" and "approx_chain b"
  shows "approx_chain (\<lambda>i. cfun_map\<cdot>(a i)\<cdot>(b i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP cfun_map_ID finite_deflation_cfun_map)

lemma approx_chain_prod_map:
  assumes "approx_chain a" and "approx_chain b"
  shows "approx_chain (\<lambda>i. prod_map\<cdot>(a i)\<cdot>(b i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP prod_map_ID finite_deflation_prod_map)

text {* Approx chains for countable discrete types. *}

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

subsection {* Class instance proofs *}

instance bifinite \<subseteq> profinite
proof
  show "\<exists>(a::nat \<Rightarrow> 'a\<^sub>\<bottom> \<rightarrow> 'a\<^sub>\<bottom>). approx_chain a"
    using bifinite [where 'a='a]
    by (fast intro!: approx_chain_u_map)
qed

instance u :: (profinite) bifinite
  by default (rule profinite)

text {*
  Types @{typ "'a \<rightarrow> 'b"} and @{typ "'a u \<rightarrow>! 'b"} are isomorphic.
*}

definition "encode_cfun = (\<Lambda> f. sfun_abs\<cdot>(fup\<cdot>f))"

definition "decode_cfun = (\<Lambda> g x. sfun_rep\<cdot>g\<cdot>(up\<cdot>x))"

lemma decode_encode_cfun [simp]: "decode_cfun\<cdot>(encode_cfun\<cdot>x) = x"
unfolding encode_cfun_def decode_cfun_def
by (simp add: eta_cfun)

lemma encode_decode_cfun [simp]: "encode_cfun\<cdot>(decode_cfun\<cdot>y) = y"
unfolding encode_cfun_def decode_cfun_def
apply (simp add: sfun_eq_iff strictify_cancel)
apply (rule cfun_eqI, case_tac x, simp_all)
done

instance cfun :: (profinite, bifinite) bifinite
proof
  obtain a :: "nat \<Rightarrow> 'a\<^sub>\<bottom> \<rightarrow> 'a\<^sub>\<bottom>" where a: "approx_chain a"
    using profinite ..
  obtain b :: "nat \<Rightarrow> 'b \<rightarrow> 'b" where b: "approx_chain b"
    using bifinite ..
  have "approx_chain (\<lambda>i. decode_cfun oo sfun_map\<cdot>(a i)\<cdot>(b i) oo encode_cfun)"
    using a b by (simp add: approx_chain_iso approx_chain_sfun_map)
  thus "\<exists>(a::nat \<Rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)). approx_chain a"
    by - (rule exI)
qed

text {*
  Types @{typ "('a * 'b) u"} and @{typ "'a u \<otimes> 'b u"} are isomorphic.
*}

definition "encode_prod_u = (\<Lambda>(up\<cdot>(x, y)). (:up\<cdot>x, up\<cdot>y:))"

definition "decode_prod_u = (\<Lambda>(:up\<cdot>x, up\<cdot>y:). up\<cdot>(x, y))"

lemma decode_encode_prod_u [simp]: "decode_prod_u\<cdot>(encode_prod_u\<cdot>x) = x"
unfolding encode_prod_u_def decode_prod_u_def
by (case_tac x, simp, rename_tac y, case_tac y, simp)

lemma encode_decode_prod_u [simp]: "encode_prod_u\<cdot>(decode_prod_u\<cdot>y) = y"
unfolding encode_prod_u_def decode_prod_u_def
apply (case_tac y, simp, rename_tac a b)
apply (case_tac a, simp, case_tac b, simp, simp)
done

instance prod :: (profinite, profinite) profinite
proof
  obtain a :: "nat \<Rightarrow> 'a\<^sub>\<bottom> \<rightarrow> 'a\<^sub>\<bottom>" where a: "approx_chain a"
    using profinite ..
  obtain b :: "nat \<Rightarrow> 'b\<^sub>\<bottom> \<rightarrow> 'b\<^sub>\<bottom>" where b: "approx_chain b"
    using profinite ..
  have "approx_chain (\<lambda>i. decode_prod_u oo sprod_map\<cdot>(a i)\<cdot>(b i) oo encode_prod_u)"
    using a b by (simp add: approx_chain_iso approx_chain_sprod_map)
  thus "\<exists>(a::nat \<Rightarrow> ('a \<times> 'b)\<^sub>\<bottom> \<rightarrow> ('a \<times> 'b)\<^sub>\<bottom>). approx_chain a"
    by - (rule exI)
qed

instance prod :: (bifinite, bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> ('a \<times> 'b) \<rightarrow> ('a \<times> 'b)). approx_chain a"
    using bifinite [where 'a='a] and bifinite [where 'a='b]
    by (fast intro!: approx_chain_prod_map)
qed

instance sfun :: (bifinite, bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> ('a \<rightarrow>! 'b) \<rightarrow> ('a \<rightarrow>! 'b)). approx_chain a"
    using bifinite [where 'a='a] and bifinite [where 'a='b]
    by (fast intro!: approx_chain_sfun_map)
qed

instance sprod :: (bifinite, bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> ('a \<otimes> 'b) \<rightarrow> ('a \<otimes> 'b)). approx_chain a"
    using bifinite [where 'a='a] and bifinite [where 'a='b]
    by (fast intro!: approx_chain_sprod_map)
qed

instance ssum :: (bifinite, bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> ('a \<oplus> 'b) \<rightarrow> ('a \<oplus> 'b)). approx_chain a"
    using bifinite [where 'a='a] and bifinite [where 'a='b]
    by (fast intro!: approx_chain_ssum_map)
qed

lemma approx_chain_unit: "approx_chain (\<bottom> :: nat \<Rightarrow> unit \<rightarrow> unit)"
by (simp add: approx_chain_def cfun_eq_iff finite_deflation_bottom)

instance unit :: bifinite
  by default (fast intro!: approx_chain_unit)

instance discr :: (countable) profinite
  by default (fast intro!: discr_approx)

instance lift :: (countable) bifinite
proof
  note [simp] = cont_Abs_lift cont_Rep_lift Rep_lift_inverse Abs_lift_inverse
  obtain a :: "nat \<Rightarrow> ('a discr)\<^sub>\<bottom> \<rightarrow> ('a discr)\<^sub>\<bottom>" where a: "approx_chain a"
    using profinite ..
  hence "approx_chain (\<lambda>i. (\<Lambda> y. Abs_lift y) oo a i oo (\<Lambda> x. Rep_lift x))"
    by (rule approx_chain_iso) simp_all
  thus "\<exists>(a::nat \<Rightarrow> 'a lift \<rightarrow> 'a lift). approx_chain a"
    by - (rule exI)
qed

end
