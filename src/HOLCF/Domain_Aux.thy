(*  Title:      HOLCF/Domain_Aux.thy
    Author:     Brian Huffman
*)

header {* Domain package support *}

theory Domain_Aux
imports Ssum Sprod Fixrec
uses
  ("Tools/Domain/domain_take_proofs.ML")
begin

subsection {* Continuous isomorphisms *}

text {* A locale for continuous isomorphisms *}

locale iso =
  fixes abs :: "'a \<rightarrow> 'b"
  fixes rep :: "'b \<rightarrow> 'a"
  assumes abs_iso [simp]: "rep\<cdot>(abs\<cdot>x) = x"
  assumes rep_iso [simp]: "abs\<cdot>(rep\<cdot>y) = y"
begin

lemma swap: "iso rep abs"
  by (rule iso.intro [OF rep_iso abs_iso])

lemma abs_below: "(abs\<cdot>x \<sqsubseteq> abs\<cdot>y) = (x \<sqsubseteq> y)"
proof
  assume "abs\<cdot>x \<sqsubseteq> abs\<cdot>y"
  then have "rep\<cdot>(abs\<cdot>x) \<sqsubseteq> rep\<cdot>(abs\<cdot>y)" by (rule monofun_cfun_arg)
  then show "x \<sqsubseteq> y" by simp
next
  assume "x \<sqsubseteq> y"
  then show "abs\<cdot>x \<sqsubseteq> abs\<cdot>y" by (rule monofun_cfun_arg)
qed

lemma rep_below: "(rep\<cdot>x \<sqsubseteq> rep\<cdot>y) = (x \<sqsubseteq> y)"
  by (rule iso.abs_below [OF swap])

lemma abs_eq: "(abs\<cdot>x = abs\<cdot>y) = (x = y)"
  by (simp add: po_eq_conv abs_below)

lemma rep_eq: "(rep\<cdot>x = rep\<cdot>y) = (x = y)"
  by (rule iso.abs_eq [OF swap])

lemma abs_strict: "abs\<cdot>\<bottom> = \<bottom>"
proof -
  have "\<bottom> \<sqsubseteq> rep\<cdot>\<bottom>" ..
  then have "abs\<cdot>\<bottom> \<sqsubseteq> abs\<cdot>(rep\<cdot>\<bottom>)" by (rule monofun_cfun_arg)
  then have "abs\<cdot>\<bottom> \<sqsubseteq> \<bottom>" by simp
  then show ?thesis by (rule UU_I)
qed

lemma rep_strict: "rep\<cdot>\<bottom> = \<bottom>"
  by (rule iso.abs_strict [OF swap])

lemma abs_defin': "abs\<cdot>x = \<bottom> \<Longrightarrow> x = \<bottom>"
proof -
  have "x = rep\<cdot>(abs\<cdot>x)" by simp
  also assume "abs\<cdot>x = \<bottom>"
  also note rep_strict
  finally show "x = \<bottom>" .
qed

lemma rep_defin': "rep\<cdot>z = \<bottom> \<Longrightarrow> z = \<bottom>"
  by (rule iso.abs_defin' [OF swap])

lemma abs_defined: "z \<noteq> \<bottom> \<Longrightarrow> abs\<cdot>z \<noteq> \<bottom>"
  by (erule contrapos_nn, erule abs_defin')

lemma rep_defined: "z \<noteq> \<bottom> \<Longrightarrow> rep\<cdot>z \<noteq> \<bottom>"
  by (rule iso.abs_defined [OF iso.swap]) (rule iso_axioms)

lemma abs_defined_iff: "(abs\<cdot>x = \<bottom>) = (x = \<bottom>)"
  by (auto elim: abs_defin' intro: abs_strict)

lemma rep_defined_iff: "(rep\<cdot>x = \<bottom>) = (x = \<bottom>)"
  by (rule iso.abs_defined_iff [OF iso.swap]) (rule iso_axioms)

lemma casedist_rule: "rep\<cdot>x = \<bottom> \<or> P \<Longrightarrow> x = \<bottom> \<or> P"
  by (simp add: rep_defined_iff)

lemma compact_abs_rev: "compact (abs\<cdot>x) \<Longrightarrow> compact x"
proof (unfold compact_def)
  assume "adm (\<lambda>y. \<not> abs\<cdot>x \<sqsubseteq> y)"
  with cont_Rep_CFun2
  have "adm (\<lambda>y. \<not> abs\<cdot>x \<sqsubseteq> abs\<cdot>y)" by (rule adm_subst)
  then show "adm (\<lambda>y. \<not> x \<sqsubseteq> y)" using abs_below by simp
qed

lemma compact_rep_rev: "compact (rep\<cdot>x) \<Longrightarrow> compact x"
  by (rule iso.compact_abs_rev [OF iso.swap]) (rule iso_axioms)

lemma compact_abs: "compact x \<Longrightarrow> compact (abs\<cdot>x)"
  by (rule compact_rep_rev) simp

lemma compact_rep: "compact x \<Longrightarrow> compact (rep\<cdot>x)"
  by (rule iso.compact_abs [OF iso.swap]) (rule iso_axioms)

lemma iso_swap: "(x = abs\<cdot>y) = (rep\<cdot>x = y)"
proof
  assume "x = abs\<cdot>y"
  then have "rep\<cdot>x = rep\<cdot>(abs\<cdot>y)" by simp
  then show "rep\<cdot>x = y" by simp
next
  assume "rep\<cdot>x = y"
  then have "abs\<cdot>(rep\<cdot>x) = abs\<cdot>y" by simp
  then show "x = abs\<cdot>y" by simp
qed

end


subsection {* Proofs about take functions *}

text {*
  This section contains lemmas that are used in a module that supports
  the domain isomorphism package; the module contains proofs related
  to take functions and the finiteness predicate.
*}

lemma deflation_abs_rep:
  fixes abs and rep and d
  assumes abs_iso: "\<And>x. rep\<cdot>(abs\<cdot>x) = x"
  assumes rep_iso: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
  shows "deflation d \<Longrightarrow> deflation (abs oo d oo rep)"
by (rule ep_pair.deflation_e_d_p) (simp add: ep_pair.intro assms)

lemma deflation_chain_min:
  assumes chain: "chain d"
  assumes defl: "\<And>n. deflation (d n)"
  shows "d m\<cdot>(d n\<cdot>x) = d (min m n)\<cdot>x"
proof (rule linorder_le_cases)
  assume "m \<le> n"
  with chain have "d m \<sqsubseteq> d n" by (rule chain_mono)
  then have "d m\<cdot>(d n\<cdot>x) = d m\<cdot>x"
    by (rule deflation_below_comp1 [OF defl defl])
  moreover from `m \<le> n` have "min m n = m" by simp
  ultimately show ?thesis by simp
next
  assume "n \<le> m"
  with chain have "d n \<sqsubseteq> d m" by (rule chain_mono)
  then have "d m\<cdot>(d n\<cdot>x) = d n\<cdot>x"
    by (rule deflation_below_comp2 [OF defl defl])
  moreover from `n \<le> m` have "min m n = n" by simp
  ultimately show ?thesis by simp
qed

lemma lub_ID_take_lemma:
  assumes "chain t" and "(\<Squnion>n. t n) = ID"
  assumes "\<And>n. t n\<cdot>x = t n\<cdot>y" shows "x = y"
proof -
  have "(\<Squnion>n. t n\<cdot>x) = (\<Squnion>n. t n\<cdot>y)"
    using assms(3) by simp
  then have "(\<Squnion>n. t n)\<cdot>x = (\<Squnion>n. t n)\<cdot>y"
    using assms(1) by (simp add: lub_distribs)
  then show "x = y"
    using assms(2) by simp
qed

lemma lub_ID_reach:
  assumes "chain t" and "(\<Squnion>n. t n) = ID"
  shows "(\<Squnion>n. t n\<cdot>x) = x"
using assms by (simp add: lub_distribs)


subsection {* Finiteness *}

text {*
  Let a ``decisive'' function be a deflation that maps every input to
  either itself or bottom.  Then if a domain's take functions are all
  decisive, then all values in the domain are finite.
*}

definition
  decisive :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool"
where
  "decisive d \<longleftrightarrow> (\<forall>x. d\<cdot>x = x \<or> d\<cdot>x = \<bottom>)"

lemma decisiveI: "(\<And>x. d\<cdot>x = x \<or> d\<cdot>x = \<bottom>) \<Longrightarrow> decisive d"
  unfolding decisive_def by simp

lemma decisive_cases:
  assumes "decisive d" obtains "d\<cdot>x = x" | "d\<cdot>x = \<bottom>"
using assms unfolding decisive_def by auto

lemma decisive_bottom: "decisive \<bottom>"
  unfolding decisive_def by simp

lemma decisive_ID: "decisive ID"
  unfolding decisive_def by simp

lemma decisive_ssum_map:
  assumes f: "decisive f"
  assumes g: "decisive g"
  shows "decisive (ssum_map\<cdot>f\<cdot>g)"
apply (rule decisiveI, rename_tac s)
apply (case_tac s, simp_all)
apply (rule_tac x=x in decisive_cases [OF f], simp_all)
apply (rule_tac x=y in decisive_cases [OF g], simp_all)
done

lemma decisive_sprod_map:
  assumes f: "decisive f"
  assumes g: "decisive g"
  shows "decisive (sprod_map\<cdot>f\<cdot>g)"
apply (rule decisiveI, rename_tac s)
apply (case_tac s, simp_all)
apply (rule_tac x=x in decisive_cases [OF f], simp_all)
apply (rule_tac x=y in decisive_cases [OF g], simp_all)
done

lemma decisive_abs_rep:
  fixes abs rep
  assumes iso: "iso abs rep"
  assumes d: "decisive d"
  shows "decisive (abs oo d oo rep)"
apply (rule decisiveI)
apply (rule_tac x="rep\<cdot>x" in decisive_cases [OF d])
apply (simp add: iso.rep_iso [OF iso])
apply (simp add: iso.abs_strict [OF iso])
done

lemma lub_ID_finite:
  assumes chain: "chain d"
  assumes lub: "(\<Squnion>n. d n) = ID"
  assumes decisive: "\<And>n. decisive (d n)"
  shows "\<exists>n. d n\<cdot>x = x"
proof -
  have 1: "chain (\<lambda>n. d n\<cdot>x)" using chain by simp
  have 2: "(\<Squnion>n. d n\<cdot>x) = x" using chain lub by (rule lub_ID_reach)
  have "\<forall>n. d n\<cdot>x = x \<or> d n\<cdot>x = \<bottom>"
    using decisive unfolding decisive_def by simp
  hence "range (\<lambda>n. d n\<cdot>x) \<subseteq> {x, \<bottom>}"
    by auto
  hence "finite (range (\<lambda>n. d n\<cdot>x))"
    by (rule finite_subset, simp)
  with 1 have "finite_chain (\<lambda>n. d n\<cdot>x)"
    by (rule finite_range_imp_finch)
  then have "\<exists>n. (\<Squnion>n. d n\<cdot>x) = d n\<cdot>x"
    unfolding finite_chain_def by (auto simp add: maxinch_is_thelub)
  with 2 show "\<exists>n. d n\<cdot>x = x" by (auto elim: sym)
qed

subsection {* ML setup *}

use "Tools/Domain/domain_take_proofs.ML"

end
