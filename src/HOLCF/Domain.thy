(*  Title:      HOLCF/Domain.thy
    Author:     Brian Huffman
*)

header {* Domain package *}

theory Domain
imports Ssum Sprod Up One Tr Fixrec
uses
  ("Tools/cont_consts.ML")
  ("Tools/cont_proc.ML")
  ("Tools/Domain/domain_library.ML")
  ("Tools/Domain/domain_syntax.ML")
  ("Tools/Domain/domain_axioms.ML")
  ("Tools/Domain/domain_theorems.ML")
  ("Tools/Domain/domain_extender.ML")
begin

defaultsort pcpo


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

lemma (in iso) compact_abs_rev: "compact (abs\<cdot>x) \<Longrightarrow> compact x"
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


subsection {* Casedist *}

lemma ex_one_defined_iff:
  "(\<exists>x. P x \<and> x \<noteq> \<bottom>) = P ONE"
 apply safe
  apply (rule_tac p=x in oneE)
   apply simp
  apply simp
 apply force
 done

lemma ex_up_defined_iff:
  "(\<exists>x. P x \<and> x \<noteq> \<bottom>) = (\<exists>x. P (up\<cdot>x))"
 apply safe
  apply (rule_tac p=x in upE)
   apply simp
  apply fast
 apply (force intro!: up_defined)
 done

lemma ex_sprod_defined_iff:
 "(\<exists>y. P y \<and> y \<noteq> \<bottom>) =
  (\<exists>x y. (P (:x, y:) \<and> x \<noteq> \<bottom>) \<and> y \<noteq> \<bottom>)"
 apply safe
  apply (rule_tac p=y in sprodE)
   apply simp
  apply fast
 apply (force intro!: spair_defined)
 done

lemma ex_sprod_up_defined_iff:
 "(\<exists>y. P y \<and> y \<noteq> \<bottom>) =
  (\<exists>x y. P (:up\<cdot>x, y:) \<and> y \<noteq> \<bottom>)"
 apply safe
  apply (rule_tac p=y in sprodE)
   apply simp
  apply (rule_tac p=x in upE)
   apply simp
  apply fast
 apply (force intro!: spair_defined)
 done

lemma ex_ssum_defined_iff:
 "(\<exists>x. P x \<and> x \<noteq> \<bottom>) =
 ((\<exists>x. P (sinl\<cdot>x) \<and> x \<noteq> \<bottom>) \<or>
  (\<exists>x. P (sinr\<cdot>x) \<and> x \<noteq> \<bottom>))"
 apply (rule iffI)
  apply (erule exE)
  apply (erule conjE)
  apply (rule_tac p=x in ssumE)
    apply simp
   apply (rule disjI1, fast)
  apply (rule disjI2, fast)
 apply (erule disjE)
  apply force
 apply force
 done

lemma exh_start: "p = \<bottom> \<or> (\<exists>x. p = x \<and> x \<noteq> \<bottom>)"
  by auto

lemmas ex_defined_iffs =
   ex_ssum_defined_iff
   ex_sprod_up_defined_iff
   ex_sprod_defined_iff
   ex_up_defined_iff
   ex_one_defined_iff

text {* Rules for turning exh into casedist *}

lemma exh_casedist0: "\<lbrakk>R; R \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" (* like make_elim *)
  by auto

lemma exh_casedist1: "((P \<or> Q \<Longrightarrow> R) \<Longrightarrow> S) \<equiv> (\<lbrakk>P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> S)"
  by rule auto

lemma exh_casedist2: "(\<exists>x. P x \<Longrightarrow> Q) \<equiv> (\<And>x. P x \<Longrightarrow> Q)"
  by rule auto

lemma exh_casedist3: "(P \<and> Q \<Longrightarrow> R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> R)"
  by rule auto

lemmas exh_casedists = exh_casedist1 exh_casedist2 exh_casedist3


subsection {* Combinators for building copy functions *}

lemmas domain_map_stricts =
  ssum_map_strict sprod_map_strict u_map_strict

lemmas domain_map_simps =
  ssum_map_sinl ssum_map_sinr sprod_map_spair u_map_up


subsection {* Installing the domain package *}

lemmas con_strict_rules =
  sinl_strict sinr_strict spair_strict1 spair_strict2

lemmas con_defin_rules =
  sinl_defined sinr_defined spair_defined up_defined ONE_defined

lemmas con_defined_iff_rules =
  sinl_defined_iff sinr_defined_iff spair_strict_iff up_defined ONE_defined

use "Tools/cont_consts.ML"
use "Tools/cont_proc.ML"
use "Tools/Domain/domain_library.ML"
use "Tools/Domain/domain_syntax.ML"
use "Tools/Domain/domain_axioms.ML"
use "Tools/Domain/domain_theorems.ML"
use "Tools/Domain/domain_extender.ML"

end
