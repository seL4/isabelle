(*  Title:      HOLCF/Domain.thy
    Author:     Brian Huffman
*)

header {* Domain package *}

theory Domain
imports Ssum Sprod Up One Tr Fixrec Representable
uses
  ("Tools/cont_consts.ML")
  ("Tools/cont_proc.ML")
  ("Tools/Domain/domain_constructors.ML")
  ("Tools/Domain/domain_library.ML")
  ("Tools/Domain/domain_axioms.ML")
  ("Tools/Domain/domain_theorems.ML")
  ("Tools/Domain/domain_extender.ML")
begin

defaultsort pcpo


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

lemmas con_below_iff_rules =
  sinl_below sinr_below sinl_below_sinr sinr_below_sinl con_defined_iff_rules

lemmas con_eq_iff_rules =
  sinl_eq sinr_eq sinl_eq_sinr sinr_eq_sinl con_defined_iff_rules

lemmas sel_strict_rules =
  cfcomp2 sscase1 sfst_strict ssnd_strict fup1

lemma sel_app_extra_rules:
  "sscase\<cdot>ID\<cdot>\<bottom>\<cdot>(sinr\<cdot>x) = \<bottom>"
  "sscase\<cdot>ID\<cdot>\<bottom>\<cdot>(sinl\<cdot>x) = x"
  "sscase\<cdot>\<bottom>\<cdot>ID\<cdot>(sinl\<cdot>x) = \<bottom>"
  "sscase\<cdot>\<bottom>\<cdot>ID\<cdot>(sinr\<cdot>x) = x"
  "fup\<cdot>ID\<cdot>(up\<cdot>x) = x"
by (cases "x = \<bottom>", simp, simp)+

lemmas sel_app_rules =
  sel_strict_rules sel_app_extra_rules
  ssnd_spair sfst_spair up_defined spair_defined

lemmas sel_defined_iff_rules =
  cfcomp2 sfst_defined_iff ssnd_defined_iff

lemmas take_con_rules =
  ssum_map_sinl' ssum_map_sinr' sprod_map_spair' u_map_up
  deflation_strict deflation_ID ID1 cfcomp2

use "Tools/cont_consts.ML"
use "Tools/cont_proc.ML"
use "Tools/Domain/domain_library.ML"
use "Tools/Domain/domain_axioms.ML"
use "Tools/Domain/domain_constructors.ML"
use "Tools/Domain/domain_theorems.ML"
use "Tools/Domain/domain_extender.ML"

end
