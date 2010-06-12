(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C Paulson
    Author:     Jia Meng, NICTA
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory Sledgehammer
imports Plain Hilbert_Choice
uses
  "~~/src/Tools/Metis/metis.ML"
  "Tools/Sledgehammer/sledgehammer_util.ML"
  ("Tools/Sledgehammer/sledgehammer_fol_clause.ML")
  ("Tools/Sledgehammer/sledgehammer_fact_preprocessor.ML")
  ("Tools/Sledgehammer/sledgehammer_hol_clause.ML")
  ("Tools/Sledgehammer/sledgehammer_proof_reconstruct.ML")
  ("Tools/Sledgehammer/sledgehammer_fact_filter.ML")
  ("Tools/ATP_Manager/atp_manager.ML")
  ("Tools/ATP_Manager/atp_systems.ML")
  ("Tools/Sledgehammer/sledgehammer_fact_minimizer.ML")
  ("Tools/Sledgehammer/sledgehammer_isar.ML")
  ("Tools/Sledgehammer/meson_tactic.ML")
  ("Tools/Sledgehammer/metis_tactics.ML")
begin

definition skolem_Eps :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
[no_atp]: "skolem_Eps = Eps"

lemma skolem_someI_ex [no_atp]: "\<exists>x. P x \<Longrightarrow> P (skolem_Eps (\<lambda>x. P x))"
unfolding skolem_Eps_def by (rule someI_ex)

definition COMBI :: "'a \<Rightarrow> 'a" where
[no_atp]: "COMBI P \<equiv> P"

definition COMBK :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
[no_atp]: "COMBK P Q \<equiv> P"

definition COMBB :: "('b => 'c) \<Rightarrow> ('a => 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where [no_atp]:
"COMBB P Q R \<equiv> P (Q R)"

definition COMBC :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
[no_atp]: "COMBC P Q R \<equiv> P R Q"

definition COMBS :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
[no_atp]: "COMBS P Q R \<equiv> P R (Q R)"

definition fequal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where [no_atp]:
"fequal X Y \<equiv> (X = Y)"

lemma fequal_imp_equal [no_atp]: "fequal X Y \<Longrightarrow> X = Y"
  by (simp add: fequal_def)

lemma equal_imp_fequal [no_atp]: "X = Y \<Longrightarrow> fequal X Y"
  by (simp add: fequal_def)

text{*These two represent the equivalence between Boolean equality and iff.
They can't be converted to clauses automatically, as the iff would be
expanded...*}

lemma iff_positive: "P \<or> Q \<or> P = Q"
by blast

lemma iff_negative: "\<not> P \<or> \<not> Q \<or> P = Q"
by blast

text{*Theorems for translation to combinators*}

lemma abs_S [no_atp]: "\<lambda>x. (f x) (g x) \<equiv> COMBS f g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBS_def) 
done

lemma abs_I [no_atp]: "\<lambda>x. x \<equiv> COMBI"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBI_def) 
done

lemma abs_K [no_atp]: "\<lambda>x. y \<equiv> COMBK y"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBK_def) 
done

lemma abs_B [no_atp]: "\<lambda>x. a (g x) \<equiv> COMBB a g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBB_def) 
done

lemma abs_C [no_atp]: "\<lambda>x. (f x) b \<equiv> COMBC f b"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBC_def) 
done


subsection {* Setup of external ATPs *}

use "Tools/Sledgehammer/sledgehammer_fol_clause.ML"
use "Tools/Sledgehammer/sledgehammer_fact_preprocessor.ML"
setup Sledgehammer_Fact_Preprocessor.setup
use "Tools/Sledgehammer/sledgehammer_hol_clause.ML"
use "Tools/Sledgehammer/sledgehammer_proof_reconstruct.ML"
use "Tools/Sledgehammer/sledgehammer_fact_filter.ML"
use "Tools/ATP_Manager/atp_manager.ML"
use "Tools/ATP_Manager/atp_systems.ML"
setup ATP_Systems.setup
use "Tools/Sledgehammer/sledgehammer_fact_minimizer.ML"
use "Tools/Sledgehammer/sledgehammer_isar.ML"
setup Sledgehammer_Isar.setup


subsection {* The MESON prover *}

use "Tools/Sledgehammer/meson_tactic.ML"
setup Meson_Tactic.setup


subsection {* The Metis prover *}

use "Tools/Sledgehammer/metis_tactics.ML"
setup Metis_Tactics.setup

end
