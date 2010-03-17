(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C Paulson
    Author:     Jia Meng, NICTA
    Author:     Fabian Immler, TUM
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory Sledgehammer
imports Plain Hilbert_Choice
uses
  "Tools/polyhash.ML"
  "Tools/Sledgehammer/sledgehammer_fol_clause.ML"
  ("Tools/Sledgehammer/sledgehammer_fact_preprocessor.ML")
  ("Tools/Sledgehammer/sledgehammer_hol_clause.ML")
  ("Tools/Sledgehammer/sledgehammer_proof_reconstruct.ML")
  ("Tools/Sledgehammer/sledgehammer_fact_filter.ML")
  ("Tools/ATP_Manager/atp_manager.ML")
  ("Tools/ATP_Manager/atp_wrapper.ML")
  ("Tools/ATP_Manager/atp_minimal.ML")
  "~~/src/Tools/Metis/metis.ML"
  ("Tools/Sledgehammer/metis_tactics.ML")
begin

definition COMBI :: "'a => 'a"
  where "COMBI P == P"

definition COMBK :: "'a => 'b => 'a"
  where "COMBK P Q == P"

definition COMBB :: "('b => 'c) => ('a => 'b) => 'a => 'c"
  where "COMBB P Q R == P (Q R)"

definition COMBC :: "('a => 'b => 'c) => 'b => 'a => 'c"
  where "COMBC P Q R == P R Q"

definition COMBS :: "('a => 'b => 'c) => ('a => 'b) => 'a => 'c"
  where "COMBS P Q R == P R (Q R)"

definition fequal :: "'a => 'a => bool"
  where "fequal X Y == (X=Y)"

lemma fequal_imp_equal: "fequal X Y ==> X=Y"
  by (simp add: fequal_def)

lemma equal_imp_fequal: "X=Y ==> fequal X Y"
  by (simp add: fequal_def)

text{*These two represent the equivalence between Boolean equality and iff.
They can't be converted to clauses automatically, as the iff would be
expanded...*}

lemma iff_positive: "P | Q | P=Q"
by blast

lemma iff_negative: "~P | ~Q | P=Q"
by blast

text{*Theorems for translation to combinators*}

lemma abs_S: "(%x. (f x) (g x)) == COMBS f g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBS_def) 
done

lemma abs_I: "(%x. x) == COMBI"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBI_def) 
done

lemma abs_K: "(%x. y) == COMBK y"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBK_def) 
done

lemma abs_B: "(%x. a (g x)) == COMBB a g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBB_def) 
done

lemma abs_C: "(%x. (f x) b) == COMBC f b"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBC_def) 
done


subsection {* Setup of external ATPs *}

use "Tools/Sledgehammer/sledgehammer_fact_preprocessor.ML"
setup Sledgehammer_Fact_Preprocessor.setup
use "Tools/Sledgehammer/sledgehammer_hol_clause.ML"
use "Tools/Sledgehammer/sledgehammer_proof_reconstruct.ML"
setup Sledgehammer_Proof_Reconstruct.setup
use "Tools/Sledgehammer/sledgehammer_fact_filter.ML"

use "Tools/ATP_Manager/atp_wrapper.ML"
setup ATP_Wrapper.setup
use "Tools/ATP_Manager/atp_manager.ML"
use "Tools/ATP_Manager/atp_minimal.ML"

text {* basic provers *}
setup {* ATP_Manager.add_prover ATP_Wrapper.spass *}
setup {* ATP_Manager.add_prover ATP_Wrapper.vampire *}
setup {* ATP_Manager.add_prover ATP_Wrapper.eprover *}

text {* provers with stuctured output *}
setup {* ATP_Manager.add_prover ATP_Wrapper.vampire_full *}
setup {* ATP_Manager.add_prover ATP_Wrapper.eprover_full *}

text {* on some problems better results *}
setup {* ATP_Manager.add_prover ATP_Wrapper.spass_no_tc *}

text {* remote provers via SystemOnTPTP *}
setup {* ATP_Manager.add_prover ATP_Wrapper.remote_vampire *}
setup {* ATP_Manager.add_prover ATP_Wrapper.remote_spass *}
setup {* ATP_Manager.add_prover ATP_Wrapper.remote_eprover *}
  


subsection {* The Metis prover *}

use "Tools/Sledgehammer/metis_tactics.ML"
setup Metis_Tactics.setup

end
