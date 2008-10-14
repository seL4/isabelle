(*  Title:      HOL/ATP_Linkup.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Author:     Jia Meng, NICTA
    Author:     Fabian Immler, TUM
*)

header {* The Isabelle-ATP Linkup *}

theory ATP_Linkup
imports Record Hilbert_Choice
uses
  "Tools/polyhash.ML"
  "Tools/res_clause.ML"
  ("Tools/res_axioms.ML")
  ("Tools/res_hol_clause.ML")
  ("Tools/res_reconstruct.ML")
  ("Tools/res_atp.ML")
  ("Tools/atp_manager.ML")
  ("Tools/atp_thread.ML")
  "~~/src/Tools/Metis/metis.ML"
  ("Tools/metis_tools.ML")
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

use "Tools/res_axioms.ML" setup ResAxioms.setup
use "Tools/res_hol_clause.ML"
use "Tools/res_reconstruct.ML" setup ResReconstruct.setup
use "Tools/res_atp.ML"

use "Tools/atp_manager.ML"
use "Tools/atp_thread.ML"

text {* basic provers *}
setup {* AtpManager.add_prover "spass" AtpThread.spass *}
setup {* AtpManager.add_prover "vampire" AtpThread.vampire *}
setup {* AtpManager.add_prover "e" AtpThread.eprover *}

text {* provers with stuctured output *}
setup {* AtpManager.add_prover "vampire_full" AtpThread.vampire_full *}
setup {* AtpManager.add_prover "e_full" AtpThread.eprover_full *}

text {* on some problems better results *}
setup {* AtpManager.add_prover "spass_no_tc" (AtpThread.spass_filter_opts 40 false) *}

text {* remote provers via SystemOnTPTP *}
setup {* AtpManager.add_prover "remote_vamp9"
  (AtpThread.remote_prover "Vampire---9.0" "jumpirefix --output_syntax tptp --mode casc -t 3600") *}
setup {* AtpManager.add_prover "remote_vamp10"
  (AtpThread.remote_prover "Vampire---10.0" "drakosha.pl 60") *}


subsection {* The Metis prover *}

use "Tools/metis_tools.ML"
setup MetisTools.setup

end
