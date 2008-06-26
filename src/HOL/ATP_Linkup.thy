(*  Title:      HOL/ATP_Linkup.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Author:     Jia Meng, NICTA
*)

header{* The Isabelle-ATP Linkup *}

theory ATP_Linkup
imports Record Hilbert_Choice
uses
  "Tools/polyhash.ML"
  "Tools/res_clause.ML"
  ("Tools/res_hol_clause.ML")
  ("Tools/res_axioms.ML")
  ("Tools/res_reconstruct.ML")
  ("Tools/watcher.ML")
  ("Tools/res_atp.ML")
  ("Tools/res_atp_provers.ML")
  ("Tools/res_atp_methods.ML")
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


subsection {* Setup of Vampire, E prover and SPASS *}

use "Tools/res_axioms.ML"      --{*requires the combinators declared above*}
setup ResAxioms.setup

use "Tools/res_hol_clause.ML"
use "Tools/res_reconstruct.ML"
use "Tools/watcher.ML"
use "Tools/res_atp.ML"

use "Tools/res_atp_provers.ML"

oracle vampire_oracle ("string * int") = {* ResAtpProvers.vampire_o *}
oracle eprover_oracle ("string * int") = {* ResAtpProvers.eprover_o *}
oracle spass_oracle ("string * int") = {* ResAtpProvers.spass_o *}

use "Tools/res_atp_methods.ML"
setup ResAtpMethods.setup      --{*Oracle ATP methods: still useful?*}
setup ResReconstruct.setup     --{*Config parameters*}


subsection {* The Metis prover *}

use "Tools/metis_tools.ML"
setup MetisTools.setup

end
