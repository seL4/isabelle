(*  Title:      HOL/ATP_Linkup.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Author:     Jia Meng, NICTA
*)

header{* The Isabelle-ATP Linkup *}

theory ATP_Linkup
imports Divides Record Hilbert_Choice
uses
  "Tools/polyhash.ML"
  "Tools/res_clause.ML"
  "Tools/ATP/reduce_axiomsN.ML"
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

constdefs
  COMBI :: "'a => 'a"
    "COMBI P == P"

  COMBK :: "'a => 'b => 'a"
    "COMBK P Q == P"

  COMBB :: "('b => 'c) => ('a => 'b) => 'a => 'c"
    "COMBB P Q R == P (Q R)"

  COMBC :: "('a => 'b => 'c) => 'b => 'a => 'c"
    "COMBC P Q R == P R Q"

  COMBS :: "('a => 'b => 'c) => ('a => 'b) => 'a => 'c"
    "COMBS P Q R == P R (Q R)"

  COMBB' :: "('a => 'c) => ('b => 'a) => ('d => 'b) => 'd => 'c"
    "COMBB' M P Q R == M (P (Q R))"

  COMBC' :: "('a => 'b => 'c) => ('d => 'a) => 'b => 'd => 'c"
    "COMBC' M P Q R == M (P R) Q"

  COMBS' :: "('a => 'b => 'c) => ('d => 'a) => ('d => 'b) => 'd => 'c"
    "COMBS' M P Q R == M (P R) (Q R)"

  fequal :: "'a => 'a => bool"
    "fequal X Y == (X=Y)"

lemma fequal_imp_equal: "fequal X Y ==> X=Y"
  by (simp add: fequal_def)

lemma equal_imp_fequal: "X=Y ==> fequal X Y"
  by (simp add: fequal_def)

lemma K_simp: "COMBK P == (%Q. P)"
apply (rule eq_reflection)
apply (rule ext)
apply (simp add: COMBK_def)
done

lemma I_simp: "COMBI == (%P. P)"
apply (rule eq_reflection)
apply (rule ext)
apply (simp add: COMBI_def)
done

lemma B_simp: "COMBB P Q == %R. P (Q R)"
apply (rule eq_reflection)
apply (rule ext)
apply (simp add: COMBB_def)
done

text{*These two represent the equivalence between Boolean equality and iff.
They can't be converted to clauses automatically, as the iff would be
expanded...*}

lemma iff_positive: "P | Q | P=Q"
by blast

lemma iff_negative: "~P | ~Q | P=Q"
by blast

use "Tools/res_axioms.ML"      --{*requires the combinators declared above*}
use "Tools/res_hol_clause.ML"  --{*requires the combinators*}
use "Tools/res_reconstruct.ML"
use "Tools/watcher.ML"
use "Tools/res_atp.ML"

setup ResAxioms.meson_method_setup


subsection {* Setup for Vampire, E prover and SPASS *}

use "Tools/res_atp_provers.ML"

oracle vampire_oracle ("string * int") = {* ResAtpProvers.vampire_o *}
oracle eprover_oracle ("string * int") = {* ResAtpProvers.eprover_o *}
oracle spass_oracle ("string * int") = {* ResAtpProvers.spass_o *}

use "Tools/res_atp_methods.ML"
setup ResAtpMethods.ResAtps_setup


subsection {* The Metis prover *}

use "Tools/metis_tools.ML"
setup MetisTools.setup

end
