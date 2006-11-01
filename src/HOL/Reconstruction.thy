(*  Title:      HOL/Reconstruction.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   2004  University of Cambridge
*)

header{* Reconstructing external resolution proofs *}

theory Reconstruction
imports Hilbert_Choice Map Extraction
uses 	 "Tools/polyhash.ML"
	 "Tools/ATP/AtpCommunication.ML"
	 "Tools/ATP/watcher.ML"
         "Tools/ATP/reduce_axiomsN.ML"
         "Tools/res_clause.ML"
	 ("Tools/res_hol_clause.ML")
	 ("Tools/res_axioms.ML")
	 ("Tools/res_atp.ML")

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

use "Tools/res_axioms.ML"
use "Tools/res_hol_clause.ML"
use "Tools/res_atp.ML"

setup ResAxioms.meson_method_setup

end
