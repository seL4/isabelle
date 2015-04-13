(*  Title:      HOL/Library/Rewrite.thy
    Author:     Christoph Traut, Lars Noschinski, TU Muenchen

Proof method "rewrite" with support for subterm-selection based on patterns.
*)

theory Rewrite
imports Main
begin

consts rewrite_HOLE :: "'a::{}"
notation rewrite_HOLE ("HOLE")
notation rewrite_HOLE ("\<hole>")

lemma eta_expand:
  fixes f :: "'a::{} \<Rightarrow> 'b::{}"
  shows "f \<equiv> \<lambda>x. f x" .

ML_file "cconv.ML"
ML_file "rewrite.ML"

end
