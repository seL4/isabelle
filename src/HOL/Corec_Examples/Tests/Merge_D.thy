(*  Title:      HOL/Corec_Examples/Tests/Merge_D.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Tests theory merges.
*)

section \<open>Tests Theory Merges\<close>

theory Merge_D
imports Merge_B Merge_C
begin

thm ta.coinduct_upto

(* Merges files having defined their own friends and uses these friends to
define another corecursive function. *)

corec gd where
  "gd = fc (gc (gb (fb (ga (Ca 0 gd)))))"

thm gd_def

term fc

corec hd :: "('a::zero) ta \<Rightarrow> 'a ta" where
  "hd s = fc (gc (gb (fb (ga (Ca 0 (hd s))))))"

friend_of_corec hd where
  "hd s = Ca 0 (fc (gc (gb (fb (ga (Ca 0 (hd s)))))))"
  sorry

corecursive (friend) ff :: "'a ta \<Rightarrow> 'a ta" where
  "ff x = Ca undefined (ff x)"
  sorry

thm ta.cong_intros
thm ta.cong_gb

end
