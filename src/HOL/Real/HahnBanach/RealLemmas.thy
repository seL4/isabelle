(*  Title:      HOL/Real/HahnBanach/RealLemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Auxiliary theorems *}

theory RealLemmas = Real:

lemma real_mult_diff_distrib:
  "a * (- x - (y::real)) = - a * x - a * y"
proof -
  have "- x - y = - x + - y" by simp
  also have "a * ... = a * - x + a * - y"
    by (simp only: right_distrib)
  also have "... = - a * x - a * y"
    by simp
  finally show ?thesis .
qed

lemma real_mult_diff_distrib2: 
  "a * (x - (y::real)) = a * x - a * y"
proof -
  have "x - y = x + - y" by simp
  also have "a * ... = a * x + a * - y"
    by (simp only: right_distrib)
  also have "... = a * x - a * y"
    by simp
  finally show ?thesis .
qed

end
