(*  Title:      HOL/Alethe_Arith_Rewrites_Lemmas.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_Arith_Rewrites_Lemmas
  imports "Alethe_Rare_Nary_Ops"
begin

(*TODO: Find better proofs eventually*)

lemma arith_plus_zero_lemma:
  shows "foldr (+) xs (0::int) + (a + foldr (+) ys 0) = foldr (+) xs (a + foldr (+) ys 0)"
  apply (induction xs)
  by simp_all

lemma arith_mul_one_lemma:
  shows "a = (0::int) \<or> foldr (*) ts (1::int) * (aa * foldr (*) ss (1::int)) = foldr (*) ts (aa * foldr (*) ss (1::int))"
  apply (induction ts)
   apply simp_all
  by blast

lemma arith_mul_zero_lemma:
  shows
  "a = (0::int) \<or> foldr (*) ts (0::int) = (0::int)"
  "foldr (*) ts (0::int) = (0::int) \<or> a = (0::int) \<or> foldr (*) ss (1::int) = (0::int)"
  apply (metis arith_mul_one_lemma mult_zero_left mult_zero_right)
  by (metis arith_mul_one_lemma times_int_code(1) times_int_code(2))

lemma arith_plus_flatten_lemma:
 shows
 "foldr (+) xss (w + (aa + foldr (+) yss (0::int))) = foldr (+) xss w + (aa + foldr (+) yss (0::int))"
 "foldr (+) xss (w + foldr (+) yss (0::int)) = foldr (+) xss w + foldr (+) yss (0::int)"
  apply (metis (no_types, opaque_lifting) add.assoc add_cancel_right_right arith_mul_one_lemma arith_plus_zero_lemma foldr.simps(1) mult_zero_left ring_class.ring_distribs(1))
  by (metis ab_semigroup_add_class.add_ac(1) add.right_neutral arith_plus_zero_lemma foldr.simps(1) id_apply)

lemma arith_mult_flatten_lemma:
  shows
 "a = (0::int) \<or> foldr (*) xss (w * (aa * foldr (*) yss (1::int))) = foldr (*) xss w * (aa * foldr (*) yss (1::int))"
 "a = (0::int) \<or> foldr (*) zss (1::int) = (0::int) \<or> foldr (*) xss (w * foldr (*) yss (1::int)) = foldr (*) xss w * foldr (*) yss (1::int)"
   apply (case_tac [!] "a = 0")
     apply simp_all
  apply (metis (no_types, opaque_lifting) arith_mul_one_lemma foldr.simps(1) id_apply mult.assoc mult.right_neutral)
  apply (case_tac [!] "foldr (*) zss (1::int) = (0::int)")
   apply simp_all
proof -
  have "\<forall>i is ia. foldr (*) is (1::int) * ia = foldr (*) is ia \<or> (0::int) = i"
    by (metis arith_mul_one_lemma foldr.simps(1) id_apply mult.right_neutral)
  then show "foldr (*) xss (w * foldr (*) yss 1) = foldr (*) xss w * foldr (*) yss 1"
    by (metis (no_types) mult.left_commute mult.right_neutral)
qed

lemma arith_mult_dist_lemma:
  shows
 "x * (y + z) = x * y + x * z"
 "x * (y + z + (a + foldr (+) ws (0::int))) = x * y + x * (z + (a + foldr (+) ws (0::int)))"
  by (simp_all add: distrib_left)

lemma arith_plus_cancel1_lemma:
  shows
 "foldr (+) ts x - x = foldr (+) ts (0::int)"
 "foldr (+) ts x + (a + foldr (+) ss (0::int)) - x = foldr (+) ts (a + foldr (+) ss (0::int))"
 "foldr (+) ts x + foldr (+) ss (0::int) - x = foldr (+) ts (foldr (+) ss (0::int))"
    apply (induction ts)
  by simp_all

lemma arith_plus_cancel2_lemma:
  shows
 "foldr (+) ts (- x) + x = foldr (+) ts (0::int)"
 "foldr (+) ts (- x) + (a + foldr (+) ss (0::int)) + x = foldr (+) ts (a + foldr (+) ss (0::int))"
 "foldr (+) ts (- x) + foldr (+) ss (0::int) + x = foldr (+) ts (foldr (+) ss (0::int))"
  apply (induction ts)
  by simp_all

end
