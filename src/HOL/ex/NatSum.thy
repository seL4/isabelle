(* Title: HOL/ex/NatSum.ML
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header {* Summing natural numbers *}

theory NatSum = Main:

text {*
  Summing natural numbers, squares, cubes, etc.

  Originally demonstrated permutative rewriting, but @{thm [source]
  add_ac} is no longer needed thanks to new simprocs.

  Thanks to Sloane's On-Line Encyclopedia of Integer Sequences,
  \url{http://www.research.att.com/~njas/sequences/}.
*}

lemmas [simp] =
  lessThan_Suc atMost_Suc setsum_op_ivl_Suc setsum_cl_ivl_Suc
  left_distrib right_distrib
  left_diff_distrib right_diff_distrib --{*for true subtraction*}
  diff_mult_distrib diff_mult_distrib2 --{*for type nat*}

text {*
  \medskip The sum of the first @{text n} odd numbers equals @{text n}
  squared.
*}

lemma sum_of_odds: "(\<Sum>i \<in> {0..<n}. Suc (i + i)) = n * n"
  apply (induct n)
   apply auto
  done


text {*
  \medskip The sum of the first @{text n} odd squares.
*}

lemma sum_of_odd_squares:
  "3 * (\<Sum>i=0..<n. Suc(2*i) * Suc(2*i)) = n * (4 * n * n - 1)"
  apply (induct n)
   apply (auto split: nat_diff_split) (*eliminate the subtraction*)
  done


text {*
  \medskip The sum of the first @{text n} odd cubes
*}

lemma numeral_2_eq_2: "2 = Suc (Suc 0)" by auto

lemma sum_of_odd_cubes:
  "(\<Sum>i=0..<n. Suc (2*i) * Suc (2*i) * Suc (2*i)) =
    n * n * (2 * n * n - 1)"
  apply (induct n)
   apply (auto split: nat_diff_split) (*eliminate the subtraction*)
  done

text {*
  \medskip The sum of the first @{text n} positive integers equals
  @{text "n (n + 1) / 2"}.*}

lemma sum_of_naturals:
    "2 * (\<Sum>i=0..n. i) = n * Suc n"
  apply (induct n)
   apply auto
  done

lemma sum_of_squares:
    "6 * (\<Sum>i=0..n. i * i) = n * Suc n * Suc (2 * n)"
  apply (induct n)
   apply auto
  done

lemma sum_of_cubes:
    "4 * (\<Sum>i=0..n. i * i * i) = n * n * Suc n * Suc n"
  apply (induct n)
   apply auto
  done


text {*
  \medskip Sum of fourth powers: three versions.
*}

lemma sum_of_fourth_powers:
  "30 * (\<Sum>i=0..n. i * i * i * i) =
    n * Suc n * Suc (2 * n) * (3 * n * n + 3 * n - 1)"
  apply (induct n)
   apply simp_all
  apply (case_tac n)  -- {* eliminates the subtraction *} 
   apply (simp_all (no_asm_simp))
  done

text {*
  Tow alternative proofs, with a change of variables and much more
  subtraction, performed using the integers. *}

lemma int_sum_of_fourth_powers:
  "30 * int (\<Sum>i=0..<m. i * i * i * i) =
    int m * (int m - 1) * (int(2 * m) - 1) *
    (int(3 * m * m) - int(3 * m) - 1)"
  apply (induct m)
   apply (simp_all add:zmult_int[symmetric])
  done

lemma of_nat_sum_of_fourth_powers:
  "30 * of_nat (\<Sum>i=0..<m. i * i * i * i) =
    of_nat m * (of_nat m - 1) * (of_nat (2 * m) - 1) *
    (of_nat (3 * m * m) - of_nat (3 * m) - (1::int))"
  apply (induct m)
   apply simp_all
  done


text {*
  \medskip Sums of geometric series: @{text 2}, @{text 3} and the
  general case.
*}

lemma sum_of_2_powers: "(\<Sum>i=0..<n. 2^i) = 2^n - (1::nat)"
  apply (induct n)
   apply (auto split: nat_diff_split)
  done

lemma sum_of_3_powers: "2 * (\<Sum>i=0..<n. 3^i) = 3^n - (1::nat)"
  apply (induct n)
   apply auto
  done

lemma sum_of_powers: "0 < k ==> (k - 1) * (\<Sum>i=0..<n. k^i) = k^n - (1::nat)"
  apply (induct n)
   apply auto
  done

end
