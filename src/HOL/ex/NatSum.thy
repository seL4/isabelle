(*  Title:      HOL/ex/NatSum.ML
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

declare lessThan_Suc [simp] atMost_Suc [simp]
declare add_mult_distrib [simp] add_mult_distrib2 [simp]
declare diff_mult_distrib [simp] diff_mult_distrib2 [simp]

text {*
  \medskip The sum of the first @{text n} odd numbers equals @{text n}
  squared.
*}

lemma sum_of_odds: "(\<Sum>i \<in> {..n(}. Suc (i + i)) = n * n"
  apply (induct n)
   apply auto
  done


text {*
  \medskip The sum of the first @{text n} odd squares.
*}

lemma sum_of_odd_squares:
  "3 * (\<Sum>i \<in> {..n(}. Suc (i + i) * Suc (i + i)) =
    n * (4 * n * n - 1)"
  apply (induct n)
   apply (case_tac [2] n)  -- {* eliminates the subtraction *}
    apply auto
  done


text {*
  \medskip The sum of the first @{text n} odd cubes
*}

lemma sum_of_odd_cubes:
  "(\<Sum>i \<in> {..n(}. Suc (i + i) * Suc (i + i) * Suc (i + i)) =
    n * n * (2 * n * n - 1)"
  apply (induct n)
   apply (case_tac [2] n)  -- {* eliminates the subtraction *}
    apply auto
  done

text {*
  \medskip The sum of the first @{text n} positive integers equals
  @{text "n (n + 1) / 2"}.*}

lemma sum_of_naturals:
    "2 * (\<Sum>i \<in> {..n}. i) = n * Suc n"
  apply (induct n)
   apply auto
  done

lemma sum_of_squares:
    "6 * (\<Sum>i \<in> {..n}. i * i) = n * Suc n * Suc (2 * n)"
  apply (induct n)
   apply auto
  done

lemma sum_of_cubes:
    "4 * (\<Sum>i \<in> {..n}. i * i * i) = n * n * Suc n * Suc n"
  apply (induct n)
   apply auto
  done


text {*
  \medskip Sum of fourth powers: two versions.
*}

lemma sum_of_fourth_powers:
  "30 * (\<Sum>i \<in> {..n}. i * i * i * i) =
    n * Suc n * Suc (2 * n) * (3 * n * n + 3 * n - 1)"
  apply (induct n)
   apply auto
  apply (case_tac n)  -- {* eliminates the subtraction *}
   apply simp_all
  done

text {*
  Alternative proof, with a change of variables and much more
  subtraction, performed using the integers. *}

declare
  zmult_int [symmetric, simp]
  zadd_zmult_distrib [simp]
  zadd_zmult_distrib2 [simp]
  zdiff_zmult_distrib [simp]
  zdiff_zmult_distrib2 [simp]

lemma int_sum_of_fourth_powers:
  "30 * int (\<Sum>i \<in> {..m(}. i * i * i * i) =
    int m * (int m - 1) * (int (2 * m) - 1) *
    (int (3 * m * m) - int (3 * m) - 1)"
  apply (induct m)
   apply simp_all
  done


text {*
  \medskip Sums of geometric series: @{text 2}, @{text 3} and the
  general case.
*}

lemma sum_of_2_powers: "(\<Sum>i \<in> {..n(}. 2^i) = 2^n - (1::nat)"
  apply (induct n)
   apply (auto split: nat_diff_split)
  done

lemma sum_of_3_powers: "2 * (\<Sum>i \<in> {..n(}. 3^i) = 3^n - (1::nat)"
  apply (induct n)
   apply auto
  done

lemma sum_of_powers: "0 < k ==> (k - 1) * (\<Sum>i \<in> {..n(}. k^i) = k^n - (1::nat)"
  apply (induct n)
   apply auto
  done

end
