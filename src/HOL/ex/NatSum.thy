(*  Title:      HOL/ex/NatSum.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Summing natural numbers, squares, cubes, etc.

Originally demonstrated permutative rewriting, but add_ac is no longer
needed thanks to new simprocs.

Thanks to Sloane's On-Line Encyclopedia of Integer Sequences,
http://www.research.att.com/~njas/sequences/
*)

header {* Summing natural numbers *}

theory NatSum = Main:

declare lessThan_Suc [simp] atMost_Suc [simp]
declare add_mult_distrib [simp] add_mult_distrib2 [simp]
declare diff_mult_distrib [simp] diff_mult_distrib2 [simp]

text {*
  \medskip The sum of the first @{term n} odd numbers equals @{term n}
  squared.
*}

lemma sum_of_odds: "setsum (\<lambda>i. Suc (i + i)) (lessThan n) = n * n"
  apply (induct n)
   apply auto
  done


text {*
  \medskip The sum of the first @{text n} odd squares.
*}

lemma sum_of_odd_squares:
  "#3 * setsum (\<lambda>i. Suc (i + i) * Suc (i + i)) (lessThan n) =
    n * (#4 * n * n - #1)"
  apply (induct n)
  txt {* This removes the @{term "-#1"} from the inductive step *}
   apply (case_tac [2] n)
    apply auto
  done


text {*
  \medskip The sum of the first @{term n} odd cubes
*}

lemma sum_of_odd_cubes:
  "setsum (\<lambda>i. Suc (i + i) * Suc (i + i) * Suc (i + i)) (lessThan n) =
    n * n * (#2 * n * n - #1)"
  apply (induct "n")
  txt {* This removes the @{term "-#1"} from the inductive step *}
   apply (case_tac [2] "n")
    apply auto
  done

text {*
  \medskip The sum of the first @{term n} positive integers equals
  @{text "n (n + 1) / 2"}.*}

lemma sum_of_naturals:
    "#2 * setsum id (atMost n) = n * Suc n"
  apply (induct n)
   apply auto
  done

lemma sum_of_squares:
    "#6 * setsum (\<lambda>i. i * i) (atMost n) = n * Suc n * Suc (#2 * n)"
  apply (induct n)
   apply auto
  done

lemma sum_of_cubes:
    "#4 * setsum (\<lambda>i. i * i * i) (atMost n) = n * n * Suc n * Suc n"
  apply (induct n)
   apply auto
  done


text {*
  \medskip Sum of fourth powers: two versions.
*}

lemma sum_of_fourth_powers:
  "#30 * setsum (\<lambda>i. i * i * i * i) (atMost n) =
    n * Suc n * Suc (#2 * n) * (#3 * n * n + #3 * n - #1)"
  apply (induct n)
   apply auto
  txt {* Eliminates the subtraction *}
  apply (case_tac n)
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
  "#30 * int (setsum (\<lambda>i. i * i * i * i) (lessThan m)) =
    int m * (int m - #1) * (int (#2 * m) - #1) *
    (int (#3 * m * m) - int (#3 * m) - #1)"
  apply (induct m)
   apply simp_all
  done


text {*
  \medskip Sums of geometric series: 2, 3 and the general case *}

lemma sum_of_2_powers: "setsum (\<lambda>i. #2^i) (lessThan n) = #2^n - 1"
  apply (induct n)
   apply (auto split: nat_diff_split) 
  done

lemma sum_of_3_powers: "#2 * setsum (\<lambda>i. #3^i) (lessThan n) = #3^n - 1"
  apply (induct n)
   apply auto
  done

lemma sum_of_powers: "0 < k ==> (k - 1) * setsum (\<lambda>i. k^i) (lessThan n) = k^n - 1"
  apply (induct n)
   apply auto
  done

end
