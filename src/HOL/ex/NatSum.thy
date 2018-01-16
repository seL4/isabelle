(*  Title:      HOL/ex/NatSum.thy
    Author:     Tobias Nipkow
*)

section \<open>Summing natural numbers\<close>

theory NatSum
  imports Main
begin

text \<open>
  Summing natural numbers, squares, cubes, etc.

  Thanks to Sloane's On-Line Encyclopedia of Integer Sequences,
  \<^url>\<open>http://oeis.org\<close>.
\<close>

lemmas [simp] =
  ring_distribs
  diff_mult_distrib diff_mult_distrib2 \<comment> \<open>for type nat\<close>


text \<open>\<^medskip> The sum of the first \<open>n\<close> odd numbers equals \<open>n\<close> squared.\<close>

lemma sum_of_odds: "(\<Sum>i=0..<n. Suc (i + i)) = n * n"
  by (induct n) auto


text \<open>\<^medskip> The sum of the first \<open>n\<close> odd squares.\<close>

lemma sum_of_odd_squares:
  "3 * (\<Sum>i=0..<n. Suc(2*i) * Suc(2*i)) = n * (4 * n * n - 1)"
  by (induct n) auto


text \<open>\<^medskip> The sum of the first \<open>n\<close> odd cubes.\<close>

lemma sum_of_odd_cubes:
  "(\<Sum>i=0..<n. Suc (2*i) * Suc (2*i) * Suc (2*i)) =
    n * n * (2 * n * n - 1)"
  by (induct n) auto


text \<open>\<^medskip> The sum of the first \<open>n\<close> positive integers equals \<open>n (n + 1) / 2\<close>.\<close>

lemma sum_of_naturals: "2 * (\<Sum>i=0..n. i) = n * Suc n"
  by (induct n) auto

lemma sum_of_squares: "6 * (\<Sum>i=0..n. i * i) = n * Suc n * Suc (2 * n)"
  by (induct n) auto

lemma sum_of_cubes: "4 * (\<Sum>i=0..n. i * i * i) = n * n * Suc n * Suc n"
  by (induct n) auto


text \<open>\<^medskip> A cute identity:\<close>

lemma sum_squared: "(\<Sum>i=0..n. i)^2 = (\<Sum>i=0..n. i^3)" for n :: nat
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "(\<Sum>i = 0..Suc n. i)^2 =
        (\<Sum>i = 0..n. i^3) + (2*(\<Sum>i = 0..n. i)*(n+1) + (n+1)^2)"
    (is "_ = ?A + ?B")
    using Suc by (simp add: eval_nat_numeral)
  also have "?B = (n+1)^3"
    using sum_of_naturals by (simp add: eval_nat_numeral)
  also have "?A + (n+1)^3 = (\<Sum>i=0..Suc n. i^3)" by simp
  finally show ?case .
qed


text \<open>\<^medskip> Sum of fourth powers: three versions.\<close>

lemma sum_of_fourth_powers:
  "30 * (\<Sum>i=0..n. i * i * i * i) =
    n * Suc n * Suc (2 * n) * (3 * n * n + 3 * n - 1)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case
    by (cases n)  \<comment> \<open>eliminates the subtraction\<close>
      simp_all
qed

text \<open>
  Two alternative proofs, with a change of variables and much more
  subtraction, performed using the integers.
\<close>

lemma int_sum_of_fourth_powers:
  "30 * int (\<Sum>i=0..<m. i * i * i * i) =
    int m * (int m - 1) * (int(2 * m) - 1) *
    (int(3 * m * m) - int(3 * m) - 1)"
  by (induct m) simp_all

lemma of_nat_sum_of_fourth_powers:
  "30 * of_nat (\<Sum>i=0..<m. i * i * i * i) =
    of_nat m * (of_nat m - 1) * (of_nat (2 * m) - 1) *
    (of_nat (3 * m * m) - of_nat (3 * m) - (1::int))"
  by (induct m) simp_all


text \<open>\<^medskip> Sums of geometric series: \<open>2\<close>, \<open>3\<close> and the general case.\<close>

lemma sum_of_2_powers: "(\<Sum>i=0..<n. 2^i) = 2^n - (1::nat)"
  by (induct n) auto

lemma sum_of_3_powers: "2 * (\<Sum>i=0..<n. 3^i) = 3^n - (1::nat)"
  by (induct n) auto

lemma sum_of_powers: "0 < k \<Longrightarrow> (k - 1) * (\<Sum>i=0..<n. k^i) = k^n - 1"
  for k :: nat
  by (induct n) auto

end
