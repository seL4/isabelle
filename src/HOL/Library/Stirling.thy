(* Authors: Amine Chaieb & Florian Haftmann, TU Muenchen
            with contributions by Lukas Bulwahn and Manuel Eberl*)

section {* Stirling numbers of first and second kind *}

theory Stirling
imports Binomial
begin

subsection {* Stirling numbers of the second kind *}

fun Stirling :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "Stirling 0 0 = 1"
| "Stirling 0 (Suc k) = 0"
| "Stirling (Suc n) 0 = 0"
| "Stirling (Suc n) (Suc k) = Suc k * Stirling n (Suc k) + Stirling n k"

lemma Stirling_1 [simp]:
  "Stirling (Suc n) (Suc 0) = 1"
  by (induct n) simp_all

lemma Stirling_less [simp]:
  "n < k \<Longrightarrow> Stirling n k = 0"
  by (induct n k rule: Stirling.induct) simp_all

lemma Stirling_same [simp]:
  "Stirling n n = 1"
  by (induct n) simp_all

lemma Stirling_2_2:
  "Stirling (Suc (Suc n)) (Suc (Suc 0)) = 2 ^ Suc n - 1"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "Stirling (Suc (Suc (Suc n))) (Suc (Suc 0)) =
    2 * Stirling (Suc (Suc n)) (Suc (Suc 0)) + Stirling (Suc (Suc n)) (Suc 0)" by simp
  also have "\<dots> = 2 * (2 ^ Suc n - 1) + 1"
    by (simp only: Suc Stirling_1)
  also have "\<dots> = 2 ^ Suc (Suc n) - 1"
  proof -
    have "(2::nat) ^ Suc n - 1 > 0" by (induct n) simp_all
    then have "2 * ((2::nat) ^ Suc n - 1) > 0" by simp
    then have "2 \<le> 2 * ((2::nat) ^ Suc n)" by simp
    with add_diff_assoc2 [of 2 "2 * 2 ^ Suc n" 1]
      have "2 * 2 ^ Suc n - 2 + (1::nat) = 2 * 2 ^ Suc n + 1 - 2" .
    then show ?thesis by (simp add: nat_distrib)
  qed
  finally show ?case by simp
qed

lemma Stirling_2:
  "Stirling (Suc n) (Suc (Suc 0)) = 2 ^ n - 1"
  using Stirling_2_2 by (cases n) simp_all

subsection {* Stirling numbers of the first kind *}

fun stirling :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "stirling 0 0 = 1"
| "stirling 0 (Suc k) = 0"
| "stirling (Suc n) 0 = 0"
| "stirling (Suc n) (Suc k) = n * stirling n (Suc k) + stirling n k"

lemma stirling_0 [simp]: "n > 0 \<Longrightarrow> stirling n 0 = 0"
  by (cases n) simp_all

lemma stirling_less [simp]:
  "n < k \<Longrightarrow> stirling n k = 0"
  by (induct n k rule: stirling.induct) simp_all

lemma stirling_same [simp]:
  "stirling n n = 1"
  by (induct n) simp_all

lemma stirling_Suc_n_1:
  "stirling (Suc n) (Suc 0) = fact n"
  by (induct n) auto

lemma stirling_Suc_n_n:
  shows "stirling (Suc n) n = Suc n choose 2"
by (induct n) (auto simp add: numerals(2))

lemma stirling_Suc_n_2:
  assumes "n \<ge> Suc 0"
  shows "stirling (Suc n) 2 = (\<Sum>k=1..n. fact n div k)"
using assms
proof (induct n)
  case 0 from this show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0 from this show ?thesis by (simp add: numerals(2))
  next
    case Suc
    from this have geq1: "Suc 0 \<le> n" by simp
    have "stirling (Suc (Suc n)) 2 = Suc n * stirling (Suc n) 2 + stirling (Suc n) (Suc 0)"
      by (simp only: stirling.simps(4)[of "Suc n"] numerals(2))
    also have "... = Suc n * (\<Sum>k=1..n. fact n div k) + fact n"
      using Suc.hyps[OF geq1]
      by (simp only: stirling_Suc_n_1 of_nat_fact of_nat_add of_nat_mult)
    also have "... = Suc n * (\<Sum>k=1..n. fact n div k) + Suc n * fact n div Suc n"
      by (metis nat.distinct(1) nonzero_mult_divide_cancel_left)
    also have "... = (\<Sum>k=1..n. fact (Suc n) div k) + fact (Suc n) div Suc n"
      by (simp add: setsum_right_distrib div_mult_swap dvd_fact)
    also have "... = (\<Sum>k=1..Suc n. fact (Suc n) div k)" by simp
    finally show ?thesis .
  qed
qed

lemma of_nat_stirling_Suc_n_2:
  assumes "n \<ge> Suc 0"
  shows "(of_nat (stirling (Suc n) 2)::'a::field_char_0) = fact n * (\<Sum>k=1..n. (1 / of_nat k))"
using assms
proof (induct n)
  case 0 from this show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0 from this show ?thesis by (auto simp add: numerals(2))
  next
    case Suc
    from this have geq1: "Suc 0 \<le> n" by simp
    have "(of_nat (stirling (Suc (Suc n)) 2)::'a) =
      of_nat (Suc n * stirling (Suc n) 2 + stirling (Suc n) (Suc 0))"
      by (simp only: stirling.simps(4)[of "Suc n"] numerals(2))
    also have "... = of_nat (Suc n) * (fact n * (\<Sum>k = 1..n. 1 / of_nat k)) + fact n"
      using Suc.hyps[OF geq1]
      by (simp only: stirling_Suc_n_1 of_nat_fact of_nat_add of_nat_mult)
    also have "... = fact (Suc n) * (\<Sum>k = 1..n. 1 / of_nat k) + fact (Suc n) * (1 / of_nat (Suc n))"
      using of_nat_neq_0 by auto
    also have "... = fact (Suc n) * (\<Sum>k = 1..Suc n. 1 / of_nat k)"
      by (simp add: distrib_left)
    finally show ?thesis .
  qed
qed

lemma setsum_stirling:
  "(\<Sum>k\<le>n. stirling n k) = fact n"
proof (induct n)
  case 0
  from this show ?case by simp
next
  case (Suc n)
  have "(\<Sum>k\<le>Suc n. stirling (Suc n) k) = stirling (Suc n) 0 + (\<Sum>k\<le>n. stirling (Suc n) (Suc k))"
    by (simp only: setsum_atMost_Suc_shift)
  also have "\<dots> = (\<Sum>k\<le>n. stirling (Suc n) (Suc k))" by simp
  also have "\<dots> = (\<Sum>k\<le>n. n * stirling n (Suc k) + stirling n k)" by simp
  also have "\<dots> = n * (\<Sum>k\<le>n. stirling n (Suc k)) + (\<Sum>k\<le>n. stirling n k)"
    by (simp add: setsum.distrib setsum_right_distrib)
  also have "\<dots> = n * fact n + fact n"
  proof -
    have "n * (\<Sum>k\<le>n. stirling n (Suc k)) = n * ((\<Sum>k\<le>Suc n. stirling n k) - stirling n 0)"
      by (metis add_diff_cancel_left' setsum_atMost_Suc_shift)
    also have "\<dots> = n * (\<Sum>k\<le>n. stirling n k)" by (cases n) simp+
    also have "\<dots> = n * fact n" using Suc.hyps by simp
    finally have "n * (\<Sum>k\<le>n. stirling n (Suc k)) = n * fact n" .
    moreover have "(\<Sum>k\<le>n. stirling n k) = fact n" using Suc.hyps .
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = fact (Suc n)" by simp
  finally show ?case .
qed

lemma stirling_pochhammer:
  "(\<Sum>k\<le>n. of_nat (stirling n k) * x ^ k) = (pochhammer x n :: 'a :: comm_semiring_1)"
proof (induction n)
  case (Suc n)
  have "of_nat (n * stirling n 0) = (0 :: 'a)" by (cases n) simp_all
  hence "(\<Sum>k\<le>Suc n. of_nat (stirling (Suc n) k) * x ^ k) =
            (of_nat (n * stirling n 0) * x ^ 0 +
            (\<Sum>i\<le>n. of_nat (n * stirling n (Suc i)) * (x ^ Suc i))) +
            (\<Sum>i\<le>n. of_nat (stirling n i) * (x ^ Suc i))"
    by (subst setsum_atMost_Suc_shift) (simp add: setsum.distrib ring_distribs)
  also have "\<dots> = pochhammer x (Suc n)"
    by (subst setsum_atMost_Suc_shift [symmetric])
       (simp add: algebra_simps setsum.distrib setsum_right_distrib pochhammer_Suc Suc [symmetric])
  finally show ?case .
qed simp_all


text \<open>A row of the Stirling number triangle\<close>

definition stirling_row :: "nat \<Rightarrow> nat list" where
  "stirling_row n = [stirling n k. k \<leftarrow> [0..<Suc n]]"

lemma nth_stirling_row: "k \<le> n \<Longrightarrow> stirling_row n ! k = stirling n k"
  by (simp add: stirling_row_def del: upt_Suc)

lemma length_stirling_row [simp]: "length (stirling_row n) = Suc n"
  by (simp add: stirling_row_def)

lemma stirling_row_nonempty [simp]: "stirling_row n \<noteq> []"
  using length_stirling_row[of n] by (auto simp del: length_stirling_row)

(* TODO Move *)
lemma list_ext:
  assumes "length xs = length ys"
  assumes "\<And>i. i < length xs \<Longrightarrow> xs ! i = ys ! i"
  shows   "xs = ys"
using assms
proof (induction rule: list_induct2)
  case (Cons x xs y ys)
  from Cons.prems[of 0] have "x = y" by simp
  moreover from Cons.prems[of "Suc i" for i] have "xs = ys" by (intro Cons.IH) simp
  ultimately show ?case by simp
qed simp_all


subsubsection \<open>Efficient code\<close>

text \<open>
  Naively using the defining equations of the Stirling numbers of the first kind to
  compute them leads to exponential run time due to repeated computations.
  We can use memoisation to compute them row by row without repeating computations, at
  the cost of computing a few unneeded values.

  As a bonus, this is very efficient for applications where an entire row of
  Stirling numbers is needed..
\<close>

definition zip_with_prev :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "zip_with_prev f x xs = map (\<lambda>(x,y). f x y) (zip (x # xs) xs)"

lemma zip_with_prev_altdef:
  "zip_with_prev f x xs =
     (if xs = [] then [] else f x (hd xs) # [f (xs!i) (xs!(i+1)). i \<leftarrow> [0..<length xs - 1]])"
proof (cases xs)
  case (Cons y ys)
  hence "zip_with_prev f x xs = f x (hd xs) # zip_with_prev f y ys"
    by (simp add: zip_with_prev_def)
  also have "zip_with_prev f y ys = map (\<lambda>i. f (xs ! i) (xs ! (i + 1))) [0..<length xs - 1]"
    unfolding Cons
    by (induction ys arbitrary: y)
       (simp_all add: zip_with_prev_def upt_conv_Cons map_Suc_upt [symmetric] del: upt_Suc)
  finally show ?thesis using Cons by simp
qed (simp add: zip_with_prev_def)


primrec stirling_row_aux where
  "stirling_row_aux n y [] = [1]"
| "stirling_row_aux n y (x#xs) = (y + n * x) # stirling_row_aux n x xs"

lemma stirling_row_aux_correct:
  "stirling_row_aux n y xs = zip_with_prev (\<lambda>a b. a + n * b) y xs @ [1]"
  by (induction xs arbitrary: y) (simp_all add: zip_with_prev_def)

lemma stirling_row_code [code]:
  "stirling_row 0 = [1]"
  "stirling_row (Suc n) = stirling_row_aux n 0 (stirling_row n)"
proof -
  have "stirling_row (Suc n) =
          0 # [stirling_row n ! i + stirling_row n ! (i+1) * n. i \<leftarrow> [0..<n]] @ [1]"
  proof (rule list_ext, goal_cases length nth)
    case (nth i)
    from nth have "i \<le> Suc n" by simp
    then consider "i = 0" | j where "i > 0" "i \<le> n" | "i = Suc n" by linarith
    thus ?case
    proof cases
      assume i: "i > 0" "i \<le> n"
      from this show ?thesis by (cases i) (simp_all add: nth_append nth_stirling_row)
    qed (simp_all add: nth_stirling_row nth_append)
  qed simp
  also have "0 # [stirling_row n ! i + stirling_row n ! (i+1) * n. i \<leftarrow> [0..<n]] @ [1] =
               zip_with_prev (\<lambda>a b. a + n * b) 0 (stirling_row n) @ [1]"
    by (cases n) (auto simp add: zip_with_prev_altdef stirling_row_def hd_map simp del: upt_Suc)
  also have "\<dots> = stirling_row_aux n 0 (stirling_row n)"
    by (simp add: stirling_row_aux_correct)
  finally show "stirling_row (Suc n) = stirling_row_aux n 0 (stirling_row n)" .
qed (simp add: stirling_row_def)

lemma stirling_code [code]:
  "stirling n k = (if k = 0 then if n = 0 then 1 else 0
                   else if k > n then 0 else if k = n then 1
                   else stirling_row n ! k)"
  by (simp add: nth_stirling_row)

end
