(*  Title:      HOL/Old_Number_Theory/EvenOdd.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {*Parity: Even and Odd Integers*}

theory EvenOdd
imports Int2
begin

definition zOdd :: "int set"
  where "zOdd = {x. \<exists>k. x = 2 * k + 1}"

definition zEven :: "int set"
  where "zEven = {x. \<exists>k. x = 2 * k}"

subsection {* Some useful properties about even and odd *}

lemma zOddI [intro?]: "x = 2 * k + 1 \<Longrightarrow> x \<in> zOdd"
  and zOddE [elim?]: "x \<in> zOdd \<Longrightarrow> (!!k. x = 2 * k + 1 \<Longrightarrow> C) \<Longrightarrow> C"
  by (auto simp add: zOdd_def)

lemma zEvenI [intro?]: "x = 2 * k \<Longrightarrow> x \<in> zEven"
  and zEvenE [elim?]: "x \<in> zEven \<Longrightarrow> (!!k. x = 2 * k \<Longrightarrow> C) \<Longrightarrow> C"
  by (auto simp add: zEven_def)

lemma one_not_even: "~(1 \<in> zEven)"
proof
  assume "1 \<in> zEven"
  then obtain k :: int where "1 = 2 * k" ..
  then show False by arith
qed

lemma even_odd_conj: "~(x \<in> zOdd & x \<in> zEven)"
proof -
  {
    fix a b
    assume "2 * (a::int) = 2 * (b::int) + 1"
    then have "2 * (a::int) - 2 * (b :: int) = 1"
      by arith
    then have "2 * (a - b) = 1"
      by (auto simp add: left_diff_distrib)
    moreover have "(2 * (a - b)):zEven"
      by (auto simp only: zEven_def)
    ultimately have False
      by (auto simp add: one_not_even)
  }
  then show ?thesis
    by (auto simp add: zOdd_def zEven_def)
qed

lemma even_odd_disj: "(x \<in> zOdd | x \<in> zEven)"
  by (simp add: zOdd_def zEven_def) arith

lemma not_odd_impl_even: "~(x \<in> zOdd) ==> x \<in> zEven"
  using even_odd_disj by auto

lemma odd_mult_odd_prop: "(x*y):zOdd ==> x \<in> zOdd"
proof (rule classical)
  assume "\<not> ?thesis"
  then have "x \<in> zEven" by (rule not_odd_impl_even)
  then obtain a where a: "x = 2 * a" ..
  assume "x * y : zOdd"
  then obtain b where "x * y = 2 * b + 1" ..
  with a have "2 * a * y = 2 * b + 1" by simp
  then have "2 * a * y - 2 * b = 1"
    by arith
  then have "2 * (a * y - b) = 1"
    by (auto simp add: left_diff_distrib)
  moreover have "(2 * (a * y - b)):zEven"
    by (auto simp only: zEven_def)
  ultimately have False
    by (auto simp add: one_not_even)
  then show ?thesis ..
qed

lemma odd_minus_one_even: "x \<in> zOdd ==> (x - 1):zEven"
  by (auto simp add: zOdd_def zEven_def)

lemma even_div_2_prop1: "x \<in> zEven ==> (x mod 2) = 0"
  by (auto simp add: zEven_def)

lemma even_div_2_prop2: "x \<in> zEven ==> (2 * (x div 2)) = x"
  by (auto simp add: zEven_def)

lemma even_plus_even: "[| x \<in> zEven; y \<in> zEven |] ==> x + y \<in> zEven"
  apply (auto simp add: zEven_def)
  apply (auto simp only: distrib_left [symmetric])
  done

lemma even_times_either: "x \<in> zEven ==> x * y \<in> zEven"
  by (auto simp add: zEven_def)

lemma even_minus_even: "[| x \<in> zEven; y \<in> zEven |] ==> x - y \<in> zEven"
  apply (auto simp add: zEven_def)
  apply (auto simp only: right_diff_distrib [symmetric])
  done

lemma odd_minus_odd: "[| x \<in> zOdd; y \<in> zOdd |] ==> x - y \<in> zEven"
  apply (auto simp add: zOdd_def zEven_def)
  apply (auto simp only: right_diff_distrib [symmetric])
  done

lemma even_minus_odd: "[| x \<in> zEven; y \<in> zOdd |] ==> x - y \<in> zOdd"
  apply (auto simp add: zOdd_def zEven_def)
  apply (rule_tac x = "k - ka - 1" in exI)
  apply auto
  done

lemma odd_minus_even: "[| x \<in> zOdd; y \<in> zEven |] ==> x - y \<in> zOdd"
  apply (auto simp add: zOdd_def zEven_def)
  apply (auto simp only: right_diff_distrib [symmetric])
  done

lemma odd_times_odd: "[| x \<in> zOdd;  y \<in> zOdd |] ==> x * y \<in> zOdd"
  apply (auto simp add: zOdd_def distrib_right distrib_left)
  apply (rule_tac x = "2 * ka * k + ka + k" in exI)
  apply (auto simp add: distrib_right)
  done

lemma odd_iff_not_even: "(x \<in> zOdd) = (~ (x \<in> zEven))"
  using even_odd_conj even_odd_disj by auto

lemma even_product: "x * y \<in> zEven ==> x \<in> zEven | y \<in> zEven"
  using odd_iff_not_even odd_times_odd by auto

lemma even_diff: "x - y \<in> zEven = ((x \<in> zEven) = (y \<in> zEven))"
proof
  assume xy: "x - y \<in> zEven"
  {
    assume x: "x \<in> zEven"
    have "y \<in> zEven"
    proof (rule classical)
      assume "\<not> ?thesis"
      then have "y \<in> zOdd"
        by (simp add: odd_iff_not_even)
      with x have "x - y \<in> zOdd"
        by (simp add: even_minus_odd)
      with xy have False
        by (auto simp add: odd_iff_not_even)
      then show ?thesis ..
    qed
  } moreover {
    assume y: "y \<in> zEven"
    have "x \<in> zEven"
    proof (rule classical)
      assume "\<not> ?thesis"
      then have "x \<in> zOdd"
        by (auto simp add: odd_iff_not_even)
      with y have "x - y \<in> zOdd"
        by (simp add: odd_minus_even)
      with xy have False
        by (auto simp add: odd_iff_not_even)
      then show ?thesis ..
    qed
  }
  ultimately show "(x \<in> zEven) = (y \<in> zEven)"
    by (auto simp add: odd_iff_not_even even_minus_even odd_minus_odd
      even_minus_odd odd_minus_even)
next
  assume "(x \<in> zEven) = (y \<in> zEven)"
  then show "x - y \<in> zEven"
    by (auto simp add: odd_iff_not_even even_minus_even odd_minus_odd
      even_minus_odd odd_minus_even)
qed

lemma neg_one_even_power: "[| x \<in> zEven; 0 \<le> x |] ==> (-1::int)^(nat x) = 1"
proof -
  assume "x \<in> zEven" and "0 \<le> x"
  from `x \<in> zEven` obtain a where "x = 2 * a" ..
  with `0 \<le> x` have "0 \<le> a" by simp
  from `0 \<le> x` and `x = 2 * a` have "nat x = nat (2 * a)"
    by simp
  also from `x = 2 * a` have "nat (2 * a) = 2 * nat a"
    by (simp add: nat_mult_distrib)
  finally have "(-1::int)^nat x = (-1)^(2 * nat a)"
    by simp
  also have "... = ((-1::int)^2)^ (nat a)"
    by (simp add: zpower_zpower [symmetric])
  also have "(-1::int)^2 = 1"
    by simp
  finally show ?thesis
    by simp
qed

lemma neg_one_odd_power: "[| x \<in> zOdd; 0 \<le> x |] ==> (-1::int)^(nat x) = -1"
proof -
  assume "x \<in> zOdd" and "0 \<le> x"
  from `x \<in> zOdd` obtain a where "x = 2 * a + 1" ..
  with `0 \<le> x` have a: "0 \<le> a" by simp
  with `0 \<le> x` and `x = 2 * a + 1` have "nat x = nat (2 * a + 1)"
    by simp
  also from a have "nat (2 * a + 1) = 2 * nat a + 1"
    by (auto simp add: nat_mult_distrib nat_add_distrib)
  finally have "(-1::int)^nat x = (-1)^(2 * nat a + 1)"
    by simp
  also have "... = ((-1::int)^2)^ (nat a) * (-1)^1"
    by (auto simp add: power_mult power_add)
  also have "(-1::int)^2 = 1"
    by simp
  finally show ?thesis
    by simp
qed

lemma neg_one_power_parity: "[| 0 \<le> x; 0 \<le> y; (x \<in> zEven) = (y \<in> zEven) |] ==>
    (-1::int)^(nat x) = (-1::int)^(nat y)"
  using even_odd_disj [of x] even_odd_disj [of y]
  by (auto simp add: neg_one_even_power neg_one_odd_power)


lemma one_not_neg_one_mod_m: "2 < m ==> ~([1 = -1] (mod m))"
  by (auto simp add: zcong_def zdvd_not_zless)

lemma even_div_2_l: "[| y \<in> zEven; x < y |] ==> x div 2 < y div 2"
proof -
  assume "y \<in> zEven" and "x < y"
  from `y \<in> zEven` obtain k where k: "y = 2 * k" ..
  with `x < y` have "x < 2 * k" by simp
  then have "x div 2 < k" by (auto simp add: div_prop1)
  also have "k = (2 * k) div 2" by simp
  finally have "x div 2 < 2 * k div 2" by simp
  with k show ?thesis by simp
qed

lemma even_sum_div_2: "[| x \<in> zEven; y \<in> zEven |] ==> (x + y) div 2 = x div 2 + y div 2"
  by (auto simp add: zEven_def)

lemma even_prod_div_2: "[| x \<in> zEven |] ==> (x * y) div 2 = (x div 2) * y"
  by (auto simp add: zEven_def)

(* An odd prime is greater than 2 *)

lemma zprime_zOdd_eq_grt_2: "zprime p ==> (p \<in> zOdd) = (2 < p)"
  apply (auto simp add: zOdd_def zprime_def)
  apply (drule_tac x = 2 in allE)
  using odd_iff_not_even [of p]
  apply (auto simp add: zOdd_def zEven_def)
  done

(* Powers of -1 and parity *)

lemma neg_one_special: "finite A ==>
    ((-1 :: int) ^ card A) * (-1 ^ card A) = 1"
  by (induct set: finite) auto

lemma neg_one_power: "(-1::int)^n = 1 | (-1::int)^n = -1"
  by (induct n) auto

lemma neg_one_power_eq_mod_m: "[| 2 < m; [(-1::int)^j = (-1::int)^k] (mod m) |]
    ==> ((-1::int)^j = (-1::int)^k)"
  using neg_one_power [of j] and ListMem.insert neg_one_power [of k]
  by (auto simp add: one_not_neg_one_mod_m zcong_sym)

end
