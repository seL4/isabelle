(*  Title:      HOL/Quadratic_Reciprocity/EvenOdd.thy
    ID:         $Id$
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {*Parity: Even and Odd Integers*}

theory EvenOdd = Int2:;

text{*Note.  This theory is being revised.  See the web page
\url{http://www.andrew.cmu.edu/~avigad/isabelle}.*}

constdefs
  zOdd    :: "int set"
  "zOdd == {x. \<exists>k. x = 2*k + 1}"
  zEven   :: "int set"
  "zEven == {x. \<exists>k. x = 2 * k}"

(***********************************************************)
(*                                                         *)
(* Some useful properties about even and odd               *)
(*                                                         *)
(***********************************************************)

lemma one_not_even: "~(1 \<in> zEven)";
  apply (simp add: zEven_def)
  apply (rule allI, case_tac "k \<le> 0", auto)
done

lemma even_odd_conj: "~(x \<in> zOdd & x \<in> zEven)";
  apply (auto simp add: zOdd_def zEven_def)
  proof -;
    fix a b;
    assume "2 * (a::int) = 2 * (b::int) + 1"; 
    then have "2 * (a::int) - 2 * (b :: int) = 1";
       by arith
    then have "2 * (a - b) = 1";
       by (auto simp add: zdiff_zmult_distrib)
    moreover have "(2 * (a - b)):zEven";
       by (auto simp only: zEven_def)
    ultimately show "False";
       by (auto simp add: one_not_even)
  qed;

lemma even_odd_disj: "(x \<in> zOdd | x \<in> zEven)";
  by (simp add: zOdd_def zEven_def, presburger)

lemma not_odd_impl_even: "~(x \<in> zOdd) ==> x \<in> zEven";
  by (insert even_odd_disj, auto)

lemma odd_mult_odd_prop: "(x*y):zOdd ==> x \<in> zOdd";
  apply (case_tac "x \<in> zOdd", auto)
  apply (drule not_odd_impl_even)
  apply (auto simp add: zEven_def zOdd_def)
  proof -;
    fix a b; 
    assume "2 * a * y = 2 * b + 1";
    then have "2 * a * y - 2 * b = 1";
      by arith
    then have "2 * (a * y - b) = 1";
      by (auto simp add: zdiff_zmult_distrib)
    moreover have "(2 * (a * y - b)):zEven";
       by (auto simp only: zEven_def)
    ultimately show "False";
       by (auto simp add: one_not_even)
  qed;

lemma odd_minus_one_even: "x \<in> zOdd ==> (x - 1):zEven";
  by (auto simp add: zOdd_def zEven_def)

lemma even_div_2_prop1: "x \<in> zEven ==> (x mod 2) = 0";
  by (auto simp add: zEven_def)

lemma even_div_2_prop2: "x \<in> zEven ==> (2 * (x div 2)) = x";
  by (auto simp add: zEven_def)

lemma even_plus_even: "[| x \<in> zEven; y \<in> zEven |] ==> x + y \<in> zEven";
  apply (auto simp add: zEven_def)
  by (auto simp only: zadd_zmult_distrib2 [THEN sym])

lemma even_times_either: "x \<in> zEven ==> x * y \<in> zEven";
  by (auto simp add: zEven_def)

lemma even_minus_even: "[| x \<in> zEven; y \<in> zEven |] ==> x - y \<in> zEven";
  apply (auto simp add: zEven_def)
  by (auto simp only: zdiff_zmult_distrib2 [THEN sym])

lemma odd_minus_odd: "[| x \<in> zOdd; y \<in> zOdd |] ==> x - y \<in> zEven";
  apply (auto simp add: zOdd_def zEven_def)
  by (auto simp only: zdiff_zmult_distrib2 [THEN sym])

lemma even_minus_odd: "[| x \<in> zEven; y \<in> zOdd |] ==> x - y \<in> zOdd";
  apply (auto simp add: zOdd_def zEven_def)
  apply (rule_tac x = "k - ka - 1" in exI)
  by auto

lemma odd_minus_even: "[| x \<in> zOdd; y \<in> zEven |] ==> x - y \<in> zOdd";
  apply (auto simp add: zOdd_def zEven_def)
  by (auto simp only: zdiff_zmult_distrib2 [THEN sym])

lemma odd_times_odd: "[| x \<in> zOdd;  y \<in> zOdd |] ==> x * y \<in> zOdd";
  apply (auto simp add: zOdd_def zadd_zmult_distrib zadd_zmult_distrib2)
  apply (rule_tac x = "2 * ka * k + ka + k" in exI)
  by (auto simp add: zadd_zmult_distrib)

lemma odd_iff_not_even: "(x \<in> zOdd) = (~ (x \<in> zEven))";
  by (insert even_odd_conj even_odd_disj, auto)

lemma even_product: "x * y \<in> zEven ==> x \<in> zEven | y \<in> zEven"; 
  by (insert odd_iff_not_even odd_times_odd, auto)

lemma even_diff: "x - y \<in> zEven = ((x \<in> zEven) = (y \<in> zEven))";
  apply (auto simp add: odd_iff_not_even even_minus_even odd_minus_odd
     even_minus_odd odd_minus_even)
  proof -;
    assume "x - y \<in> zEven" and "x \<in> zEven";
    show "y \<in> zEven";
    proof (rule classical);
      assume "~(y \<in> zEven)"; 
      then have "y \<in> zOdd" 
        by (auto simp add: odd_iff_not_even)
      with prems have "x - y \<in> zOdd";
        by (simp add: even_minus_odd)
      with prems have "False"; 
        by (auto simp add: odd_iff_not_even)
      thus ?thesis;
        by auto
    qed;
    next assume "x - y \<in> zEven" and "y \<in> zEven"; 
    show "x \<in> zEven";
    proof (rule classical);
      assume "~(x \<in> zEven)"; 
      then have "x \<in> zOdd" 
        by (auto simp add: odd_iff_not_even)
      with prems have "x - y \<in> zOdd";
        by (simp add: odd_minus_even)
      with prems have "False"; 
        by (auto simp add: odd_iff_not_even)
      thus ?thesis;
        by auto
    qed;
  qed;

lemma neg_one_even_power: "[| x \<in> zEven; 0 \<le> x |] ==> (-1::int)^(nat x) = 1";
proof -;
  assume "x \<in> zEven" and "0 \<le> x";
  then have "\<exists>k. x = 2 * k";
    by (auto simp only: zEven_def)
  then show ?thesis;
    proof;
      fix a;
      assume "x = 2 * a";
      from prems have a: "0 \<le> a";
        by arith
      from prems have "nat x = nat(2 * a)";
        by auto
      also from a have "nat (2 * a) = 2 * nat a";
        by (auto simp add: nat_mult_distrib)
      finally have "(-1::int)^nat x = (-1)^(2 * nat a)";
        by auto
      also have "... = ((-1::int)^2)^ (nat a)";
        by (auto simp add: zpower_zpower [THEN sym])
      also have "(-1::int)^2 = 1";
        by auto
      finally; show ?thesis;
        by auto
    qed;
qed;

lemma neg_one_odd_power: "[| x \<in> zOdd; 0 \<le> x |] ==> (-1::int)^(nat x) = -1";
proof -;
  assume "x \<in> zOdd" and "0 \<le> x";
  then have "\<exists>k. x = 2 * k + 1";
    by (auto simp only: zOdd_def)
  then show ?thesis;
    proof;
      fix a;
      assume "x = 2 * a + 1";
      from prems have a: "0 \<le> a";
        by arith
      from prems have "nat x = nat(2 * a + 1)";
        by auto
      also from a have "nat (2 * a + 1) = 2 * nat a + 1";
        by (auto simp add: nat_mult_distrib nat_add_distrib)
      finally have "(-1::int)^nat x = (-1)^(2 * nat a + 1)";
        by auto
      also have "... = ((-1::int)^2)^ (nat a) * (-1)^1";
        by (auto simp add: zpower_zpower [THEN sym] zpower_zadd_distrib)
      also have "(-1::int)^2 = 1";
        by auto
      finally; show ?thesis;
        by auto
    qed;
qed;

lemma neg_one_power_parity: "[| 0 \<le> x; 0 \<le> y; (x \<in> zEven) = (y \<in> zEven) |] ==> 
  (-1::int)^(nat x) = (-1::int)^(nat y)";
  apply (insert even_odd_disj [of x])
  apply (insert even_odd_disj [of y])
  by (auto simp add: neg_one_even_power neg_one_odd_power)

lemma one_not_neg_one_mod_m: "2 < m ==> ~([1 = -1] (mod m))";
  by (auto simp add: zcong_def zdvd_not_zless)

lemma even_div_2_l: "[| y \<in> zEven; x < y |] ==> x div 2 < y div 2";
  apply (auto simp only: zEven_def)
  proof -;
    fix k assume "x < 2 * k";
    then have "x div 2 < k" by (auto simp add: div_prop1)
    also have "k = (2 * k) div 2"; by auto
    finally show "x div 2 < 2 * k div 2" by auto
  qed;

lemma even_sum_div_2: "[| x \<in> zEven; y \<in> zEven |] ==> (x + y) div 2 = x div 2 + y div 2";
  by (auto simp add: zEven_def, auto simp add: zdiv_zadd1_eq)

lemma even_prod_div_2: "[| x \<in> zEven |] ==> (x * y) div 2 = (x div 2) * y";
  by (auto simp add: zEven_def)

(* An odd prime is greater than 2 *)

lemma zprime_zOdd_eq_grt_2: "p \<in> zprime ==> (p \<in> zOdd) = (2 < p)";
  apply (auto simp add: zOdd_def zprime_def)
  apply (drule_tac x = 2 in allE)
  apply (insert odd_iff_not_even [of p])  
by (auto simp add: zOdd_def zEven_def)

(* Powers of -1 and parity *)

lemma neg_one_special: "finite A ==> 
    ((-1 :: int) ^ card A) * (-1 ^ card A) = 1";
  by (induct set: Finites, auto)

lemma neg_one_power: "(-1::int)^n = 1 | (-1::int)^n = -1";
  apply (induct_tac n)
  by auto

lemma neg_one_power_eq_mod_m: "[| 2 < m; [(-1::int)^j = (-1::int)^k] (mod m) |]
  ==> ((-1::int)^j = (-1::int)^k)";
  apply (insert neg_one_power [of j])
  apply (insert neg_one_power [of k])
  by (auto simp add: one_not_neg_one_mod_m zcong_sym)

end;
