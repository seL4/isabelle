(*  Title:      HOL/Quotient_Examples/Quotient_Int.thy
    Author:     Cezary Kaliszyk
    Author:     Christian Urban

Integers based on Quotients, based on an older version by Larry
Paulson.
*)

theory Quotient_Int
imports "~~/src/HOL/Library/Quotient_Product" Nat
begin

fun
  intrel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" (infix "\<approx>" 50)
where
  "intrel (x, y) (u, v) = (x + v = u + y)"

quotient_type int = "nat \<times> nat" / intrel
  by (auto simp add: equivp_def fun_eq_iff)

instantiation int :: "{zero, one, plus, uminus, minus, times, ord, abs, sgn}"
begin

quotient_definition
  "0 \<Colon> int" is "(0\<Colon>nat, 0\<Colon>nat)" done

quotient_definition
  "1 \<Colon> int" is "(1\<Colon>nat, 0\<Colon>nat)" done

fun
  plus_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "plus_int_raw (x, y) (u, v) = (x + u, y + v)"

quotient_definition
  "(op +) \<Colon> (int \<Rightarrow> int \<Rightarrow> int)" is "plus_int_raw" by auto

fun
  uminus_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "uminus_int_raw (x, y) = (y, x)"

quotient_definition
  "(uminus \<Colon> (int \<Rightarrow> int))" is "uminus_int_raw" by auto

definition
  minus_int_def:  "z - w = z + (-w\<Colon>int)"

fun
  times_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "times_int_raw (x, y) (u, v) = (x*u + y*v, x*v + y*u)"

lemma times_int_raw_fst:
  assumes a: "x \<approx> z"
  shows "times_int_raw x y \<approx> times_int_raw z y"
  using a
  apply(cases x, cases y, cases z)
  apply(auto simp add: times_int_raw.simps intrel.simps)
  apply(rename_tac u v w x y z)
  apply(subgoal_tac "u*w + z*w = y*w + v*w  &  u*x + z*x = y*x + v*x")
  apply(simp add: mult_ac)
  apply(simp add: add_mult_distrib [symmetric])
done

lemma times_int_raw_snd:
  assumes a: "x \<approx> z"
  shows "times_int_raw y x \<approx> times_int_raw y z"
  using a
  apply(cases x, cases y, cases z)
  apply(auto simp add: times_int_raw.simps intrel.simps)
  apply(rename_tac u v w x y z)
  apply(subgoal_tac "u*w + z*w = y*w + v*w  &  u*x + z*x = y*x + v*x")
  apply(simp add: mult_ac)
  apply(simp add: add_mult_distrib [symmetric])
done

quotient_definition
  "(op *) :: (int \<Rightarrow> int \<Rightarrow> int)" is "times_int_raw"
  apply(rule equivp_transp[OF int_equivp])
  apply(rule times_int_raw_fst)
  apply(assumption)
  apply(rule times_int_raw_snd)
  apply(assumption)
done

fun
  le_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool"
where
  "le_int_raw (x, y) (u, v) = (x+v \<le> u+y)"

quotient_definition
  le_int_def: "(op \<le>) :: int \<Rightarrow> int \<Rightarrow> bool" is "le_int_raw" by auto

definition
  less_int_def: "(z\<Colon>int) < w = (z \<le> w \<and> z \<noteq> w)"

definition
  zabs_def: "\<bar>i\<Colon>int\<bar> = (if i < 0 then - i else i)"

definition
  zsgn_def: "sgn (i\<Colon>int) = (if i = 0 then 0 else if 0 < i then 1 else - 1)"

instance ..

end


text{* The integers form a @{text comm_ring_1}*}

instance int :: comm_ring_1
proof
  fix i j k :: int
  show "(i + j) + k = i + (j + k)"
    by (descending) (auto)
  show "i + j = j + i"
    by (descending) (auto)
  show "0 + i = (i::int)"
    by (descending) (auto)
  show "- i + i = 0"
    by (descending) (auto)
  show "i - j = i + - j"
    by (simp add: minus_int_def)
  show "(i * j) * k = i * (j * k)"
    by (descending) (auto simp add: algebra_simps)
  show "i * j = j * i"
    by (descending) (auto)
  show "1 * i = i"
    by (descending) (auto)
  show "(i + j) * k = i * k + j * k"
    by (descending) (auto simp add: algebra_simps)
  show "0 \<noteq> (1::int)"
    by (descending) (auto)
qed

lemma plus_int_raw_rsp_aux:
  assumes a: "a \<approx> b" "c \<approx> d"
  shows "plus_int_raw a c \<approx> plus_int_raw b d"
  using a
  by (cases a, cases b, cases c, cases d)
     (simp)

lemma add_abs_int:
  "(abs_int (x,y)) + (abs_int (u,v)) =
   (abs_int (x + u, y + v))"
  apply(simp add: plus_int_def id_simps)
  apply(fold plus_int_raw.simps)
  apply(rule Quotient3_rel_abs[OF Quotient3_int])
  apply(rule plus_int_raw_rsp_aux)
  apply(simp_all add: rep_abs_rsp_left[OF Quotient3_int])
  done

definition int_of_nat_raw:
  "int_of_nat_raw m = (m :: nat, 0 :: nat)"

quotient_definition
  "int_of_nat :: nat \<Rightarrow> int" is "int_of_nat_raw" done

lemma int_of_nat:
  shows "of_nat m = int_of_nat m"
  by (induct m)
     (simp_all add: zero_int_def one_int_def int_of_nat_def int_of_nat_raw add_abs_int)

instance int :: linorder
proof
  fix i j k :: int
  show antisym: "i \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> i = j"
    by (descending) (auto)
  show "(i < j) = (i \<le> j \<and> \<not> j \<le> i)"
    by (auto simp add: less_int_def dest: antisym)
  show "i \<le> i"
    by (descending) (auto)
  show "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k"
    by (descending) (auto)
  show "i \<le> j \<or> j \<le> i"
    by (descending) (auto)
qed

instantiation int :: distrib_lattice
begin

definition
  "(inf \<Colon> int \<Rightarrow> int \<Rightarrow> int) = min"

definition
  "(sup \<Colon> int \<Rightarrow> int \<Rightarrow> int) = max"

instance
  by default
     (auto simp add: inf_int_def sup_int_def min_max.sup_inf_distrib1)

end

instance int :: ordered_cancel_ab_semigroup_add
proof
  fix i j k :: int
  show "i \<le> j \<Longrightarrow> k + i \<le> k + j"
    by (descending) (auto)
qed

abbreviation
  "less_int_raw i j \<equiv> le_int_raw i j \<and> \<not>(i \<approx> j)"

lemma zmult_zless_mono2_lemma:
  fixes i j::int
  and   k::nat
  shows "i < j \<Longrightarrow> 0 < k \<Longrightarrow> of_nat k * i < of_nat k * j"
  apply(induct "k")
  apply(simp)
  apply(case_tac "k = 0")
  apply(simp_all add: left_distrib add_strict_mono)
  done

lemma zero_le_imp_eq_int_raw:
  fixes k::"(nat \<times> nat)"
  shows "less_int_raw (0, 0) k \<Longrightarrow> (\<exists>n > 0. k \<approx> int_of_nat_raw n)"
  apply(cases k)
  apply(simp add:int_of_nat_raw)
  apply(auto)
  apply(rule_tac i="b" and j="a" in less_Suc_induct)
  apply(auto)
  done

lemma zero_le_imp_eq_int:
  fixes k::int
  shows "0 < k \<Longrightarrow> \<exists>n > 0. k = of_nat n"
  unfolding less_int_def int_of_nat
  by (descending) (rule zero_le_imp_eq_int_raw)

lemma zmult_zless_mono2:
  fixes i j k::int
  assumes a: "i < j" "0 < k"
  shows "k * i < k * j"
  using a
  by (drule_tac zero_le_imp_eq_int) (auto simp add: zmult_zless_mono2_lemma)

text{*The integers form an ordered integral domain*}

instance int :: linordered_idom
proof
  fix i j k :: int
  show "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
    by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)"
    by (simp only: zabs_def)
  show "sgn (i\<Colon>int) = (if i=0 then 0 else if 0<i then 1 else - 1)"
    by (simp only: zsgn_def)
qed

lemmas int_distrib =
  left_distrib [of z1 z2 w]
  right_distrib [of w z1 z2]
  left_diff_distrib [of z1 z2 w]
  right_diff_distrib [of w z1 z2]
  minus_add_distrib[of z1 z2]
  for z1 z2 w :: int

lemma int_induct2:
  assumes "P 0 0"
  and     "\<And>n m. P n m \<Longrightarrow> P (Suc n) m"
  and     "\<And>n m. P n m \<Longrightarrow> P n (Suc m)"
  shows   "P n m"
using assms
by (induction_schema) (pat_completeness, lexicographic_order)


lemma int_induct:
  fixes j :: int
  assumes a: "P 0"
  and     b: "\<And>i::int. P i \<Longrightarrow> P (i + 1)"
  and     c: "\<And>i::int. P i \<Longrightarrow> P (i - 1)"
  shows      "P j"
using a b c 
unfolding minus_int_def
by (descending) (auto intro: int_induct2)
  

text {* Magnitide of an Integer, as a Natural Number: @{term nat} *}

definition
  "int_to_nat_raw \<equiv> \<lambda>(x, y).x - (y::nat)"

quotient_definition
  "int_to_nat::int \<Rightarrow> nat"
is
  "int_to_nat_raw" 
unfolding int_to_nat_raw_def by auto 

lemma nat_le_eq_zle:
  fixes w z::"int"
  shows "0 < w \<or> 0 \<le> z \<Longrightarrow> (int_to_nat w \<le> int_to_nat z) = (w \<le> z)"
  unfolding less_int_def
  by (descending) (auto simp add: int_to_nat_raw_def)

end
