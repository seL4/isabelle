(*  Title:      HOL/Quotient_Examples/Quotient_Int.thy
    Author:     Cezary Kaliszyk
    Author:     Christian Urban

Integers based on Quotients, based on an older version by Larry
Paulson.
*)

theory Quotient_Int
imports "HOL-Library.Quotient_Product"
begin

fun
  intrel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" (infix \<open>\<approx>\<close> 50)
where
  "intrel (x, y) (u, v) = (x + v = u + y)"

quotient_type int = "nat \<times> nat" / intrel
  by (auto simp add: equivp_def fun_eq_iff)

instantiation int :: "{zero, one, plus, uminus, minus, times, ord, abs, sgn}"
begin

quotient_definition
  "0 :: int" is "(0::nat, 0::nat)" done

quotient_definition
  "1 :: int" is "(1::nat, 0::nat)" done

fun
  plus_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "plus_int_raw (x, y) (u, v) = (x + u, y + v)"

quotient_definition
  "(+) :: (int \<Rightarrow> int \<Rightarrow> int)" is "plus_int_raw" by auto

fun
  uminus_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "uminus_int_raw (x, y) = (y, x)"

quotient_definition
  "(uminus :: (int \<Rightarrow> int))" is "uminus_int_raw" by auto

definition
  minus_int_def:  "z - w = z + (-w::int)"

fun
  times_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "times_int_raw (x, y) (u, v) = (x*u + y*v, x*v + y*u)"

lemma times_int_raw:
  assumes "x \<approx> z"
  shows "times_int_raw x y \<approx> times_int_raw z y \<and> times_int_raw y x \<approx> times_int_raw y z"
proof (cases x, cases y, cases z)
  fix a a' b b' c c'
  assume \<section>: "x = (a, a')" "y = (b, b')" "z = (c, c')"
  then obtain "a*b + c'*b = c*b + a'*b" "a*b' + c'*b' = c*b' + a'*b'"
    by (metis add_mult_distrib assms intrel.simps)
  then show ?thesis
    by (simp add: \<section> algebra_simps)
qed

quotient_definition
  "((*)) :: (int \<Rightarrow> int \<Rightarrow> int)" is "times_int_raw"
  by (metis Quotient_Int.int.abs_eq_iff times_int_raw)

fun
  le_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool"
where
  "le_int_raw (x, y) (u, v) = (x+v \<le> u+y)"

quotient_definition
  le_int_def: "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool" is "le_int_raw" by auto

definition
  less_int_def: "(z::int) < w = (z \<le> w \<and> z \<noteq> w)"

definition
  zabs_def: "\<bar>i::int\<bar> = (if i < 0 then - i else i)"

definition
  zsgn_def: "sgn (i::int) = (if i = 0 then 0 else if 0 < i then 1 else - 1)"

instance ..

end


text\<open>The integers form a \<open>comm_ring_1\<close>\<close>

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
  "(abs_int (x,y)) + (abs_int (u,v)) = (abs_int (x + u, y + v))"
proof -
  have "abs_int (plus_int_raw (rep_int (abs_int (x, y))) (rep_int (abs_int (u, v)))) 
     = abs_int (plus_int_raw (x, y) (u, v))"
  by (meson Quotient3_abs_rep Quotient3_int int.abs_eq_iff plus_int_raw_rsp_aux)
  then show ?thesis
    by (simp add: Quotient_Int.plus_int_def)
qed

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
  "(inf :: int \<Rightarrow> int \<Rightarrow> int) = min"

definition
  "(sup :: int \<Rightarrow> int \<Rightarrow> int) = max"

instance
  by standard (auto simp add: inf_int_def sup_int_def max_min_distrib2)

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
proof (induction "k")
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case 
    by (cases "k = 0"; simp add: distrib_right add_strict_mono)
qed

lemma zero_le_imp_eq_int_raw:
  assumes "less_int_raw (0, 0) u"
  shows "(\<exists>n > 0. u \<approx> int_of_nat_raw n)"
proof -
  have "\<And>a b::nat. \<lbrakk>b \<le> a; b \<noteq> a\<rbrakk> \<Longrightarrow> \<exists>n>0. a = n + b"
    by (metis add.comm_neutral add.commute gr0I le_iff_add)
  with assms show ?thesis
    by (cases u) (simp add:int_of_nat_raw)
qed

lemma zero_le_imp_eq_int:
  fixes k::int
  shows "0 < k \<Longrightarrow> \<exists>n > 0. k = of_nat n"
  unfolding less_int_def int_of_nat
  by (descending) (rule zero_le_imp_eq_int_raw)

lemma zmult_zless_mono2:
  fixes i j k::int
  assumes "i < j" "0 < k"
  shows "k * i < k * j"
  using assms zmult_zless_mono2_lemma [of i j]
  using Quotient_Int.zero_le_imp_eq_int by blast

text\<open>The integers form an ordered integral domain\<close>

instance int :: linordered_idom
proof
  fix i j k :: int
  show "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
    by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)"
    by (simp only: zabs_def)
  show "sgn (i::int) = (if i=0 then 0 else if 0<i then 1 else - 1)"
    by (simp only: zsgn_def)
qed

lemmas int_distrib =
  distrib_right [of z1 z2 w]
  distrib_left [of w z1 z2]
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
  

text \<open>Magnitide of an Integer, as a Natural Number: \<^term>\<open>nat\<close>\<close>

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
