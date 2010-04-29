(*  Title:      HOL/Quotient_Examples/Quotient_Int.thy
    Author:     Cezary Kaliszyk
    Author:     Christian Urban

Integers based on Quotients, based on an older version by Larry Paulson.
*)
theory Quotient_Int
imports Quotient_Product Nat
begin

fun
  intrel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" (infix "\<approx>" 50)
where
  "intrel (x, y) (u, v) = (x + v = u + y)"

quotient_type int = "nat \<times> nat" / intrel
  by (auto simp add: equivp_def expand_fun_eq)

instantiation int :: "{zero, one, plus, uminus, minus, times, ord, abs, sgn}"
begin

quotient_definition
  "0 \<Colon> int" is "(0\<Colon>nat, 0\<Colon>nat)"

quotient_definition
  "1 \<Colon> int" is "(1\<Colon>nat, 0\<Colon>nat)"

fun
  plus_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "plus_int_raw (x, y) (u, v) = (x + u, y + v)"

quotient_definition
  "(op +) \<Colon> (int \<Rightarrow> int \<Rightarrow> int)" is "plus_int_raw"

fun
  uminus_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "uminus_int_raw (x, y) = (y, x)"

quotient_definition
  "(uminus \<Colon> (int \<Rightarrow> int))" is "uminus_int_raw"

definition
  minus_int_def [code del]:  "z - w = z + (-w\<Colon>int)"

fun
  times_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "times_int_raw (x, y) (u, v) = (x*u + y*v, x*v + y*u)"

quotient_definition
  "(op *) :: (int \<Rightarrow> int \<Rightarrow> int)" is "times_int_raw"

fun
  le_int_raw :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool"
where
  "le_int_raw (x, y) (u, v) = (x+v \<le> u+y)"

quotient_definition
  le_int_def: "(op \<le>) :: int \<Rightarrow> int \<Rightarrow> bool" is "le_int_raw"

definition
  less_int_def [code del]: "(z\<Colon>int) < w = (z \<le> w \<and> z \<noteq> w)"

definition
  zabs_def: "\<bar>i\<Colon>int\<bar> = (if i < 0 then - i else i)"

definition
  zsgn_def: "sgn (i\<Colon>int) = (if i = 0 then 0 else if 0 < i then 1 else - 1)"

instance ..

end

lemma [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op \<approx>) plus_int_raw plus_int_raw"
  and   "(op \<approx> ===> op \<approx>) uminus_int_raw uminus_int_raw"
  and   "(op \<approx> ===> op \<approx> ===> op =) le_int_raw le_int_raw"
  by auto

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

lemma [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op \<approx>) times_int_raw times_int_raw"
  apply(simp only: fun_rel_def)
  apply(rule allI | rule impI)+
  apply(rule equivp_transp[OF int_equivp])
  apply(rule times_int_raw_fst)
  apply(assumption)
  apply(rule times_int_raw_snd)
  apply(assumption)
  done

lemma plus_assoc_raw:
  shows "plus_int_raw (plus_int_raw i j) k \<approx> plus_int_raw i (plus_int_raw j k)"
  by (cases i, cases j, cases k) (simp)

lemma plus_sym_raw:
  shows "plus_int_raw i j \<approx> plus_int_raw j i"
  by (cases i, cases j) (simp)

lemma plus_zero_raw:
  shows "plus_int_raw (0, 0) i \<approx> i"
  by (cases i) (simp)

lemma plus_minus_zero_raw:
  shows "plus_int_raw (uminus_int_raw i) i \<approx> (0, 0)"
  by (cases i) (simp)

lemma times_assoc_raw:
  shows "times_int_raw (times_int_raw i j) k \<approx> times_int_raw i (times_int_raw j k)"
  by (cases i, cases j, cases k)
     (simp add: algebra_simps)

lemma times_sym_raw:
  shows "times_int_raw i j \<approx> times_int_raw j i"
  by (cases i, cases j) (simp add: algebra_simps)

lemma times_one_raw:
  shows "times_int_raw  (1, 0) i \<approx> i"
  by (cases i) (simp)

lemma times_plus_comm_raw:
  shows "times_int_raw (plus_int_raw i j) k \<approx> plus_int_raw (times_int_raw i k) (times_int_raw j k)"
by (cases i, cases j, cases k)
   (simp add: algebra_simps)

lemma one_zero_distinct:
  shows "\<not> (0, 0) \<approx> ((1::nat), (0::nat))"
  by simp

text{* The integers form a @{text comm_ring_1}*}

instance int :: comm_ring_1
proof
  fix i j k :: int
  show "(i + j) + k = i + (j + k)"
    by (lifting plus_assoc_raw)
  show "i + j = j + i"
    by (lifting plus_sym_raw)
  show "0 + i = (i::int)"
    by (lifting plus_zero_raw)
  show "- i + i = 0"
    by (lifting plus_minus_zero_raw)
  show "i - j = i + - j"
    by (simp add: minus_int_def)
  show "(i * j) * k = i * (j * k)"
    by (lifting times_assoc_raw)
  show "i * j = j * i"
    by (lifting times_sym_raw)
  show "1 * i = i"
    by (lifting times_one_raw)
  show "(i + j) * k = i * k + j * k"
    by (lifting times_plus_comm_raw)
  show "0 \<noteq> (1::int)"
    by (lifting one_zero_distinct)
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
  apply(rule Quotient_rel_abs[OF Quotient_int])
  apply(rule plus_int_raw_rsp_aux)
  apply(simp_all add: rep_abs_rsp_left[OF Quotient_int])
  done

definition int_of_nat_raw:
  "int_of_nat_raw m = (m :: nat, 0 :: nat)"

quotient_definition
  "int_of_nat :: nat \<Rightarrow> int" is "int_of_nat_raw"

lemma[quot_respect]:
  shows "(op = ===> op \<approx>) int_of_nat_raw int_of_nat_raw"
  by (simp add: equivp_reflp[OF int_equivp])

lemma int_of_nat:
  shows "of_nat m = int_of_nat m"
  by (induct m)
     (simp_all add: zero_int_def one_int_def int_of_nat_def int_of_nat_raw add_abs_int)

lemma le_antisym_raw:
  shows "le_int_raw i j \<Longrightarrow> le_int_raw j i \<Longrightarrow> i \<approx> j"
  by (cases i, cases j) (simp)

lemma le_refl_raw:
  shows "le_int_raw i i"
  by (cases i) (simp)

lemma le_trans_raw:
  shows "le_int_raw i j \<Longrightarrow> le_int_raw j k \<Longrightarrow> le_int_raw i k"
  by (cases i, cases j, cases k) (simp)

lemma le_cases_raw:
  shows "le_int_raw i j \<or> le_int_raw j i"
  by (cases i, cases j)
     (simp add: linorder_linear)

instance int :: linorder
proof
  fix i j k :: int
  show antisym: "i \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> i = j"
    by (lifting le_antisym_raw)
  show "(i < j) = (i \<le> j \<and> \<not> j \<le> i)"
    by (auto simp add: less_int_def dest: antisym)
  show "i \<le> i"
    by (lifting le_refl_raw)
  show "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k"
    by (lifting le_trans_raw)
  show "i \<le> j \<or> j \<le> i"
    by (lifting le_cases_raw)
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

lemma le_plus_int_raw:
  shows "le_int_raw i j \<Longrightarrow> le_int_raw (plus_int_raw k i) (plus_int_raw k j)"
  by (cases i, cases j, cases k) (simp)

instance int :: ordered_cancel_ab_semigroup_add
proof
  fix i j k :: int
  show "i \<le> j \<Longrightarrow> k + i \<le> k + j"
    by (lifting le_plus_int_raw)
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
  by (lifting zero_le_imp_eq_int_raw)

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
  left_distrib [of "z1::int" "z2" "w", standard]
  right_distrib [of "w::int" "z1" "z2", standard]
  left_diff_distrib [of "z1::int" "z2" "w", standard]
  right_diff_distrib [of "w::int" "z1" "z2", standard]
  minus_add_distrib[of "z1::int" "z2", standard]

lemma int_induct_raw:
  assumes a: "P (0::nat, 0)"
  and     b: "\<And>i. P i \<Longrightarrow> P (plus_int_raw i (1, 0))"
  and     c: "\<And>i. P i \<Longrightarrow> P (plus_int_raw i (uminus_int_raw (1, 0)))"
  shows      "P x"
proof (cases x, clarify)
  fix a b
  show "P (a, b)"
  proof (induct a arbitrary: b rule: Nat.induct)
    case zero
    show "P (0, b)" using assms by (induct b) auto
  next
    case (Suc n)
    then show ?case using assms by auto
  qed
qed

lemma int_induct:
  fixes x :: int
  assumes a: "P 0"
  and     b: "\<And>i. P i \<Longrightarrow> P (i + 1)"
  and     c: "\<And>i. P i \<Longrightarrow> P (i - 1)"
  shows      "P x"
  using a b c unfolding minus_int_def
  by (lifting int_induct_raw)

text {* Magnitide of an Integer, as a Natural Number: @{term nat} *}

definition
  "int_to_nat_raw \<equiv> \<lambda>(x, y).x - (y::nat)"

quotient_definition
  "int_to_nat::int \<Rightarrow> nat"
is
  "int_to_nat_raw"

lemma [quot_respect]:
  shows "(intrel ===> op =) int_to_nat_raw int_to_nat_raw"
  by (auto iff: int_to_nat_raw_def)

lemma nat_le_eq_zle_raw:
  assumes a: "less_int_raw (0, 0) w \<or> le_int_raw (0, 0) z"
  shows "(int_to_nat_raw w \<le> int_to_nat_raw z) = (le_int_raw w z)"
  using a
  by (cases w, cases z) (auto simp add: int_to_nat_raw_def)

lemma nat_le_eq_zle:
  fixes w z::"int"
  shows "0 < w \<or> 0 \<le> z \<Longrightarrow> (int_to_nat w \<le> int_to_nat z) = (w \<le> z)"
  unfolding less_int_def
  by (lifting nat_le_eq_zle_raw)

end
