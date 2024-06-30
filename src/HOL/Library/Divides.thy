(*  Title:      HOL/Library/Divides.thy
*)

section \<open>Misc lemmas on division, to be sorted out finally\<close>

theory Divides
imports Main
begin

class unique_euclidean_semiring_numeral = linordered_euclidean_semiring + discrete_linordered_semidom +
  assumes div_less [no_atp]: "0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a div b = 0"
    and mod_less [no_atp]: " 0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a mod b = a"
    and div_positive [no_atp]: "0 < b \<Longrightarrow> b \<le> a \<Longrightarrow> a div b > 0"
    and mod_less_eq_dividend [no_atp]: "0 \<le> a \<Longrightarrow> a mod b \<le> a"
    and pos_mod_bound [no_atp]: "0 < b \<Longrightarrow> a mod b < b"
    and pos_mod_sign [no_atp]: "0 < b \<Longrightarrow> 0 \<le> a mod b"
    and mod_mult2_eq [no_atp]: "0 \<le> c \<Longrightarrow> a mod (b * c) = b * (a div b mod c) + a mod b"
    and div_mult2_eq [no_atp]: "0 \<le> c \<Longrightarrow> a div (b * c) = a div b div c"

hide_fact (open) div_less mod_less div_positive mod_less_eq_dividend pos_mod_bound pos_mod_sign mod_mult2_eq div_mult2_eq

context unique_euclidean_semiring_numeral
begin

context
begin

qualified lemma discrete [no_atp]:
  "a < b \<longleftrightarrow> a + 1 \<le> b"
  by (fact less_iff_succ_less_eq)

qualified lemma divmod_digit_1 [no_atp]:
  assumes "0 \<le> a" "0 < b" and "b \<le> a mod (2 * b)"
  shows "2 * (a div (2 * b)) + 1 = a div b" (is "?P")
    and "a mod (2 * b) - b = a mod b" (is "?Q")
proof -
  from assms mod_less_eq_dividend [of a "2 * b"] have "b \<le> a"
    by (auto intro: trans)
  with \<open>0 < b\<close> have "0 < a div b" by (auto intro: div_positive)
  then have [simp]: "1 \<le> a div b" by (simp add: discrete)
  with \<open>0 < b\<close> have mod_less: "a mod b < b" by (simp add: pos_mod_bound)
  define w where "w = a div b mod 2"
  then have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  from assms w_exhaust have "w = 1"
    using mod_less by (auto simp add: mod_w)
  with mod_w have mod: "a mod (2 * b) = a mod b + b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq minus_mod_eq_mult_div ac_simps)
  with \<open>w = 1\<close> have div: "2 * (a div (2 * b)) = a div b - 1" by simp
  then show ?P and ?Q
    by (simp_all add: div mod add_implies_diff [symmetric])
qed

qualified lemma divmod_digit_0 [no_atp]:
  assumes "0 < b" and "a mod (2 * b) < b"
  shows "2 * (a div (2 * b)) = a div b" (is "?P")
    and "a mod (2 * b) = a mod b" (is "?Q")
proof -
  define w where "w = a div b mod 2"
  then have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  moreover have "b \<le> a mod b + b"
  proof -
    from \<open>0 < b\<close> pos_mod_sign have "0 \<le> a mod b" by blast
    then have "0 + b \<le> a mod b + b" by (rule add_right_mono)
    then show ?thesis by simp
  qed
  moreover note assms w_exhaust
  ultimately have "w = 0" by auto
  with mod_w have mod: "a mod (2 * b) = a mod b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq minus_mod_eq_mult_div ac_simps)
  with \<open>w = 0\<close> have div: "2 * (a div (2 * b)) = a div b" by simp
  then show ?P and ?Q
    by (simp_all add: div mod)
qed

qualified lemma mod_double_modulus [no_atp]:
  assumes "m > 0" "x \<ge> 0"
  shows   "x mod (2 * m) = x mod m \<or> x mod (2 * m) = x mod m + m"
proof (cases "x mod (2 * m) < m")
  case True
  thus ?thesis using assms using divmod_digit_0(2)[of m x] by auto
next
  case False
  hence *: "x mod (2 * m) - m = x mod m"
    using assms by (intro divmod_digit_1) auto
  hence "x mod (2 * m) = x mod m + m"
    by (subst * [symmetric], subst le_add_diff_inverse2) (use False in auto)
  thus ?thesis by simp
qed

end

end

instance nat :: unique_euclidean_semiring_numeral
  by standard
    (auto simp add: div_greater_zero_iff div_mult2_eq mod_mult2_eq)

instance int :: unique_euclidean_semiring_numeral
  by standard (auto intro: zmod_le_nonneg_dividend simp add:
    pos_imp_zdiv_pos_iff zmod_zmult2_eq zdiv_zmult2_eq)

context
begin

qualified lemma zmod_eq_0D: "\<exists>q. m = d * q" if "m mod d = 0" for m d :: int
  using that by auto

qualified lemma div_geq [no_atp]: "m div n = Suc ((m - n) div n)" if "0 < n" and " \<not> m < n" for m n :: nat
  by (rule le_div_geq) (use that in \<open>simp_all add: not_less\<close>)

qualified lemma mod_geq [no_atp]: "m mod n = (m - n) mod n" if "\<not> m < n" for m n :: nat
  by (rule le_mod_geq) (use that in \<open>simp add: not_less\<close>)

qualified lemma mod_eq_0D [no_atp]: "\<exists>q. m = d * q" if "m mod d = 0" for m d :: nat
  using that by (auto simp add: mod_eq_0_iff_dvd)

qualified lemma pos_mod_conj [no_atp]: "0 < b \<Longrightarrow> 0 \<le> a mod b \<and> a mod b < b" for a b :: int
  by simp

qualified lemma neg_mod_conj [no_atp]: "b < 0 \<Longrightarrow> a mod b \<le> 0 \<and> b < a mod b" for a b :: int
  by simp

qualified lemma zmod_eq_0_iff [no_atp]: "m mod d = 0 \<longleftrightarrow> (\<exists>q. m = d * q)" for m d :: int
  by (auto simp add: mod_eq_0_iff_dvd)

qualified lemma div_positive_int [no_atp]:
  "k div l > 0" if "k \<ge> l" and "l > 0" for k l :: int
  using that by (simp add: nonneg1_imp_zdiv_pos_iff)

end

code_identifier
  code_module Divides \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
