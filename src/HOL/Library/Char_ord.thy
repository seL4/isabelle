(*  Title:      HOL/Library/Char_ord.thy
    Author:     Norbert Voelker, Florian Haftmann
*)

section \<open>Order on characters\<close>

theory Char_ord
  imports Main
begin

context linordered_semidom
begin

lemma horner_sum_nonnegative:
  \<open>0 \<le> horner_sum of_bool 2 bs\<close>
  by (induction bs) simp_all

end

context unique_euclidean_semiring_numeral
begin

lemma horner_sum_bound:
  \<open>horner_sum of_bool 2 bs < 2 ^ length bs\<close>
proof (induction bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  moreover define a where \<open>a = 2 ^ length bs - horner_sum of_bool 2 bs\<close>
  ultimately have *: \<open>2 ^ length bs = horner_sum of_bool 2 bs + a\<close>
    by simp
  have \<open>1 < a * 2\<close> if \<open>0 < a\<close>
    using that add_mono [of 1 a 1 a]
    by (simp add: mult_2_right discrete)
  with Cons show ?case
    by (simp add: algebra_simps *)
qed

end

context unique_euclidean_semiring_numeral
begin

lemma horner_sum_less_eq_iff_lexordp_eq:
  \<open>horner_sum of_bool 2 bs \<le> horner_sum of_bool 2 cs \<longleftrightarrow> lexordp_eq (rev bs) (rev cs)\<close>
  if \<open>length bs = length cs\<close>
proof -
  have \<open>horner_sum of_bool 2 (rev bs) \<le> horner_sum of_bool 2 (rev cs) \<longleftrightarrow> lexordp_eq bs cs\<close>
    if \<open>length bs = length cs\<close> for bs cs
  using that proof (induction bs cs rule: list_induct2)
    case Nil
    then show ?case
      by simp
  next
    case (Cons b bs c cs)
    with horner_sum_nonnegative [of \<open>rev bs\<close>] horner_sum_nonnegative [of \<open>rev cs\<close>]
      horner_sum_bound [of \<open>rev bs\<close>] horner_sum_bound [of \<open>rev cs\<close>]
    show ?case
      by (auto simp add: horner_sum_append not_le Cons intro: add_strict_increasing2 add_increasing)
  qed
  from that this [of \<open>rev bs\<close> \<open>rev cs\<close>] show ?thesis
    by simp
qed

lemma horner_sum_less_iff_lexordp:
  \<open>horner_sum of_bool 2 bs < horner_sum of_bool 2 cs \<longleftrightarrow> ord_class.lexordp (rev bs) (rev cs)\<close>
  if \<open>length bs = length cs\<close>
proof -
  have \<open>horner_sum of_bool 2 (rev bs) < horner_sum of_bool 2 (rev cs) \<longleftrightarrow> ord_class.lexordp bs cs\<close>
    if \<open>length bs = length cs\<close> for bs cs
  using that proof (induction bs cs rule: list_induct2)
    case Nil
    then show ?case
      by simp
  next
    case (Cons b bs c cs)
    with horner_sum_nonnegative [of \<open>rev bs\<close>] horner_sum_nonnegative [of \<open>rev cs\<close>]
      horner_sum_bound [of \<open>rev bs\<close>] horner_sum_bound [of \<open>rev cs\<close>]
    show ?case
      by (auto simp add: horner_sum_append not_less Cons intro: add_strict_increasing2 add_increasing)
  qed
  from that this [of \<open>rev bs\<close> \<open>rev cs\<close>] show ?thesis
    by simp
qed

end

instantiation char :: linorder
begin

definition less_eq_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close>
  where \<open>c1 \<le> c2 \<longleftrightarrow> of_char c1 \<le> (of_char c2 :: nat)\<close>

definition less_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close>
  where \<open>c1 < c2 \<longleftrightarrow> of_char c1 < (of_char c2 :: nat)\<close>


instance
  by standard (auto simp add: less_eq_char_def less_char_def)

end

lemma less_eq_char_simp [simp, code]:
  \<open>Char b0 b1 b2 b3 b4 b5 b6 b7 \<le> Char c0 c1 c2 c3 c4 c5 c6 c7
    \<longleftrightarrow> lexordp_eq [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0]\<close>
  by (simp only: less_eq_char_def of_char_def char.sel horner_sum_less_eq_iff_lexordp_eq list.size) simp

lemma less_char_simp [simp, code]:
  \<open>Char b0 b1 b2 b3 b4 b5 b6 b7 < Char c0 c1 c2 c3 c4 c5 c6 c7
    \<longleftrightarrow> ord_class.lexordp [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0]\<close>
  by (simp only: less_char_def of_char_def char.sel horner_sum_less_iff_lexordp list.size) simp

instantiation char :: distrib_lattice
begin

definition \<open>(inf :: char \<Rightarrow> _) = min\<close>
definition \<open>(sup :: char \<Rightarrow> _) = max\<close>

instance
  by standard (auto simp add: inf_char_def sup_char_def max_min_distrib2)

end

end
