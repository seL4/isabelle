section \<open>Approximate Operations on Intervals of Floating Point Numbers\<close>
theory Interval_Float
  imports
    Interval
    Float
begin

definition mid :: "float interval \<Rightarrow> float"
  where "mid i = (lower i + upper i) * Float 1 (-1)"

lemma mid_in_interval: "mid i \<in>\<^sub>i i"
  using lower_le_upper[of i]
  by (auto simp: mid_def set_of_eq powr_minus)

lemma mid_le: "lower i \<le> mid i" "mid i \<le> upper i"
  using mid_in_interval
  by (auto simp: set_of_eq)

definition centered :: "float interval \<Rightarrow> float interval"
  where "centered i = i - interval_of (mid i)"

definition "split_float_interval x = split_interval x ((lower x + upper x) * Float 1 (-1))"

lemma split_float_intervalD: "split_float_interval X = (A, B) \<Longrightarrow> set_of X \<subseteq> set_of A \<union> set_of B"
  by (auto dest!: split_intervalD simp: split_float_interval_def)

lemma split_float_interval_bounds:
  shows
    lower_split_float_interval1: "lower (fst (split_float_interval X)) = lower X"
  and lower_split_float_interval2: "lower (snd (split_float_interval X)) = mid X"
  and upper_split_float_interval1: "upper (fst (split_float_interval X)) = mid X"
  and upper_split_float_interval2: "upper (snd (split_float_interval X)) = upper X"
  using mid_le[of X]
  by (auto simp: split_float_interval_def mid_def[symmetric] min_def max_def real_of_float_eq
      lower_split_interval1 lower_split_interval2
      upper_split_interval1 upper_split_interval2)

lemmas float_round_down_le[intro] = order_trans[OF float_round_down]
  and float_round_up_ge[intro] = order_trans[OF _ float_round_up]

text \<open>TODO: many of the lemmas should move to theories Float or Approximation
  (the latter should be based on type @{type interval}.\<close>

subsection "Intervals with Floating Point Bounds"

context includes interval.lifting begin

lift_definition round_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>p. \<lambda>(l, u). (float_round_down p l, float_round_up p u)"
  by (auto simp: intro!: float_round_down_le float_round_up_le)

lemma lower_round_ivl[simp]: "lower (round_interval p x) = float_round_down p (lower x)"
  by transfer auto
lemma upper_round_ivl[simp]: "upper (round_interval p x) = float_round_up p (upper x)"
  by transfer auto

lemma round_ivl_correct: "set_of A \<subseteq> set_of (round_interval prec A)"
  by (auto simp: set_of_eq float_round_down_le float_round_up_le)

lift_definition truncate_ivl :: "nat \<Rightarrow> real interval \<Rightarrow> real interval"
  is "\<lambda>p. \<lambda>(l, u). (truncate_down p l, truncate_up p u)"
  by (auto intro!: truncate_down_le truncate_up_le)

lemma lower_truncate_ivl[simp]: "lower (truncate_ivl p x) = truncate_down p (lower x)"
  by transfer auto
lemma upper_truncate_ivl[simp]: "upper (truncate_ivl p x) = truncate_up p (upper x)"
  by transfer auto

lemma truncate_ivl_correct: "set_of A \<subseteq> set_of (truncate_ivl prec A)"
  by (auto simp: set_of_eq intro!: truncate_down_le truncate_up_le)

lift_definition real_interval::"float interval \<Rightarrow> real interval"
  is "\<lambda>(l, u). (real_of_float l, real_of_float u)"
  by auto

lemma lower_real_interval[simp]: "lower (real_interval x) = lower x"
  by transfer auto
lemma upper_real_interval[simp]: "upper (real_interval x) = upper x"
  by transfer auto

definition "set_of' x = (case x of None \<Rightarrow> UNIV | Some i \<Rightarrow> set_of (real_interval i))"

lemma real_interval_min_interval[simp]:
  "real_interval (min_interval a b) = min_interval (real_interval a) (real_interval b)"
  by (auto simp: interval_eq_set_of_iff set_of_eq real_of_float_min)

lemma real_interval_max_interval[simp]:
  "real_interval (max_interval a b) = max_interval (real_interval a) (real_interval b)"
  by (auto simp: interval_eq_set_of_iff set_of_eq real_of_float_max)

lemma in_intervalI:
  "x \<in>\<^sub>i X" if "lower X \<le> x" "x \<le> upper X"
  using that by (auto simp: set_of_eq)

abbreviation in_real_interval ("(_/ \<in>\<^sub>r _)" [51, 51] 50) where
  "x \<in>\<^sub>r X \<equiv> x \<in>\<^sub>i real_interval X"

lemma in_real_intervalI:
  "x \<in>\<^sub>r X" if "lower X \<le> x" "x \<le> upper X" for x::real and X::"float interval"
  using that
  by (intro in_intervalI) auto

subsection \<open>intros for \<open>real_interval\<close>\<close>

lemma in_round_intervalI: "x \<in>\<^sub>r A  \<Longrightarrow> x \<in>\<^sub>r (round_interval prec A)"
  by (auto simp: set_of_eq float_round_down_le float_round_up_le)

lemma zero_in_float_intervalI: "0 \<in>\<^sub>r 0"
  by (auto simp: set_of_eq)

lemma plus_in_float_intervalI: "a + b \<in>\<^sub>r A + B" if "a \<in>\<^sub>r A" "b \<in>\<^sub>r B"
  using that
  by (auto simp: set_of_eq)

lemma minus_in_float_intervalI: "a - b \<in>\<^sub>r A - B" if "a \<in>\<^sub>r A" "b \<in>\<^sub>r B"
  using that
  by (auto simp: set_of_eq)

lemma uminus_in_float_intervalI: "-a \<in>\<^sub>r -A" if "a \<in>\<^sub>r A"
  using that
  by (auto simp: set_of_eq)

lemma real_interval_times: "real_interval (A * B) = real_interval A * real_interval B"
  by (auto simp: interval_eq_iff lower_times upper_times min_def max_def)

lemma times_in_float_intervalI: "a * b \<in>\<^sub>r A * B" if "a \<in>\<^sub>r A" "b \<in>\<^sub>r B"
  using times_in_intervalI[OF that]
  by (auto simp: real_interval_times)

lemma real_interval_abs: "real_interval (abs_interval A) = abs_interval (real_interval A)"
  by (auto simp: interval_eq_iff min_def max_def)

lemma abs_in_float_intervalI: "abs a \<in>\<^sub>r abs_interval A" if "a \<in>\<^sub>r A"
  by (auto simp: set_of_abs_interval real_interval_abs intro!: imageI that)

lemma interval_of[intro,simp]: "x \<in>\<^sub>r interval_of x"
  by (auto simp: set_of_eq)

lemma split_float_interval_realD: "split_float_interval X = (A, B) \<Longrightarrow> x \<in>\<^sub>r X \<Longrightarrow> x \<in>\<^sub>r A \<or> x \<in>\<^sub>r B"
  by (auto simp: set_of_eq prod_eq_iff split_float_interval_bounds)


subsection \<open>bounds for lists\<close>

lemma lower_Interval: "lower (Interval x) = fst x"
  and upper_Interval: "upper (Interval x) = snd x"
  if "fst x \<le> snd x"
  using that
  by (auto simp: lower_def upper_def Interval_inverse split_beta')

definition all_in_i :: "'a::preorder list \<Rightarrow> 'a interval list \<Rightarrow> bool"
  (infix "(all'_in\<^sub>i)" 50)
  where "x all_in\<^sub>i I = (length x = length I \<and> (\<forall>i < length I. x ! i \<in>\<^sub>i I ! i))"

definition all_in :: "real list \<Rightarrow> float interval list \<Rightarrow> bool"
  (infix "(all'_in)" 50)
  where "x all_in I = (length x = length I \<and> (\<forall>i < length I. x ! i \<in>\<^sub>r I ! i))"

definition all_subset :: "'a::order interval list \<Rightarrow> 'a interval list \<Rightarrow> bool"
  (infix "(all'_subset)" 50)
  where "I all_subset J = (length I = length J \<and> (\<forall>i < length I. set_of (I!i) \<subseteq> set_of (J!i)))"

lemmas [simp] = all_in_def all_subset_def

lemma all_subsetD:
  assumes "I all_subset J"
  assumes "x all_in I"
  shows "x all_in J"
  using assms
  by (auto simp: set_of_eq; fastforce)

lemma round_interval_mono: "set_of (round_interval prec X) \<subseteq> set_of (round_interval prec Y)"
  if "set_of X \<subseteq> set_of Y"
  using that
  by transfer
    (auto simp: float_round_down.rep_eq float_round_up.rep_eq truncate_down_mono truncate_up_mono)

lemma Ivl_simps[simp]: "lower (Ivl a b) = min a b" "upper (Ivl a b) = b"
  subgoal by transfer simp
  subgoal by transfer simp
  done

lemma set_of_subset_iff: "set_of X \<subseteq> set_of Y \<longleftrightarrow> lower Y \<le> lower X \<and> upper X \<le> upper Y"
  for X Y::"'a::linorder interval"
  by (auto simp: set_of_eq subset_iff)

lemma set_of_subset_iff':
  "set_of a \<subseteq> set_of (b :: 'a :: linorder interval) \<longleftrightarrow> a \<le> b"
  unfolding less_eq_interval_def set_of_subset_iff ..

lemma bounds_of_interval_eq_lower_upper:
  "bounds_of_interval ivl = (lower ivl, upper ivl)" if "lower ivl \<le> upper ivl"
  using that
  by (auto simp: lower.rep_eq upper.rep_eq)

lemma real_interval_Ivl: "real_interval (Ivl a b) = Ivl a b"
  by transfer (auto simp: min_def)

lemma set_of_mul_contains_real_zero:
  "0 \<in>\<^sub>r (A * B)" if "0 \<in>\<^sub>r A \<or> 0 \<in>\<^sub>r B"
  using that set_of_mul_contains_zero[of A B]
  by (auto simp: set_of_eq)

fun subdivide_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval list"
  where "subdivide_interval 0 I = [I]"
  | "subdivide_interval (Suc n) I = (
         let m = mid I
         in (subdivide_interval n (Ivl (lower I) m)) @ (subdivide_interval n (Ivl m (upper I)))
       )"

lemma subdivide_interval_length:
  shows "length (subdivide_interval n I) = 2^n"
  by(induction n arbitrary: I, simp_all add: Let_def)

lemma lower_le_mid: "lower x \<le> mid x" "real_of_float (lower x) \<le> mid x"
  and mid_le_upper: "mid x \<le> upper x" "real_of_float (mid x) \<le> upper x"
  unfolding mid_def
  subgoal by transfer (auto simp: powr_neg_one)
  subgoal by transfer (auto simp: powr_neg_one)
  subgoal by transfer (auto simp: powr_neg_one)
  subgoal by transfer (auto simp: powr_neg_one)
  done

lemma subdivide_interval_correct:
  "list_ex (\<lambda>i. x \<in>\<^sub>r i) (subdivide_interval n I)" if "x \<in>\<^sub>r I" for x::real
  using that
proof(induction n arbitrary: x I)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from \<open>x \<in>\<^sub>r I\<close> consider "x \<in>\<^sub>r Ivl (lower I) (mid I)" | "x \<in>\<^sub>r Ivl (mid I) (upper I)"
    by (cases "x \<le> real_of_float (mid I)")
      (auto simp: set_of_eq min_def lower_le_mid mid_le_upper)
  from this[case_names lower upper] show ?case
    by cases (use Suc.IH in \<open>auto simp: Let_def\<close>)
qed

fun interval_list_union :: "'a::lattice interval list \<Rightarrow> 'a interval"
  where "interval_list_union [] = undefined"
  | "interval_list_union [I] = I"
  | "interval_list_union (I#Is) = sup I (interval_list_union Is)"

lemma interval_list_union_correct:
  assumes "S \<noteq> []"
  assumes "i < length S"
  shows "set_of (S!i) \<subseteq> set_of (interval_list_union S)"
  using assms
proof(induction S arbitrary: i)
  case (Cons a S i)
  thus ?case
  proof(cases S)
    fix b S'
    assume "S = b # S'"
    hence "S \<noteq> []"
      by simp
    show ?thesis
    proof(cases i)
      case 0
      show ?thesis
        apply(cases S)
        using interval_union_mono1
        by (auto simp add: 0)
    next
      case (Suc i_prev)
      hence "i_prev < length S"
        using Cons(3) by simp

      from Cons(1)[OF \<open>S \<noteq> []\<close> this] Cons(1)
      have "set_of ((a # S) ! i) \<subseteq> set_of (interval_list_union S)"
        by (simp add: \<open>i = Suc i_prev\<close>)
      also have "... \<subseteq> set_of (interval_list_union (a # S))"
        using \<open>S \<noteq> []\<close>
        apply(cases S)
        using interval_union_mono2
        by auto
      finally show ?thesis .
    qed
  qed simp
qed simp

lemma split_domain_correct:
  fixes x :: "real list"
  assumes "x all_in I"
  assumes split_correct: "\<And>x a I. x \<in>\<^sub>r I \<Longrightarrow> list_ex (\<lambda>i::float interval. x \<in>\<^sub>r i) (split I)"
  shows "list_ex (\<lambda>s. x all_in s) (split_domain split I)"
  using assms(1)
proof(induction I arbitrary: x)
  case (Cons I Is x)
  have "x \<noteq> []"
    using Cons(2) by auto
  obtain x' xs where x_decomp: "x = x' # xs"
    using \<open>x \<noteq> []\<close> list.exhaust by auto
  hence "x' \<in>\<^sub>r I" "xs all_in Is"
    using Cons(2)
    by auto
  show ?case
    using Cons(1)[OF \<open>xs all_in Is\<close>]
      split_correct[OF \<open>x' \<in>\<^sub>r I\<close>]
    apply (auto simp add: list_ex_iff set_of_eq)
    by (smt length_Cons less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc x_decomp)
qed simp


lift_definition(code_dt) inverse_float_interval::"nat \<Rightarrow> float interval \<Rightarrow> float interval option" is
  "\<lambda>prec (l, u). if (0 < l \<or> u < 0) then Some (float_divl prec 1 u, float_divr prec 1 l) else None"
  by (auto intro!: order_trans[OF float_divl] order_trans[OF _ float_divr]
      simp: divide_simps)

lemma inverse_float_interval_eq_Some_conv:
  defines "one \<equiv> (1::float)"
  shows 
    "inverse_float_interval p X = Some R \<longleftrightarrow>
    (lower X > 0 \<or> upper X < 0) \<and>
    lower R = float_divl p one (upper X) \<and>
    upper R = float_divr p one (lower X)"
  by clarsimp (transfer fixing: one, force simp: one_def split: if_splits)

lemma inverse_float_interval:
  "inverse ` set_of (real_interval X) \<subseteq> set_of (real_interval Y)"
  if "inverse_float_interval p X = Some Y"
  using that
  apply (clarsimp simp: set_of_eq inverse_float_interval_eq_Some_conv)
  by (intro order_trans[OF float_divl] order_trans[OF _ float_divr] conjI)
    (auto simp: divide_simps)

lemma inverse_float_intervalI:
  "x \<in>\<^sub>r X \<Longrightarrow> inverse x \<in> set_of' (inverse_float_interval p X)"
  using inverse_float_interval[of p X]
  by (auto simp: set_of'_def split: option.splits)

lemma inverse_float_interval_eqI: "inverse_float_interval p X = Some IVL \<Longrightarrow> x \<in>\<^sub>r X \<Longrightarrow> inverse x \<in>\<^sub>r IVL"
  using inverse_float_intervalI[of x X p]
  by (auto simp: set_of'_def)

lemma real_interval_abs_interval[simp]:
  "real_interval (abs_interval x) = abs_interval (real_interval x)"
  by (auto simp: interval_eq_set_of_iff set_of_eq real_of_float_max real_of_float_min)

lift_definition floor_float_interval::"float interval \<Rightarrow> float interval" is
  "\<lambda>(l, u). (floor_fl l, floor_fl u)"
  by (auto intro!: floor_mono simp: floor_fl.rep_eq)

lemma lower_floor_float_interval[simp]: "lower (floor_float_interval x) = floor_fl (lower x)"
  by transfer auto
lemma upper_floor_float_interval[simp]: "upper (floor_float_interval x) = floor_fl (upper x)"
  by transfer auto

lemma floor_float_intervalI: "\<lfloor>x\<rfloor> \<in>\<^sub>r floor_float_interval X" if "x \<in>\<^sub>r X"
  using that by (auto simp: set_of_eq floor_fl_def floor_mono)

end


subsection \<open>constants for code generation\<close>

definition lowerF::"float interval \<Rightarrow> float" where "lowerF = lower"
definition upperF::"float interval \<Rightarrow> float" where "upperF = upper"


end