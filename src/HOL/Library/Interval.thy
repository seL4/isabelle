(* Title: Interval
   Author: Christoph Traut, TU Muenchen
           Fabian Immler, TU Muenchen
*)
section \<open>Interval Type\<close>
theory Interval
  imports
    Complex_Main
    Lattice_Algebras
    Set_Algebras
begin

text \<open>A type of non-empty, closed intervals.\<close>

typedef (overloaded) 'a interval =
  "{(a::'a::preorder, b). a \<le> b}"
  morphisms bounds_of_interval Interval
  by auto

setup_lifting type_definition_interval

lift_definition lower::"('a::preorder) interval \<Rightarrow> 'a" is fst .

lift_definition upper::"('a::preorder) interval \<Rightarrow> 'a" is snd .

lemma interval_eq_iff: "a = b \<longleftrightarrow> lower a = lower b \<and> upper a = upper b"
  by transfer auto

lemma interval_eqI: "lower a = lower b \<Longrightarrow> upper a = upper b \<Longrightarrow> a = b"
  by (auto simp: interval_eq_iff)

lemma lower_le_upper[simp]: "lower i \<le> upper i"
  by transfer auto

lift_definition set_of :: "'a::preorder interval \<Rightarrow> 'a set" is "\<lambda>x. {fst x .. snd x}" .

lemma set_of_eq: "set_of x = {lower x .. upper x}"
  by transfer simp

context notes [[typedef_overloaded]] begin

lift_definition(code_dt) Interval'::"'a::preorder \<Rightarrow> 'a::preorder \<Rightarrow> 'a interval option"
  is "\<lambda>a b. if a \<le> b then Some (a, b) else None"
  by auto

lemma Interval'_split:
  "P (Interval' a b) \<longleftrightarrow>
    (\<forall>ivl. a \<le> b \<longrightarrow> lower ivl = a \<longrightarrow> upper ivl = b \<longrightarrow> P (Some ivl)) \<and> (\<not>a\<le>b \<longrightarrow> P None)"
  by transfer auto

lemma Interval'_split_asm:
  "P (Interval' a b) \<longleftrightarrow>
    \<not>((\<exists>ivl. a \<le> b \<and> lower ivl = a \<and> upper ivl = b \<and> \<not>P (Some ivl)) \<or> (\<not>a\<le>b \<and> \<not>P None))"
  unfolding Interval'_split
  by auto

lemmas Interval'_splits = Interval'_split Interval'_split_asm

lemma Interval'_eq_Some: "Interval' a b = Some i \<Longrightarrow> lower i = a \<and> upper i = b"
  by (simp split: Interval'_splits)

end

instantiation "interval" :: ("{preorder,equal}") equal
begin

definition "equal_class.equal a b \<equiv> (lower a = lower b) \<and> (upper a = upper b)"

instance proof qed (simp add: equal_interval_def interval_eq_iff)
end

instantiation interval :: ("preorder") ord begin

definition less_eq_interval :: "'a interval \<Rightarrow> 'a interval \<Rightarrow> bool"
  where "less_eq_interval a b \<longleftrightarrow> lower b \<le> lower a \<and> upper a \<le> upper b"

definition less_interval :: "'a interval \<Rightarrow> 'a interval \<Rightarrow> bool"
  where  "less_interval x y = (x \<le> y \<and> \<not> y \<le> x)"

instance proof qed
end

instantiation interval :: ("lattice") semilattice_sup
begin

lift_definition sup_interval :: "'a interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval"
  is "\<lambda>(a, b) (c, d). (inf a c, sup b d)"
  by (auto simp: le_infI1 le_supI1)

lemma lower_sup[simp]: "lower (sup A B) = inf (lower A) (lower B)"
  by transfer auto

lemma upper_sup[simp]: "upper (sup A B) = sup (upper A) (upper B)"
  by transfer auto

instance proof qed (auto simp: less_eq_interval_def less_interval_def interval_eq_iff)
end

lemma set_of_interval_union: "set_of A \<union> set_of B \<subseteq> set_of (sup A B)" for A::"'a::lattice interval"
  by (auto simp: set_of_eq)

lemma interval_union_commute: "sup A B = sup B A" for A::"'a::lattice interval"
  by (auto simp add: interval_eq_iff inf.commute sup.commute)

lemma interval_union_mono1: "set_of a \<subseteq> set_of (sup a A)" for A :: "'a::lattice interval"
  using set_of_interval_union by blast

lemma interval_union_mono2: "set_of A \<subseteq> set_of (sup a A)" for A :: "'a::lattice interval"
  using set_of_interval_union by blast

lift_definition interval_of :: "'a::preorder \<Rightarrow> 'a interval" is "\<lambda>x. (x, x)"
  by auto

lemma lower_interval_of[simp]: "lower (interval_of a) = a"
  by transfer auto

lemma upper_interval_of[simp]: "upper (interval_of a) = a"
  by transfer auto

definition width :: "'a::{preorder,minus} interval \<Rightarrow> 'a"
  where "width i = upper i - lower i"


instantiation "interval" :: ("ordered_ab_semigroup_add") ab_semigroup_add
begin

lift_definition plus_interval::"'a interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval"
  is "\<lambda>(a, b). \<lambda>(c, d). (a + c, b + d)"
  by (auto intro!: add_mono)
lemma lower_plus[simp]: "lower (plus A B) = plus (lower A) (lower B)"
  by transfer auto
lemma upper_plus[simp]: "upper (plus A B) = plus (upper A) (upper B)"
  by transfer auto

instance proof qed (auto simp: interval_eq_iff less_eq_interval_def ac_simps)
end

instance "interval" :: ("{ordered_ab_semigroup_add, lattice}") ordered_ab_semigroup_add
proof qed (auto simp: less_eq_interval_def intro!: add_mono)

instantiation "interval" :: ("{preorder,zero}") zero
begin

lift_definition zero_interval::"'a interval" is "(0, 0)" by auto
lemma lower_zero[simp]: "lower 0 = 0"
  by transfer auto
lemma upper_zero[simp]: "upper 0 = 0"
  by transfer auto
instance proof qed
end

instance "interval" :: ("{ordered_comm_monoid_add}") comm_monoid_add
proof qed (auto simp: interval_eq_iff)

instance "interval" :: ("{ordered_comm_monoid_add,lattice}") ordered_comm_monoid_add ..

instantiation "interval" :: ("{ordered_ab_group_add}") uminus
begin

lift_definition uminus_interval::"'a interval \<Rightarrow> 'a interval" is "\<lambda>(a, b). (-b, -a)" by auto
lemma lower_uminus[simp]: "lower (- A) = - upper A"
  by transfer auto
lemma upper_uminus[simp]: "upper (- A) = - lower A"
  by transfer auto
instance ..
end

instantiation "interval" :: ("{ordered_ab_group_add}") minus
begin

definition minus_interval::"'a interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval"
  where "minus_interval a b = a + - b"
lemma lower_minus[simp]: "lower (minus A B) = minus (lower A) (upper B)"
  by (auto simp: minus_interval_def)
lemma upper_minus[simp]: "upper (minus A B) = minus (upper A) (lower B)"
  by (auto simp: minus_interval_def)

instance ..
end

instantiation "interval" :: (linordered_semiring) times
begin

lift_definition times_interval :: "'a interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval"
  is "\<lambda>(a1, a2). \<lambda>(b1, b2).
    (let x1 = a1 * b1; x2 = a1 * b2; x3 = a2 * b1; x4 = a2 * b2
    in (min x1 (min x2 (min x3 x4)), max x1 (max x2 (max x3 x4))))"
  by (auto simp: Let_def intro!: min.coboundedI1 max.coboundedI1)

lemma lower_times:
  "lower (times A B) = Min {lower A * lower B, lower A * upper B, upper A * lower B, upper A * upper B}"
  by transfer (auto simp: Let_def)

lemma upper_times:
  "upper (times A B) = Max {lower A * lower B, lower A * upper B, upper A * lower B, upper A * upper B}"
  by transfer (auto simp: Let_def)

instance ..
end

lemma interval_eq_set_of_iff: "X = Y \<longleftrightarrow> set_of X = set_of Y" for X Y::"'a::order interval"
  by (auto simp: set_of_eq interval_eq_iff)


subsection \<open>Membership\<close>

abbreviation (in preorder) in_interval ("(_/ \<in>\<^sub>i _)" [51, 51] 50)
  where "in_interval x X \<equiv> x \<in> set_of X"

lemma in_interval_to_interval[intro!]: "a \<in>\<^sub>i interval_of a"
  by (auto simp: set_of_eq)

lemma plus_in_intervalI:
  fixes x y :: "'a :: ordered_ab_semigroup_add"
  shows "x \<in>\<^sub>i X \<Longrightarrow> y \<in>\<^sub>i Y \<Longrightarrow> x + y \<in>\<^sub>i X + Y"
  by (simp add: add_mono_thms_linordered_semiring(1) set_of_eq)

lemma connected_set_of[intro, simp]:
  "connected (set_of X)" for X::"'a::linear_continuum_topology interval"
  by (auto simp: set_of_eq )

lemma ex_sum_in_interval_lemma: "\<exists>xa\<in>{la .. ua}. \<exists>xb\<in>{lb .. ub}. x = xa + xb"
  if "la \<le> ua" "lb \<le> ub" "la + lb \<le> x" "x \<le> ua + ub"
    "ua - la \<le> ub - lb"
  for la b c d::"'a::linordered_ab_group_add"
proof -
  define wa where "wa = ua - la"
  define wb where "wb = ub - lb"
  define w where "w = wa + wb"
  define d where "d = x - la - lb"
  define da where "da = max 0 (min wa (d - wa))"
  define db where "db = d - da"
  from that have nonneg: "0 \<le> wa" "0 \<le> wb" "0 \<le> w" "0 \<le> d" "d \<le> w"
    by (auto simp add: wa_def wb_def w_def d_def add.commute le_diff_eq)
  have "0 \<le> db"
    by (auto simp: da_def nonneg db_def intro!: min.coboundedI2)
  have "x = (la + da) + (lb + db)"
    by (simp add: da_def db_def d_def)
  moreover
  have "x - la - ub \<le> da"
    using that
    unfolding da_def
    by (intro max.coboundedI2) (auto simp: wa_def d_def diff_le_eq diff_add_eq)
  then have "db \<le> wb"
    by (auto simp: db_def d_def wb_def algebra_simps)
  with \<open>0 \<le> db\<close> that nonneg have "lb + db \<in> {lb..ub}"
    by (auto simp: wb_def algebra_simps)
  moreover
  have "da \<le> wa"
    by (auto simp: da_def nonneg)
  then have "la + da \<in> {la..ua}"
    by (auto simp: da_def wa_def algebra_simps)
  ultimately show ?thesis
    by force
qed


lemma ex_sum_in_interval: "\<exists>xa\<ge>la. xa \<le> ua \<and> (\<exists>xb\<ge>lb. xb \<le> ub \<and> x = xa + xb)"
  if a: "la \<le> ua" and b: "lb \<le> ub" and x: "la + lb \<le> x" "x \<le> ua + ub"
  for la b c d::"'a::linordered_ab_group_add"
proof -
  from linear consider "ua - la \<le> ub - lb" | "ub - lb \<le> ua - la"
    by blast
  then show ?thesis
  proof cases
    case 1
    from ex_sum_in_interval_lemma[OF that 1]
    show ?thesis by auto
  next
    case 2
    from x have "lb + la \<le> x" "x \<le> ub + ua" by (simp_all add: ac_simps)
    from ex_sum_in_interval_lemma[OF b a this 2]
    show ?thesis by auto
  qed
qed

lemma Icc_plus_Icc:
  "{a .. b} + {c .. d} = {a + c .. b + d}"
  if "a \<le> b" "c \<le> d"
  for a b c d::"'a::linordered_ab_group_add"
  using ex_sum_in_interval[OF that]
  by (auto intro: add_mono simp: atLeastAtMost_iff Bex_def set_plus_def)

lemma set_of_plus:
  fixes A :: "'a::linordered_ab_group_add interval"
  shows "set_of (A + B) = set_of A + set_of B"
  using Icc_plus_Icc[of "lower A" "upper A" "lower B" "upper B"]
  by (auto simp: set_of_eq)

lemma plus_in_intervalE:
  fixes xy :: "'a :: linordered_ab_group_add"
  assumes "xy \<in>\<^sub>i X + Y"
  obtains x y where "xy = x + y" "x \<in>\<^sub>i X" "y \<in>\<^sub>i Y"
  using assms
  unfolding set_of_plus set_plus_def
  by auto

lemma set_of_uminus: "set_of (-X) = {- x | x. x \<in> set_of X}"
  for X :: "'a :: ordered_ab_group_add interval"
  by (auto simp: set_of_eq simp: le_minus_iff minus_le_iff
      intro!: exI[where x="-x" for x])

lemma uminus_in_intervalI:
  fixes x :: "'a :: ordered_ab_group_add"
  shows "x \<in>\<^sub>i X \<Longrightarrow> -x \<in>\<^sub>i -X"
  by (auto simp: set_of_uminus)

lemma uminus_in_intervalD:
  fixes x :: "'a :: ordered_ab_group_add"
  shows "x \<in>\<^sub>i - X \<Longrightarrow> - x \<in>\<^sub>i X"
  by (auto simp: set_of_uminus)

lemma minus_in_intervalI:
  fixes x y :: "'a :: ordered_ab_group_add"
  shows "x \<in>\<^sub>i X \<Longrightarrow> y \<in>\<^sub>i Y \<Longrightarrow> x - y \<in>\<^sub>i X - Y"
  by (metis diff_conv_add_uminus minus_interval_def plus_in_intervalI uminus_in_intervalI)

lemma set_of_minus: "set_of (X - Y) = {x - y | x y . x \<in> set_of X \<and> y \<in> set_of Y}"
  for X Y :: "'a :: linordered_ab_group_add interval"
  unfolding minus_interval_def set_of_plus set_of_uminus set_plus_def
  by force

lemma times_in_intervalI:
  fixes x y::"'a::linordered_ring"
  assumes "x \<in>\<^sub>i X" "y \<in>\<^sub>i Y"
  shows "x * y \<in>\<^sub>i X * Y"
proof -
  define X1 where "X1 \<equiv> lower X"
  define X2 where "X2 \<equiv> upper X"
  define Y1 where "Y1 \<equiv> lower Y"
  define Y2 where "Y2 \<equiv> upper Y"
  from assms have assms: "X1 \<le> x" "x \<le> X2" "Y1 \<le> y" "y \<le> Y2"
    by (auto simp: X1_def X2_def Y1_def Y2_def set_of_eq)
  have "(X1 * Y1 \<le> x * y \<or> X1 * Y2 \<le> x * y \<or> X2 * Y1 \<le> x * y \<or> X2 * Y2 \<le> x * y) \<and>
        (X1 * Y1 \<ge> x * y \<or> X1 * Y2 \<ge> x * y \<or> X2 * Y1 \<ge> x * y \<or> X2 * Y2 \<ge> x * y)"
  proof (cases x "0::'a" rule: linorder_cases)
    case x0: less
    show ?thesis
    proof (cases "y < 0")
      case y0: True
      from y0 x0 assms have "x * y \<le> X1 * y" by (intro mult_right_mono_neg, auto)
      also from x0 y0 assms have "X1 * y \<le> X1 * Y1" by (intro mult_left_mono_neg, auto)
      finally have 1: "x * y \<le> X1 * Y1".
      show ?thesis proof(cases "X2 \<le> 0")
        case True
        with assms have "X2 * Y2 \<le> X2 * y" by (auto intro: mult_left_mono_neg)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono_neg)
        finally have "X2 * Y2 \<le> x * y".
        with 1 show ?thesis by auto
      next
        case False
        with assms have "X2 * Y1 \<le> X2 * y" by (auto intro: mult_left_mono)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono_neg)
        finally have "X2 * Y1 \<le> x * y".
        with 1 show ?thesis by auto
      qed
    next
      case False
      then have y0: "y \<ge> 0" by auto
      from x0 y0 assms have "X1 * Y2 \<le> x * Y2" by (intro mult_right_mono, auto)
      also from y0 x0 assms have "... \<le> x * y" by (intro mult_left_mono_neg, auto)
      finally have 1: "X1 * Y2 \<le> x * y".
      show ?thesis
      proof(cases "X2 \<le> 0")
        case X2: True
        from assms y0 have "x * y \<le> X2 * y" by (intro mult_right_mono)
        also from assms X2 have "... \<le> X2 * Y1" by (auto intro: mult_left_mono_neg)
        finally have "x * y \<le> X2 * Y1".
        with 1 show ?thesis by auto
      next
        case X2: False
        from assms y0 have "x * y \<le> X2 * y" by (intro mult_right_mono)
        also from assms X2 have "... \<le> X2 * Y2" by (auto intro: mult_left_mono)
        finally have "x * y \<le> X2 * Y2".
        with 1 show ?thesis by auto
      qed
    qed
  next
    case [simp]: equal
    with assms show ?thesis by (cases "Y2 \<le> 0", auto intro:mult_sign_intros)
  next
    case x0: greater
    show ?thesis
    proof (cases "y < 0")
      case y0: True
      from x0 y0 assms have "X2 * Y1 \<le> X2 * y" by (intro mult_left_mono, auto)
      also from y0 x0 assms have "X2 * y \<le> x * y" by (intro mult_right_mono_neg, auto)
      finally have 1: "X2 * Y1 \<le> x * y".
      show ?thesis
      proof(cases "Y2 \<le> 0")
        case Y2: True
        from x0 assms have "x * y \<le> x * Y2" by (auto intro: mult_left_mono)
        also from assms Y2 have "... \<le> X1 * Y2" by (auto intro: mult_right_mono_neg)
        finally have "x * y \<le> X1 * Y2".
        with 1 show ?thesis by auto
      next
        case Y2: False
        from x0 assms have "x * y \<le> x * Y2" by (auto intro: mult_left_mono)
        also from assms Y2 have "... \<le> X2 * Y2" by (auto intro: mult_right_mono)
        finally have "x * y \<le> X2 * Y2".
        with 1 show ?thesis by auto
      qed
    next
      case y0: False
      from x0 y0 assms have "x * y \<le> X2 * y" by (intro mult_right_mono, auto)
      also from y0 x0 assms have "... \<le> X2 * Y2" by (intro mult_left_mono, auto)
      finally have 1: "x * y \<le> X2 * Y2".
      show ?thesis
      proof(cases "X1 \<le> 0")
        case True
        with assms have "X1 * Y2 \<le> X1 * y" by (auto intro: mult_left_mono_neg)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono)
        finally have "X1 * Y2 \<le> x * y".
        with 1 show ?thesis by auto
      next
        case False
        with assms have "X1 * Y1 \<le> X1 * y" by (auto intro: mult_left_mono)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono)
        finally have "X1 * Y1 \<le> x * y".
        with 1 show ?thesis by auto
      qed
    qed
  qed
  hence min:"min (X1 * Y1) (min (X1 * Y2) (min (X2 * Y1) (X2 * Y2))) \<le> x * y"
    and max:"x * y \<le> max (X1 * Y1) (max (X1 * Y2) (max (X2 * Y1) (X2 * Y2)))"
    by (auto simp:min_le_iff_disj le_max_iff_disj)
  show ?thesis using min max
    by (auto simp: Let_def X1_def X2_def Y1_def Y2_def set_of_eq lower_times upper_times)
qed

lemma times_in_intervalE:
  fixes xy :: "'a :: {linordered_semiring, real_normed_algebra, linear_continuum_topology}"
    \<comment> \<open>TODO: linear continuum topology is pretty strong\<close>
  assumes "xy \<in>\<^sub>i X * Y"
  obtains x y where "xy = x * y" "x \<in>\<^sub>i X" "y \<in>\<^sub>i Y"
proof -
  let ?mult = "\<lambda>(x, y). x * y"
  let ?XY = "set_of X \<times> set_of Y"
  have cont: "continuous_on ?XY ?mult"
    by (auto intro!: tendsto_eq_intros simp: continuous_on_def split_beta')
  have conn: "connected (?mult ` ?XY)"
    by (rule connected_continuous_image[OF cont]) auto
  have "lower (X * Y) \<in> ?mult ` ?XY" "upper (X * Y) \<in> ?mult ` ?XY"
    by (auto simp: set_of_eq lower_times upper_times min_def max_def split: if_splits)
  from connectedD_interval[OF conn this, of xy] assms
  obtain x y where "xy = x * y" "x \<in>\<^sub>i X" "y \<in>\<^sub>i Y" by (auto simp: set_of_eq)
  then show ?thesis ..
qed

lemma set_of_times: "set_of (X * Y) = {x * y | x y. x \<in> set_of X \<and> y \<in> set_of Y}"
  for X Y::"'a :: {linordered_ring, real_normed_algebra, linear_continuum_topology} interval"
  by (auto intro!: times_in_intervalI elim!: times_in_intervalE)

instance "interval" :: (linordered_idom) cancel_semigroup_add
proof qed (auto simp: interval_eq_iff)

lemma interval_mul_commute: "A * B = B * A" for A B:: "'a::linordered_idom interval"
  by (simp add: interval_eq_iff lower_times upper_times ac_simps)

lemma interval_times_zero_right[simp]: "A * 0 = 0" for A :: "'a::linordered_ring interval"
  by (simp add: interval_eq_iff lower_times upper_times ac_simps)

lemma interval_times_zero_left[simp]:
  "0 * A = 0" for A :: "'a::linordered_ring interval"
  by (simp add: interval_eq_iff lower_times upper_times ac_simps)

instantiation "interval" :: ("{preorder,one}") one
begin

lift_definition one_interval::"'a interval" is "(1, 1)" by auto
lemma lower_one[simp]: "lower 1 = 1"
  by transfer auto
lemma upper_one[simp]: "upper 1 = 1"
  by transfer auto
instance proof qed
end

instance interval :: ("{one, preorder, linordered_semiring}") power
proof qed

lemma set_of_one[simp]: "set_of (1::'a::{one, order} interval) = {1}"
  by (auto simp: set_of_eq)

instance "interval" ::
  ("{linordered_idom,linordered_ring, real_normed_algebra, linear_continuum_topology}") monoid_mult
  apply standard
  unfolding interval_eq_set_of_iff set_of_times
  subgoal
    by (auto simp: interval_eq_set_of_iff set_of_times; metis mult.assoc)
  by auto

lemma one_times_ivl_left[simp]: "1 * A = A" for A :: "'a::linordered_idom interval"
  by (simp add: interval_eq_iff lower_times upper_times ac_simps min_def max_def)

lemma one_times_ivl_right[simp]: "A * 1 = A" for A :: "'a::linordered_idom interval"
  by (metis interval_mul_commute one_times_ivl_left)

lemma set_of_power_mono: "a^n \<in> set_of (A^n)" if "a \<in> set_of A"
  for a :: "'a::linordered_idom"
  using that
  by (induction n) (auto intro!: times_in_intervalI)

lemma set_of_add_cong:
  "set_of (A + B) = set_of (A' + B')"
  if "set_of A = set_of A'" "set_of B = set_of B'"
  for A :: "'a::linordered_ab_group_add interval"
  unfolding set_of_plus that ..

lemma set_of_add_inc_left:
  "set_of (A + B) \<subseteq> set_of (A' + B)"
  if "set_of A \<subseteq> set_of A'"
  for A :: "'a::linordered_ab_group_add interval"
  unfolding set_of_plus using that by (auto simp: set_plus_def)

lemma set_of_add_inc_right:
  "set_of (A + B) \<subseteq> set_of (A + B')"
  if "set_of B \<subseteq> set_of B'"
  for A :: "'a::linordered_ab_group_add interval"
  using set_of_add_inc_left[OF that]
  by (simp add: add.commute)

lemma set_of_add_inc:
  "set_of (A + B) \<subseteq> set_of (A' + B')"
  if "set_of A \<subseteq> set_of A'" "set_of B \<subseteq> set_of B'"
  for A :: "'a::linordered_ab_group_add interval"
  using set_of_add_inc_left[OF that(1)] set_of_add_inc_right[OF that(2)]
  by auto

lemma set_of_neg_inc:
  "set_of (-A) \<subseteq> set_of (-A')"
  if "set_of A \<subseteq> set_of A'"
  for A :: "'a::ordered_ab_group_add interval"
  using that
  unfolding set_of_uminus
  by auto

lemma set_of_sub_inc_left:
  "set_of (A - B) \<subseteq> set_of (A' - B)"
  if "set_of A \<subseteq> set_of A'"
  for A :: "'a::linordered_ab_group_add interval"
  using that
  unfolding set_of_minus
  by auto

lemma set_of_sub_inc_right:
  "set_of (A - B) \<subseteq> set_of (A - B')"
  if "set_of B \<subseteq> set_of B'"
  for A :: "'a::linordered_ab_group_add interval"
  using that
  unfolding set_of_minus
  by auto

lemma set_of_sub_inc:
  "set_of (A - B) \<subseteq> set_of (A' - B')"
  if "set_of A \<subseteq> set_of A'" "set_of B \<subseteq> set_of B'"
  for A :: "'a::linordered_idom interval"
  using set_of_sub_inc_left[OF that(1)] set_of_sub_inc_right[OF that(2)]
  by auto

lemma set_of_mul_inc_right:
  "set_of (A * B) \<subseteq> set_of (A * B')"
  if "set_of B \<subseteq> set_of B'"
  for A :: "'a::linordered_ring interval"
  using that
  apply transfer
  apply (clarsimp simp add: Let_def)
  apply (intro conjI)
         apply (metis linear min.coboundedI1 min.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
        apply (metis linear min.coboundedI1 min.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
       apply (metis linear min.coboundedI1 min.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
      apply (metis linear min.coboundedI1 min.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
     apply (metis linear max.coboundedI1 max.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
    apply (metis linear max.coboundedI1 max.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
   apply (metis linear max.coboundedI1 max.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
  apply (metis linear max.coboundedI1 max.coboundedI2 mult_left_mono mult_left_mono_neg order_trans)
  done

lemma set_of_distrib_left:
  "set_of (B * (A1 + A2)) \<subseteq> set_of (B * A1 + B * A2)"
  for A1 :: "'a::linordered_ring interval"
  apply transfer
  apply (clarsimp simp: Let_def distrib_left distrib_right)
  apply (intro conjI)
         apply (metis add_mono min.cobounded1 min.left_commute)
        apply (metis add_mono min.cobounded1 min.left_commute)
       apply (metis add_mono min.cobounded1 min.left_commute)
      apply (metis add_mono min.assoc min.cobounded2)
     apply (meson add_mono order.trans max.cobounded1 max.cobounded2)
    apply (meson add_mono order.trans max.cobounded1 max.cobounded2)
   apply (meson add_mono order.trans max.cobounded1 max.cobounded2)
  apply (meson add_mono order.trans max.cobounded1 max.cobounded2)
  done

lemma set_of_distrib_right:
  "set_of ((A1 + A2) * B) \<subseteq> set_of (A1 * B + A2 * B)"
  for A1 A2 B :: "'a::{linordered_ring, real_normed_algebra, linear_continuum_topology} interval"
  unfolding set_of_times set_of_plus set_plus_def
  apply clarsimp
  subgoal for b a1 a2
    apply (rule exI[where x="a1 * b"])
    apply (rule conjI)
    subgoal by force
    subgoal
      apply (rule exI[where x="a2 * b"])
      apply (rule conjI)
      subgoal by force
      subgoal by (simp add: algebra_simps)
      done
    done
  done

lemma set_of_mul_inc_left:
  "set_of (A * B) \<subseteq> set_of (A' * B)"
  if "set_of A \<subseteq> set_of A'"
  for A :: "'a::{linordered_ring, real_normed_algebra, linear_continuum_topology} interval"
  using that
  unfolding set_of_times
  by auto

lemma set_of_mul_inc:
  "set_of (A * B) \<subseteq> set_of (A' * B')"
  if "set_of A \<subseteq> set_of A'" "set_of B \<subseteq> set_of B'"
  for A :: "'a::{linordered_ring, real_normed_algebra, linear_continuum_topology} interval"
  using that unfolding set_of_times by auto

lemma set_of_pow_inc:
  "set_of (A^n) \<subseteq> set_of (A'^n)"
  if "set_of A \<subseteq> set_of A'"
  for A :: "'a::{linordered_idom, real_normed_algebra, linear_continuum_topology} interval"
  using that
  by (induction n, simp_all add: set_of_mul_inc)

lemma set_of_distrib_right_left:
  "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * B1 + A1 * B2 + A2 * B1 + A2 * B2)"
  for A1 :: "'a::{linordered_idom, real_normed_algebra, linear_continuum_topology} interval"
proof-
  have "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * (B1 + B2) + A2 * (B1 + B2))"
    by (rule set_of_distrib_right)
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + A2 * (B1 + B2))"
    by (rule set_of_add_inc_left[OF set_of_distrib_left])
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + (A2 * B1 + A2 * B2))"
    by (rule set_of_add_inc_right[OF set_of_distrib_left])
  finally show ?thesis
    by (simp add: add.assoc)
qed

lemma mult_bounds_enclose_zero1:
  "min (la * lb) (min (la * ub) (min (lb * ua) (ua * ub))) \<le> 0"
  "0 \<le> max (la * lb) (max (la * ub) (max (lb * ua) (ua * ub)))"
  if "la \<le> 0" "0 \<le> ua"
  for la lb ua ub:: "'a::linordered_idom"
  subgoal by (metis (no_types, hide_lams) that eq_iff min_le_iff_disj mult_zero_left mult_zero_right
        zero_le_mult_iff)
  subgoal by (metis that le_max_iff_disj mult_zero_right order_refl zero_le_mult_iff)
  done

lemma mult_bounds_enclose_zero2:
  "min (la * lb) (min (la * ub) (min (lb * ua) (ua * ub))) \<le> 0"
  "0 \<le> max (la * lb) (max (la * ub) (max (lb * ua) (ua * ub)))"
  if "lb \<le> 0" "0 \<le> ub"
  for la lb ua ub:: "'a::linordered_idom"
  using mult_bounds_enclose_zero1[OF that, of la ua]
  by (simp_all add: ac_simps)

lemma set_of_mul_contains_zero:
  "0 \<in> set_of (A * B)"
  if "0 \<in> set_of A \<or> 0 \<in> set_of B"
  for A :: "'a::linordered_idom interval"
  using that
  by (auto simp: set_of_eq lower_times upper_times algebra_simps mult_le_0_iff
      mult_bounds_enclose_zero1 mult_bounds_enclose_zero2)

instance "interval" :: (linordered_semiring) mult_zero
  apply standard
  subgoal by transfer auto
  subgoal by transfer auto
  done

lift_definition min_interval::"'a::linorder interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval" is
  "\<lambda>(l1, u1). \<lambda>(l2, u2). (min l1 l2, min u1 u2)"
  by (auto simp: min_def)
lemma lower_min_interval[simp]: "lower (min_interval x y) = min (lower x) (lower y)"
  by transfer auto
lemma upper_min_interval[simp]: "upper (min_interval x y) = min (upper x) (upper y)"
  by transfer auto

lemma min_intervalI:
  "a \<in>\<^sub>i A \<Longrightarrow> b \<in>\<^sub>i B \<Longrightarrow> min a b \<in>\<^sub>i min_interval A B"
  by (auto simp: set_of_eq min_def)

lift_definition max_interval::"'a::linorder interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval" is
  "\<lambda>(l1, u1). \<lambda>(l2, u2). (max l1 l2, max u1 u2)"
  by (auto simp: max_def)
lemma lower_max_interval[simp]: "lower (max_interval x y) = max (lower x) (lower y)"
  by transfer auto
lemma upper_max_interval[simp]: "upper (max_interval x y) = max (upper x) (upper y)"
  by transfer auto

lemma max_intervalI:
  "a \<in>\<^sub>i A \<Longrightarrow> b \<in>\<^sub>i B \<Longrightarrow> max a b \<in>\<^sub>i max_interval A B"
  by (auto simp: set_of_eq max_def)

lift_definition abs_interval::"'a::linordered_idom interval \<Rightarrow> 'a interval" is
  "(\<lambda>(l,u). (if l < 0 \<and> 0 < u then 0 else min \<bar>l\<bar> \<bar>u\<bar>, max \<bar>l\<bar> \<bar>u\<bar>))"
  by auto

lemma lower_abs_interval[simp]:
  "lower (abs_interval x) = (if lower x < 0 \<and> 0 < upper x then 0 else min \<bar>lower x\<bar> \<bar>upper x\<bar>)"
  by transfer auto
lemma upper_abs_interval[simp]: "upper (abs_interval x) = max \<bar>lower x\<bar> \<bar>upper x\<bar>"
  by transfer auto

lemma in_abs_intervalI1:
  "lx < 0 \<Longrightarrow> 0 < ux \<Longrightarrow> 0 \<le> xa \<Longrightarrow> xa \<le> max (- lx) (ux) \<Longrightarrow> xa \<in> abs ` {lx..ux}"
  for xa::"'a::linordered_idom"
  by (metis abs_minus_cancel abs_of_nonneg atLeastAtMost_iff image_eqI le_less le_max_iff_disj
      le_minus_iff neg_le_0_iff_le order_trans)

lemma in_abs_intervalI2:
  "min (\<bar>lx\<bar>) \<bar>ux\<bar> \<le> xa \<Longrightarrow> xa \<le> max \<bar>lx\<bar> \<bar>ux\<bar> \<Longrightarrow> lx \<le> ux \<Longrightarrow> 0 \<le> lx \<or> ux \<le> 0 \<Longrightarrow>
    xa \<in> abs ` {lx..ux}"
  for xa::"'a::linordered_idom"
  by (force intro: image_eqI[where x="-xa"] image_eqI[where x="xa"])

lemma set_of_abs_interval: "set_of (abs_interval x) = abs ` set_of x"
  by (auto simp: set_of_eq not_less intro: in_abs_intervalI1 in_abs_intervalI2 cong del: image_cong_simp)

fun split_domain :: "('a::preorder interval \<Rightarrow> 'a interval list) \<Rightarrow> 'a interval list \<Rightarrow> 'a interval list list"
  where "split_domain split [] = [[]]"
  | "split_domain split (I#Is) = (
         let S = split I;
             D = split_domain split Is
         in concat (map (\<lambda>d. map (\<lambda>s. s # d) S) D)
       )"

context notes [[typedef_overloaded]] begin
lift_definition(code_dt) split_interval::"'a::linorder interval \<Rightarrow> 'a \<Rightarrow> ('a interval \<times> 'a interval)"
  is "\<lambda>(l, u) x. ((min l x, max l x), (min u x, max u x))"
  by (auto simp: min_def)
end

lemma split_domain_nonempty:
  assumes "\<And>I. split I \<noteq> []"
  shows "split_domain split I \<noteq> []"
  using last_in_set assms
  by (induction I, auto)

lemma lower_split_interval1: "lower (fst (split_interval X m)) = min (lower X) m"
  and lower_split_interval2: "lower (snd (split_interval X m)) = min (upper X) m"
  and upper_split_interval1: "upper (fst (split_interval X m)) = max (lower X) m"
  and upper_split_interval2: "upper (snd (split_interval X m)) = max (upper X) m"
  subgoal by transfer auto
  subgoal by transfer (auto simp: min.commute)
  subgoal by transfer (auto simp: )
  subgoal by transfer (auto simp: )
  done

lemma split_intervalD: "split_interval X x = (A, B) \<Longrightarrow> set_of X \<subseteq> set_of A \<union> set_of B"
  unfolding set_of_eq
  by transfer (auto simp: min_def max_def split: if_splits)

instantiation interval :: ("{topological_space, preorder}") topological_space
begin

definition open_interval_def[code del]: "open (X::'a interval set) =
  (\<forall>x\<in>X.
      \<exists>A B.
         open A \<and>
         open B \<and>
         lower x \<in> A \<and> upper x \<in> B \<and> Interval ` (A \<times> B) \<subseteq> X)"

instance
proof
  show "open (UNIV :: ('a interval) set)"
    unfolding open_interval_def by auto
next
  fix S T :: "('a interval) set"
  assume "open S" "open T"
  show "open (S \<inter> T)"
    unfolding open_interval_def
  proof (safe)
    fix x assume "x \<in> S" "x \<in> T"
    from \<open>x \<in> S\<close> \<open>open S\<close> obtain Sl Su where S:
      "open Sl" "open Su" "lower x \<in> Sl" "upper x \<in> Su" "Interval ` (Sl \<times> Su) \<subseteq> S"
      by (auto simp: open_interval_def)
    from \<open>x \<in> T\<close> \<open>open T\<close> obtain Tl Tu where T:
      "open Tl" "open Tu" "lower x \<in> Tl" "upper x \<in> Tu" "Interval ` (Tl \<times> Tu) \<subseteq> T"
      by (auto simp: open_interval_def)

    let ?L = "Sl \<inter> Tl" and ?U = "Su \<inter> Tu" 
    have "open ?L \<and> open ?U \<and> lower x \<in> ?L \<and> upper x \<in> ?U \<and> Interval ` (?L \<times> ?U) \<subseteq> S \<inter> T"
      using S T by (auto simp add: open_Int)
    then show "\<exists>A B. open A \<and> open B \<and> lower x \<in> A \<and> upper x \<in> B \<and> Interval ` (A \<times> B) \<subseteq> S \<inter> T"
      by fast
  qed
qed (unfold open_interval_def, fast)

end


subsection \<open>Quickcheck\<close>

lift_definition Ivl::"'a \<Rightarrow> 'a::preorder \<Rightarrow> 'a interval" is "\<lambda>a b. (min a b, b)"
  by (auto simp: min_def)

instantiation interval :: ("{exhaustive,preorder}") exhaustive
begin

definition exhaustive_interval::"('a interval \<Rightarrow> (bool \<times> term list) option)
     \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
  where
    "exhaustive_interval f d =
    Quickcheck_Exhaustive.exhaustive (\<lambda>x. Quickcheck_Exhaustive.exhaustive (\<lambda>y. f (Ivl x y)) d) d"

instance ..

end

context
  includes term_syntax
begin

definition [code_unfold]:
  "valtermify_interval x y = Code_Evaluation.valtermify (Ivl::'a::{preorder,typerep}\<Rightarrow>_) {\<cdot>} x {\<cdot>} y"

end

instantiation interval :: ("{full_exhaustive,preorder,typerep}") full_exhaustive
begin

definition full_exhaustive_interval::
  "('a interval \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
     \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option" where
  "full_exhaustive_interval f d =
    Quickcheck_Exhaustive.full_exhaustive
      (\<lambda>x. Quickcheck_Exhaustive.full_exhaustive (\<lambda>y. f (valtermify_interval x y)) d) d"

instance ..

end

instantiation interval :: ("{random,preorder,typerep}") random
begin

definition random_interval ::
  "natural
  \<Rightarrow> natural \<times> natural
     \<Rightarrow> ('a interval \<times> (unit \<Rightarrow> term)) \<times> natural \<times> natural" where
  "random_interval i =
  scomp (Quickcheck_Random.random i)
    (\<lambda>man. scomp (Quickcheck_Random.random i) (\<lambda>exp. Pair (valtermify_interval man exp)))"

instance ..

end

lifting_update interval.lifting
lifting_forget interval.lifting

end
