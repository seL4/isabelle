(* Author: Johannes Hoelzl, TU Muenchen *)

header {* A type for positive real numbers with infinity *}

theory Positive_Infinite_Real
  imports Complex_Main Nat_Bijection Multivariate_Analysis
begin

lemma (in complete_lattice) Sup_start:
  assumes *: "\<And>x. f x \<le> f 0"
  shows "(SUP n. f n) = f 0"
proof (rule antisym)
  show "f 0 \<le> (SUP n. f n)" by (rule le_SUPI) auto
  show "(SUP n. f n) \<le> f 0" by (rule SUP_leI[OF *])
qed

lemma (in complete_lattice) Inf_start:
  assumes *: "\<And>x. f 0 \<le> f x"
  shows "(INF n. f n) = f 0"
proof (rule antisym)
  show "(INF n. f n) \<le> f 0" by (rule INF_leI) simp
  show "f 0 \<le> (INF n. f n)" by (rule le_INFI[OF *])
qed

lemma (in complete_lattice) Sup_mono_offset:
  fixes f :: "'b :: {ordered_ab_semigroup_add,monoid_add} \<Rightarrow> 'a"
  assumes *: "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y" and "0 \<le> k"
  shows "(SUP n . f (k + n)) = (SUP n. f n)"
proof (rule antisym)
  show "(SUP n. f (k + n)) \<le> (SUP n. f n)"
    by (auto intro!: Sup_mono simp: SUPR_def)
  { fix n :: 'b
    have "0 + n \<le> k + n" using `0 \<le> k` by (rule add_right_mono)
    with * have "f n \<le> f (k + n)" by simp }
  thus "(SUP n. f n) \<le> (SUP n. f (k + n))"
    by (auto intro!: Sup_mono exI simp: SUPR_def)
qed

lemma (in complete_lattice) Sup_mono_offset_Suc:
  assumes *: "\<And>x. f x \<le> f (Suc x)"
  shows "(SUP n . f (Suc n)) = (SUP n. f n)"
  unfolding Suc_eq_plus1
  apply (subst add_commute)
  apply (rule Sup_mono_offset)
  by (auto intro!: order.lift_Suc_mono_le[of "op \<le>" "op <" f, OF _ *]) default

lemma (in complete_lattice) Inf_mono_offset:
  fixes f :: "'b :: {ordered_ab_semigroup_add,monoid_add} \<Rightarrow> 'a"
  assumes *: "\<And>x y. x \<le> y \<Longrightarrow> f y \<le> f x" and "0 \<le> k"
  shows "(INF n . f (k + n)) = (INF n. f n)"
proof (rule antisym)
  show "(INF n. f n) \<le> (INF n. f (k + n))"
    by (auto intro!: Inf_mono simp: INFI_def)
  { fix n :: 'b
    have "0 + n \<le> k + n" using `0 \<le> k` by (rule add_right_mono)
    with * have "f (k + n) \<le> f n" by simp }
  thus "(INF n. f (k + n)) \<le> (INF n. f n)"
    by (auto intro!: Inf_mono exI simp: INFI_def)
qed

lemma (in complete_lattice) isotone_converge:
  fixes f :: "nat \<Rightarrow> 'a" assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y "
  shows "(INF n. SUP m. f (n + m)) = (SUP n. INF m. f (n + m))"
proof -
  have "\<And>n. (SUP m. f (n + m)) = (SUP n. f n)"
    apply (rule Sup_mono_offset)
    apply (rule assms)
    by simp_all
  moreover
  { fix n have "(INF m. f (n + m)) = f n"
      using Inf_start[of "\<lambda>m. f (n + m)"] assms by simp }
  ultimately show ?thesis by simp
qed

lemma (in complete_lattice) antitone_converges:
  fixes f :: "nat \<Rightarrow> 'a" assumes "\<And>x y. x \<le> y \<Longrightarrow> f y \<le> f x"
  shows "(INF n. SUP m. f (n + m)) = (SUP n. INF m. f (n + m))"
proof -
  have "\<And>n. (INF m. f (n + m)) = (INF n. f n)"
    apply (rule Inf_mono_offset)
    apply (rule assms)
    by simp_all
  moreover
  { fix n have "(SUP m. f (n + m)) = f n"
      using Sup_start[of "\<lambda>m. f (n + m)"] assms by simp }
  ultimately show ?thesis by simp
qed

text {*

We introduce the the positive real numbers as needed for measure theory.

*}

typedef pinfreal = "(Some ` {0::real..}) \<union> {None}"
  by (rule exI[of _ None]) simp

subsection "Introduce @{typ pinfreal} similar to a datatype"

definition "Real x = Abs_pinfreal (Some (sup 0 x))"
definition "\<omega> = Abs_pinfreal None"

definition "pinfreal_case f i x = (if x = \<omega> then i else f (THE r. 0 \<le> r \<and> x = Real r))"

definition "of_pinfreal = pinfreal_case (\<lambda>x. x) 0"

defs (overloaded)
  real_of_pinfreal_def [code_unfold]: "real == of_pinfreal"

lemma pinfreal_Some[simp]: "0 \<le> x \<Longrightarrow> Some x \<in> pinfreal"
  unfolding pinfreal_def by simp

lemma pinfreal_Some_sup[simp]: "Some (sup 0 x) \<in> pinfreal"
  by (simp add: sup_ge1)

lemma pinfreal_None[simp]: "None \<in> pinfreal"
  unfolding pinfreal_def by simp

lemma Real_inj[simp]:
  assumes  "0 \<le> x" and "0 \<le> y"
  shows "Real x = Real y \<longleftrightarrow> x = y"
  unfolding Real_def assms[THEN sup_absorb2]
  using assms by (simp add: Abs_pinfreal_inject)

lemma Real_neq_\<omega>[simp]:
  "Real x = \<omega> \<longleftrightarrow> False"
  "\<omega> = Real x \<longleftrightarrow> False"
  by (simp_all add: Abs_pinfreal_inject \<omega>_def Real_def)

lemma Real_neg: "x < 0 \<Longrightarrow> Real x = Real 0"
  unfolding Real_def by (auto simp add: Abs_pinfreal_inject intro!: sup_absorb1)

lemma pinfreal_cases[case_names preal infinite, cases type: pinfreal]:
  assumes preal: "\<And>r. x = Real r \<Longrightarrow> 0 \<le> r \<Longrightarrow> P" and inf: "x = \<omega> \<Longrightarrow> P"
  shows P
proof (cases x rule: pinfreal.Abs_pinfreal_cases)
  case (Abs_pinfreal y)
  hence "y = None \<or> (\<exists>x \<ge> 0. y = Some x)"
    unfolding pinfreal_def by auto
  thus P
  proof (rule disjE)
    assume "\<exists>x\<ge>0. y = Some x" then guess x ..
    thus P by (simp add: preal[of x] Real_def Abs_pinfreal(1) sup_absorb2)
  qed (simp add: \<omega>_def Abs_pinfreal(1) inf)
qed

lemma pinfreal_case_\<omega>[simp]: "pinfreal_case f i \<omega> = i"
  unfolding pinfreal_case_def by simp

lemma pinfreal_case_Real[simp]: "pinfreal_case f i (Real x) = (if 0 \<le> x then f x else f 0)"
proof (cases "0 \<le> x")
  case True thus ?thesis unfolding pinfreal_case_def by (auto intro: theI2)
next
  case False
  moreover have "(THE r. 0 \<le> r \<and> Real 0 = Real r) = 0"
    by (auto intro!: the_equality)
  ultimately show ?thesis unfolding pinfreal_case_def by (simp add: Real_neg)
qed

lemma pinfreal_case_cancel[simp]: "pinfreal_case (\<lambda>c. i) i x = i"
  by (cases x) simp_all

lemma pinfreal_case_split:
  "P (pinfreal_case f i x) = ((x = \<omega> \<longrightarrow> P i) \<and> (\<forall>r\<ge>0. x = Real r \<longrightarrow> P (f r)))"
  by (cases x) simp_all

lemma pinfreal_case_split_asm:
  "P (pinfreal_case f i x) = (\<not> (x = \<omega> \<and> \<not> P i \<or> (\<exists>r. r \<ge> 0 \<and> x = Real r \<and> \<not> P (f r))))"
  by (cases x) auto

lemma pinfreal_case_cong[cong]:
  assumes eq: "x = x'" "i = i'" and cong: "\<And>r. 0 \<le> r \<Longrightarrow> f r = f' r"
  shows "pinfreal_case f i x = pinfreal_case f' i' x'"
  unfolding eq using cong by (cases x') simp_all

lemma real_Real[simp]: "real (Real x) = (if 0 \<le> x then x else 0)"
  unfolding real_of_pinfreal_def of_pinfreal_def by simp

lemma Real_real_image:
  assumes "\<omega> \<notin> A" shows "Real ` real ` A = A"
proof safe
  fix x assume "x \<in> A"
  hence *: "x = Real (real x)"
    using `\<omega> \<notin> A` by (cases x) auto
  show "x \<in> Real ` real ` A"
    using `x \<in> A` by (subst *) (auto intro!: imageI)
next
  fix x assume "x \<in> A"
  thus "Real (real x) \<in> A"
    using `\<omega> \<notin> A` by (cases x) auto
qed

lemma real_pinfreal_nonneg[simp, intro]: "0 \<le> real (x :: pinfreal)"
  unfolding real_of_pinfreal_def of_pinfreal_def
  by (cases x) auto

lemma real_\<omega>[simp]: "real \<omega> = 0"
  unfolding real_of_pinfreal_def of_pinfreal_def by simp

lemma pinfreal_noteq_omega_Ex: "X \<noteq> \<omega> \<longleftrightarrow> (\<exists>r\<ge>0. X = Real r)" by (cases X) auto

subsection "@{typ pinfreal} is a monoid for addition"

instantiation pinfreal :: comm_monoid_add
begin

definition "0 = Real 0"
definition "x + y = pinfreal_case (\<lambda>r. pinfreal_case (\<lambda>p. Real (r + p)) \<omega> y) \<omega> x"

lemma pinfreal_plus[simp]:
  "Real r + Real p = (if 0 \<le> r then if 0 \<le> p then Real (r + p) else Real r else Real p)"
  "x + 0 = x"
  "0 + x = x"
  "x + \<omega> = \<omega>"
  "\<omega> + x = \<omega>"
  by (simp_all add: plus_pinfreal_def Real_neg zero_pinfreal_def split: pinfreal_case_split)

lemma \<omega>_neq_0[simp]:
  "\<omega> = 0 \<longleftrightarrow> False"
  "0 = \<omega> \<longleftrightarrow> False"
  by (simp_all add: zero_pinfreal_def)

lemma Real_eq_0[simp]:
  "Real r = 0 \<longleftrightarrow> r \<le> 0"
  "0 = Real r \<longleftrightarrow> r \<le> 0"
  by (auto simp add: Abs_pinfreal_inject zero_pinfreal_def Real_def sup_real_def)

lemma Real_0[simp]: "Real 0 = 0" by (simp add: zero_pinfreal_def)

instance
proof
  fix a :: pinfreal
  show "0 + a = a" by (cases a) simp_all

  fix b show "a + b = b + a"
    by (cases a, cases b) simp_all

  fix c show "a + b + c = a + (b + c)"
    by (cases a, cases b, cases c) simp_all
qed
end

lemma pinfreal_plus_eq_\<omega>[simp]: "(a :: pinfreal) + b = \<omega> \<longleftrightarrow> a = \<omega> \<or> b = \<omega>"
  by (cases a, cases b) auto

lemma pinfreal_add_cancel_left:
  "a + b = a + c \<longleftrightarrow> (a = \<omega> \<or> b = c)"
  by (cases a, cases b, cases c, simp_all, cases c, simp_all)

lemma pinfreal_add_cancel_right:
  "b + a = c + a \<longleftrightarrow> (a = \<omega> \<or> b = c)"
  by (cases a, cases b, cases c, simp_all, cases c, simp_all)

lemma Real_eq_Real:
  "Real a = Real b \<longleftrightarrow> (a = b \<or> (a \<le> 0 \<and> b \<le> 0))"
proof (cases "a \<le> 0 \<or> b \<le> 0")
  case False with Real_inj[of a b] show ?thesis by auto
next
  case True
  thus ?thesis
  proof
    assume "a \<le> 0"
    hence *: "Real a = 0" by simp
    show ?thesis using `a \<le> 0` unfolding * by auto
  next
    assume "b \<le> 0"
    hence *: "Real b = 0" by simp
    show ?thesis using `b \<le> 0` unfolding * by auto
  qed
qed

lemma real_pinfreal_0[simp]: "real (0 :: pinfreal) = 0"
  unfolding zero_pinfreal_def real_Real by simp

lemma real_of_pinfreal_eq_0: "real X = 0 \<longleftrightarrow> (X = 0 \<or> X = \<omega>)"
  by (cases X) auto

lemma real_of_pinfreal_eq: "real X = real Y \<longleftrightarrow>
    (X = Y \<or> (X = 0 \<and> Y = \<omega>) \<or> (Y = 0 \<and> X = \<omega>))"
  by (cases X, cases Y) (auto simp add: real_of_pinfreal_eq_0)

lemma real_of_pinfreal_add: "real X + real Y =
    (if X = \<omega> then real Y else if Y = \<omega> then real X else real (X + Y))"
  by (auto simp: pinfreal_noteq_omega_Ex)

subsection "@{typ pinfreal} is a monoid for multiplication"

instantiation pinfreal :: comm_monoid_mult
begin

definition "1 = Real 1"
definition "x * y = (if x = 0 \<or> y = 0 then 0 else
  pinfreal_case (\<lambda>r. pinfreal_case (\<lambda>p. Real (r * p)) \<omega> y) \<omega> x)"

lemma pinfreal_times[simp]:
  "Real r * Real p = (if 0 \<le> r \<and> 0 \<le> p then Real (r * p) else 0)"
  "\<omega> * x = (if x = 0 then 0 else \<omega>)"
  "x * \<omega> = (if x = 0 then 0 else \<omega>)"
  "0 * x = 0"
  "x * 0 = 0"
  "1 = \<omega> \<longleftrightarrow> False"
  "\<omega> = 1 \<longleftrightarrow> False"
  by (auto simp add: times_pinfreal_def one_pinfreal_def)

lemma pinfreal_one_mult[simp]:
  "Real x + 1 = (if 0 \<le> x then Real (x + 1) else 1)"
  "1 + Real x = (if 0 \<le> x then Real (1 + x) else 1)"
  unfolding one_pinfreal_def by simp_all

instance
proof
  fix a :: pinfreal show "1 * a = a"
    by (cases a) (simp_all add: one_pinfreal_def)

  fix b show "a * b = b * a"
    by (cases a, cases b) (simp_all add: mult_nonneg_nonneg)

  fix c show "a * b * c = a * (b * c)"
    apply (cases a, cases b, cases c)
    apply (simp_all add: mult_nonneg_nonneg not_le mult_pos_pos)
    apply (cases b, cases c)
    apply (simp_all add: mult_nonneg_nonneg not_le mult_pos_pos)
    done
qed
end

lemma pinfreal_mult_cancel_left:
  "a * b = a * c \<longleftrightarrow> (a = 0 \<or> b = c \<or> (a = \<omega> \<and> b \<noteq> 0 \<and> c \<noteq> 0))"
  by (cases a, cases b, cases c, auto simp: Real_eq_Real mult_le_0_iff, cases c, auto)

lemma pinfreal_mult_cancel_right:
  "b * a = c * a \<longleftrightarrow> (a = 0 \<or> b = c \<or> (a = \<omega> \<and> b \<noteq> 0 \<and> c \<noteq> 0))"
  by (cases a, cases b, cases c, auto simp: Real_eq_Real mult_le_0_iff, cases c, auto)

lemma Real_1[simp]: "Real 1 = 1" by (simp add: one_pinfreal_def)

lemma real_pinfreal_1[simp]: "real (1 :: pinfreal) = 1"
  unfolding one_pinfreal_def real_Real by simp

lemma real_of_pinfreal_mult: "real X * real Y = real (X * Y :: pinfreal)"
  by (cases X, cases Y) (auto simp: zero_le_mult_iff)

subsection "@{typ pinfreal} is a linear order"

instantiation pinfreal :: linorder
begin

definition "x < y \<longleftrightarrow> pinfreal_case (\<lambda>i. pinfreal_case (\<lambda>j. i < j) True y) False x"
definition "x \<le> y \<longleftrightarrow> pinfreal_case (\<lambda>j. pinfreal_case (\<lambda>i. i \<le> j) False x) True y"

lemma pinfreal_less[simp]:
  "Real r < \<omega>"
  "Real r < Real p \<longleftrightarrow> (if 0 \<le> r \<and> 0 \<le> p then r < p else 0 < p)"
  "\<omega> < x \<longleftrightarrow> False"
  "0 < \<omega>"
  "0 < Real r \<longleftrightarrow> 0 < r"
  "x < 0 \<longleftrightarrow> False"
  "0 < (1::pinfreal)"
  by (simp_all add: less_pinfreal_def zero_pinfreal_def one_pinfreal_def del: Real_0 Real_1)

lemma pinfreal_less_eq[simp]:
  "x \<le> \<omega>"
  "Real r \<le> Real p \<longleftrightarrow> (if 0 \<le> r \<and> 0 \<le> p then r \<le> p else r \<le> 0)"
  "0 \<le> x"
  by (simp_all add: less_eq_pinfreal_def zero_pinfreal_def del: Real_0)

lemma pinfreal_\<omega>_less_eq[simp]:
  "\<omega> \<le> x \<longleftrightarrow> x = \<omega>"
  by (cases x) (simp_all add: not_le less_eq_pinfreal_def)

lemma pinfreal_less_eq_zero[simp]:
  "(x::pinfreal) \<le> 0 \<longleftrightarrow> x = 0"
  by (cases x) (simp_all add: zero_pinfreal_def del: Real_0)

instance
proof
  fix x :: pinfreal
  show "x \<le> x" by (cases x) simp_all
  fix y
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x, cases y) auto
  show "x \<le> y \<or> y \<le> x "
    by (cases x, cases y) auto
  { assume "x \<le> y" "y \<le> x" thus "x = y"
      by (cases x, cases y) auto }
  { fix z assume "x \<le> y" "y \<le> z"
    thus "x \<le> z" by (cases x, cases y, cases z) auto }
qed
end

lemma pinfreal_zero_lessI[intro]:
  "(a :: pinfreal) \<noteq> 0 \<Longrightarrow> 0 < a"
  by (cases a) auto

lemma pinfreal_less_omegaI[intro, simp]:
  "a \<noteq> \<omega> \<Longrightarrow> a < \<omega>"
  by (cases a) auto

lemma pinfreal_plus_eq_0[simp]: "(a :: pinfreal) + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (cases a, cases b) auto

lemma pinfreal_le_add1[simp, intro]: "n \<le> n + (m::pinfreal)"
  by (cases n, cases m) simp_all

lemma pinfreal_le_add2: "(n::pinfreal) + m \<le> k \<Longrightarrow> m \<le> k"
  by (cases n, cases m, cases k) simp_all

lemma pinfreal_le_add3: "(n::pinfreal) + m \<le> k \<Longrightarrow> n \<le> k"
  by (cases n, cases m, cases k) simp_all

lemma pinfreal_less_\<omega>: "x < \<omega> \<longleftrightarrow> x \<noteq> \<omega>"
  by (cases x) auto

lemma pinfreal_0_less_mult_iff[simp]:
  fixes x y :: pinfreal shows "0 < x * y \<longleftrightarrow> 0 < x \<and> 0 < y"
  by (cases x, cases y) (auto simp: zero_less_mult_iff)

subsection {* @{text "x - y"} on @{typ pinfreal} *}

instantiation pinfreal :: minus
begin
definition "x - y = (if y < x then THE d. x = y + d else 0 :: pinfreal)"

lemma minus_pinfreal_eq:
  "(x - y = (z :: pinfreal)) \<longleftrightarrow> (if y < x then x = y + z else z = 0)"
  (is "?diff \<longleftrightarrow> ?if")
proof
  assume ?diff
  thus ?if
  proof (cases "y < x")
    case True
    then obtain p where p: "y = Real p" "0 \<le> p" by (cases y) auto

    show ?thesis unfolding `?diff`[symmetric] if_P[OF True] minus_pinfreal_def
    proof (rule theI2[where Q="\<lambda>d. x = y + d"])
      show "x = y + pinfreal_case (\<lambda>r. Real (r - real y)) \<omega> x" (is "x = y + ?d")
        using `y < x` p by (cases x) simp_all

      fix d assume "x = y + d"
      thus "d = ?d" using `y < x` p by (cases d, cases x) simp_all
    qed simp
  qed (simp add: minus_pinfreal_def)
next
  assume ?if
  thus ?diff
  proof (cases "y < x")
    case True
    then obtain p where p: "y = Real p" "0 \<le> p" by (cases y) auto

    from True `?if` have "x = y + z" by simp

    show ?thesis unfolding minus_pinfreal_def if_P[OF True] unfolding `x = y + z`
    proof (rule the_equality)
      fix d :: pinfreal assume "y + z = y + d"
      thus "d = z" using `y < x` p
        by (cases d, cases z) simp_all
    qed simp
  qed (simp add: minus_pinfreal_def)
qed

instance ..
end

lemma pinfreal_minus[simp]:
  "Real r - Real p = (if 0 \<le> r \<and> p < r then if 0 \<le> p then Real (r - p) else Real r else 0)"
  "(A::pinfreal) - A = 0"
  "\<omega> - Real r = \<omega>"
  "Real r - \<omega> = 0"
  "A - 0 = A"
  "0 - A = 0"
  by (auto simp: minus_pinfreal_eq not_less)

lemma pinfreal_le_epsilon:
  fixes x y :: pinfreal
  assumes "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (cases y)
  case (preal r)
  then obtain p where x: "x = Real p" "0 \<le> p"
    using assms[of 1] by (cases x) auto
  { fix e have "0 < e \<Longrightarrow> p \<le> r + e"
      using assms[of "Real e"] preal x by auto }
  hence "p \<le> r" by (rule field_le_epsilon)
  thus ?thesis using preal x by auto
qed simp

instance pinfreal :: "{ordered_comm_semiring, comm_semiring_1}"
proof
  show "0 \<noteq> (1::pinfreal)" unfolding zero_pinfreal_def one_pinfreal_def
    by (simp del: Real_1 Real_0)

  fix a :: pinfreal
  show "0 * a = 0" "a * 0 = 0" by simp_all

  fix b c :: pinfreal
  show "(a + b) * c = a * c + b * c"
    by (cases c, cases a, cases b)
       (auto intro!: arg_cong[where f=Real] simp: field_simps not_le mult_le_0_iff mult_less_0_iff)

  { assume "a \<le> b" thus "c + a \<le> c + b"
     by (cases c, cases a, cases b) auto }

  assume "a \<le> b" "0 \<le> c"
  thus "c * a \<le> c * b"
    apply (cases c, cases a, cases b)
    by (auto simp: mult_left_mono mult_le_0_iff mult_less_0_iff not_le)
qed

lemma mult_\<omega>[simp]: "x * y = \<omega> \<longleftrightarrow> (x = \<omega> \<or> y = \<omega>) \<and> x \<noteq> 0 \<and> y \<noteq> 0"
  by (cases x, cases y) auto

lemma \<omega>_mult[simp]: "(\<omega> = x * y) = ((x = \<omega> \<or> y = \<omega>) \<and> x \<noteq> 0 \<and> y \<noteq> 0)"
  by (cases x, cases y) auto

lemma pinfreal_mult_0[simp]: "x * y = 0 \<longleftrightarrow> x = 0 \<or> (y::pinfreal) = 0"
  by (cases x, cases y) (auto simp: mult_le_0_iff)

lemma pinfreal_mult_cancel:
  fixes x y z :: pinfreal
  assumes "y \<le> z"
  shows "x * y \<le> x * z"
  using assms
  by (cases x, cases y, cases z)
     (auto simp: mult_le_cancel_left mult_le_0_iff mult_less_0_iff not_le)

lemma Real_power[simp]:
  "Real x ^ n = (if x \<le> 0 then (if n = 0 then 1 else 0) else Real (x ^ n))"
  by (induct n) auto

lemma Real_power_\<omega>[simp]:
  "\<omega> ^ n = (if n = 0 then 1 else \<omega>)"
  by (induct n) auto

lemma pinfreal_of_nat[simp]: "of_nat m = Real (real m)"
  by (induct m) (auto simp: real_of_nat_Suc one_pinfreal_def simp del: Real_1)

lemma real_of_pinfreal_mono:
  fixes a b :: pinfreal
  assumes "b \<noteq> \<omega>" "a \<le> b"
  shows "real a \<le> real b"
using assms by (cases b, cases a) auto

instance pinfreal :: "semiring_char_0"
proof
  fix m n
  show "inj (of_nat::nat\<Rightarrow>pinfreal)" by (auto intro!: inj_onI)
qed

subsection "@{typ pinfreal} is a complete lattice"

instantiation pinfreal :: lattice
begin
definition [simp]: "sup x y = (max x y :: pinfreal)"
definition [simp]: "inf x y = (min x y :: pinfreal)"
instance proof qed simp_all
end

instantiation pinfreal :: complete_lattice
begin

definition "bot = Real 0"
definition "top = \<omega>"

definition "Sup S = (LEAST z. \<forall>x\<in>S. x \<le> z :: pinfreal)"
definition "Inf S = (GREATEST z. \<forall>x\<in>S. z \<le> x :: pinfreal)"

lemma pinfreal_complete_Sup:
  fixes S :: "pinfreal set" assumes "S \<noteq> {}"
  shows "\<exists>x. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z)"
proof (cases "\<exists>x\<ge>0. \<forall>a\<in>S. a \<le> Real x")
  case False
  hence *: "\<And>x. x\<ge>0 \<Longrightarrow> \<exists>a\<in>S. \<not>a \<le> Real x" by simp
  show ?thesis
  proof (safe intro!: exI[of _ \<omega>])
    fix y assume **: "\<forall>z\<in>S. z \<le> y"
    show "\<omega> \<le> y" unfolding pinfreal_\<omega>_less_eq
    proof (rule ccontr)
      assume "y \<noteq> \<omega>"
      then obtain x where [simp]: "y = Real x" and "0 \<le> x" by (cases y) auto
      from *[OF `0 \<le> x`] show False using ** by auto
    qed
  qed simp
next
  case True then obtain y where y: "\<And>a. a\<in>S \<Longrightarrow> a \<le> Real y" and "0 \<le> y" by auto
  from y[of \<omega>] have "\<omega> \<notin> S" by auto

  with `S \<noteq> {}` obtain x where "x \<in> S" and "x \<noteq> \<omega>" by auto

  have bound: "\<forall>x\<in>real ` S. x \<le> y"
  proof
    fix z assume "z \<in> real ` S" then guess a ..
    with y[of a] `\<omega> \<notin> S` `0 \<le> y` show "z \<le> y" by (cases a) auto
  qed
  with reals_complete2[of "real ` S"] `x \<in> S`
  obtain s where s: "\<forall>y\<in>S. real y \<le> s" "\<forall>z. ((\<forall>y\<in>S. real y \<le> z) \<longrightarrow> s \<le> z)"
    by auto

  show ?thesis
  proof (safe intro!: exI[of _ "Real s"])
    fix z assume "z \<in> S" thus "z \<le> Real s"
      using s `\<omega> \<notin> S` by (cases z) auto
  next
    fix z assume *: "\<forall>y\<in>S. y \<le> z"
    show "Real s \<le> z"
    proof (cases z)
      case (preal u)
      { fix v assume "v \<in> S"
        hence "v \<le> Real u" using * preal by auto
        hence "real v \<le> u" using `\<omega> \<notin> S` `0 \<le> u` by (cases v) auto }
      hence "s \<le> u" using s(2) by auto
      thus "Real s \<le> z" using preal by simp
    qed simp
  qed
qed

lemma pinfreal_complete_Inf:
  fixes S :: "pinfreal set" assumes "S \<noteq> {}"
  shows "\<exists>x. (\<forall>y\<in>S. x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> x)"
proof (cases "S = {\<omega>}")
  case True thus ?thesis by (auto intro!: exI[of _ \<omega>])
next
  case False with `S \<noteq> {}` have "S - {\<omega>} \<noteq> {}" by auto
  hence not_empty: "\<exists>x. x \<in> uminus ` real ` (S - {\<omega>})" by auto
  have bounds: "\<exists>x. \<forall>y\<in>uminus ` real ` (S - {\<omega>}). y \<le> x" by (auto intro!: exI[of _ 0])
  from reals_complete2[OF not_empty bounds]
  obtain s where s: "\<And>y. y\<in>S - {\<omega>} \<Longrightarrow> - real y \<le> s" "\<forall>z. ((\<forall>y\<in>S - {\<omega>}. - real y \<le> z) \<longrightarrow> s \<le> z)"
    by auto

  show ?thesis
  proof (safe intro!: exI[of _ "Real (-s)"])
    fix z assume "z \<in> S"
    show "Real (-s) \<le> z"
    proof (cases z)
      case (preal r)
      with s `z \<in> S` have "z \<in> S - {\<omega>}" by simp
      hence "- r \<le> s" using preal s(1)[of z] by auto
      hence "- s \<le> r" by (subst neg_le_iff_le[symmetric]) simp
      thus ?thesis using preal by simp
    qed simp
  next
    fix z assume *: "\<forall>y\<in>S. z \<le> y"
    show "z \<le> Real (-s)"
    proof (cases z)
      case (preal u)
      { fix v assume "v \<in> S-{\<omega>}"
        hence "Real u \<le> v" using * preal by auto
        hence "- real v \<le> - u" using `0 \<le> u` `v \<in> S - {\<omega>}` by (cases v) auto }
      hence "u \<le> - s" using s(2) by (subst neg_le_iff_le[symmetric]) auto
      thus "z \<le> Real (-s)" using preal by simp
    next
      case infinite
      with * have "S = {\<omega>}" using `S \<noteq> {}` by auto
      with `S - {\<omega>} \<noteq> {}` show ?thesis by simp
    qed
  qed
qed

instance
proof
  fix x :: pinfreal and A

  show "bot \<le> x" by (cases x) (simp_all add: bot_pinfreal_def)
  show "x \<le> top" by (simp add: top_pinfreal_def)

  { assume "x \<in> A"
    with pinfreal_complete_Sup[of A]
    obtain s where s: "\<forall>y\<in>A. y \<le> s" "\<forall>z. (\<forall>y\<in>A. y \<le> z) \<longrightarrow> s \<le> z" by auto
    hence "x \<le> s" using `x \<in> A` by auto
    also have "... = Sup A" using s unfolding Sup_pinfreal_def
      by (auto intro!: Least_equality[symmetric])
    finally show "x \<le> Sup A" . }

  { assume "x \<in> A"
    with pinfreal_complete_Inf[of A]
    obtain i where i: "\<forall>y\<in>A. i \<le> y" "\<forall>z. (\<forall>y\<in>A. z \<le> y) \<longrightarrow> z \<le> i" by auto
    hence "Inf A = i" unfolding Inf_pinfreal_def
      by (auto intro!: Greatest_equality)
    also have "i \<le> x" using i `x \<in> A` by auto
    finally show "Inf A \<le> x" . }

  { assume *: "\<And>z. z \<in> A \<Longrightarrow> z \<le> x"
    show "Sup A \<le> x"
    proof (cases "A = {}")
      case True
      hence "Sup A = 0" unfolding Sup_pinfreal_def
        by (auto intro!: Least_equality)
      thus "Sup A \<le> x" by simp
    next
      case False
      with pinfreal_complete_Sup[of A]
      obtain s where s: "\<forall>y\<in>A. y \<le> s" "\<forall>z. (\<forall>y\<in>A. y \<le> z) \<longrightarrow> s \<le> z" by auto
      hence "Sup A = s"
        unfolding Sup_pinfreal_def by (auto intro!: Least_equality)
      also have "s \<le> x" using * s by auto
      finally show "Sup A \<le> x" .
    qed }

  { assume *: "\<And>z. z \<in> A \<Longrightarrow> x \<le> z"
    show "x \<le> Inf A"
    proof (cases "A = {}")
      case True
      hence "Inf A = \<omega>" unfolding Inf_pinfreal_def
        by (auto intro!: Greatest_equality)
      thus "x \<le> Inf A" by simp
    next
      case False
      with pinfreal_complete_Inf[of A]
      obtain i where i: "\<forall>y\<in>A. i \<le> y" "\<forall>z. (\<forall>y\<in>A. z \<le> y) \<longrightarrow> z \<le> i" by auto
      have "x \<le> i" using * i by auto
      also have "i = Inf A" using i
        unfolding Inf_pinfreal_def by (auto intro!: Greatest_equality[symmetric])
      finally show "x \<le> Inf A" .
    qed }
qed
end

lemma Inf_pinfreal_iff:
  fixes z :: pinfreal
  shows "(\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> (\<exists>x\<in>X. x<y) \<longleftrightarrow> Inf X < y"
  by (metis complete_lattice_class.Inf_greatest complete_lattice_class.Inf_lower less_le_not_le linear
            order_less_le_trans)

lemma Inf_greater:
  fixes z :: pinfreal assumes "Inf X < z"
  shows "\<exists>x \<in> X. x < z"
proof -
  have "X \<noteq> {}" using assms by (auto simp: Inf_empty top_pinfreal_def)
  with assms show ?thesis
    by (metis Inf_pinfreal_iff mem_def not_leE)
qed

lemma Inf_close:
  fixes e :: pinfreal assumes "Inf X \<noteq> \<omega>" "0 < e"
  shows "\<exists>x \<in> X. x < Inf X + e"
proof (rule Inf_greater)
  show "Inf X < Inf X + e" using assms
    by (cases "Inf X", cases e) auto
qed

lemma pinfreal_SUPI:
  fixes x :: pinfreal
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<le> x"
  assumes "\<And>y. (\<And>i. i \<in> A \<Longrightarrow> f i \<le> y) \<Longrightarrow> x \<le> y"
  shows "(SUP i:A. f i) = x"
  unfolding SUPR_def Sup_pinfreal_def
  using assms by (auto intro!: Least_equality)

lemma Sup_pinfreal_iff:
  fixes z :: pinfreal
  shows "(\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> (\<exists>x\<in>X. y<x) \<longleftrightarrow> y < Sup X"
  by (metis complete_lattice_class.Sup_least complete_lattice_class.Sup_upper less_le_not_le linear
            order_less_le_trans)

lemma Sup_lesser:
  fixes z :: pinfreal assumes "z < Sup X"
  shows "\<exists>x \<in> X. z < x"
proof -
  have "X \<noteq> {}" using assms by (auto simp: Sup_empty bot_pinfreal_def)
  with assms show ?thesis
    by (metis Sup_pinfreal_iff mem_def not_leE)
qed

lemma Sup_eq_\<omega>: "\<omega> \<in> S \<Longrightarrow> Sup S = \<omega>"
  unfolding Sup_pinfreal_def
  by (auto intro!: Least_equality)

lemma Sup_close:
  assumes "0 < e" and S: "Sup S \<noteq> \<omega>" "S \<noteq> {}"
  shows "\<exists>X\<in>S. Sup S < X + e"
proof cases
  assume "Sup S = 0"
  moreover obtain X where "X \<in> S" using `S \<noteq> {}` by auto
  ultimately show ?thesis using `0 < e` by (auto intro!: bexI[OF _ `X\<in>S`])
next
  assume "Sup S \<noteq> 0"
  have "\<exists>X\<in>S. Sup S - e < X"
  proof (rule Sup_lesser)
    show "Sup S - e < Sup S" using `0 < e` `Sup S \<noteq> 0` `Sup S \<noteq> \<omega>`
      by (cases e) (auto simp: pinfreal_noteq_omega_Ex)
  qed
  then guess X .. note X = this
  with `Sup S \<noteq> \<omega>` Sup_eq_\<omega> have "X \<noteq> \<omega>" by auto
  thus ?thesis using `Sup S \<noteq> \<omega>` X unfolding pinfreal_noteq_omega_Ex
    by (cases e) (auto intro!: bexI[OF _ `X\<in>S`] simp: split: split_if_asm)
qed

lemma Sup_\<omega>: "(SUP i::nat. Real (real i)) = \<omega>"
proof (rule pinfreal_SUPI)
  fix y assume *: "\<And>i::nat. i \<in> UNIV \<Longrightarrow> Real (real i) \<le> y"
  thus "\<omega> \<le> y"
  proof (cases y)
    case (preal r)
    then obtain k :: nat where "r < real k"
      using ex_less_of_nat by (auto simp: real_eq_of_nat)
    with *[of k] preal show ?thesis by auto
  qed simp
qed simp

subsubsection {* Equivalence between @{text "f ----> x"} and @{text SUP} on @{typ pinfreal} *}

lemma monoseq_monoI: "mono f \<Longrightarrow> monoseq f"
  unfolding mono_def monoseq_def by auto

lemma incseq_mono: "mono f \<longleftrightarrow> incseq f"
  unfolding mono_def incseq_def by auto

lemma SUP_eq_LIMSEQ:
  assumes "mono f" and "\<And>n. 0 \<le> f n" and "0 \<le> x"
  shows "(SUP n. Real (f n)) = Real x \<longleftrightarrow> f ----> x"
proof
  assume x: "(SUP n. Real (f n)) = Real x"
  { fix n
    have "Real (f n) \<le> Real x" using x[symmetric] by (auto intro: le_SUPI)
    hence "f n \<le> x" using assms by simp }
  show "f ----> x"
  proof (rule LIMSEQ_I)
    fix r :: real assume "0 < r"
    show "\<exists>no. \<forall>n\<ge>no. norm (f n - x) < r"
    proof (rule ccontr)
      assume *: "\<not> ?thesis"
      { fix N
        from * obtain n where "N \<le> n" "r \<le> x - f n"
          using `\<And>n. f n \<le> x` by (auto simp: not_less)
        hence "f N \<le> f n" using `mono f` by (auto dest: monoD)
        hence "f N \<le> x - r" using `r \<le> x - f n` by auto
        hence "Real (f N) \<le> Real (x - r)" and "r \<le> x" using `0 \<le> f N` by auto }
      hence "(SUP n. Real (f n)) \<le> Real (x - r)"
        and "Real (x - r) < Real x" using `0 < r` by (auto intro: SUP_leI)
      hence "(SUP n. Real (f n)) < Real x" by (rule le_less_trans)
      thus False using x by auto
    qed
  qed
next
  assume "f ----> x"
  show "(SUP n. Real (f n)) = Real x"
  proof (rule pinfreal_SUPI)
    fix n
    from incseq_le[of f x] `mono f` `f ----> x`
    show "Real (f n) \<le> Real x" using assms incseq_mono by auto
  next
    fix y assume *: "\<And>n. n\<in>UNIV \<Longrightarrow> Real (f n) \<le> y"
    show "Real x \<le> y"
    proof (cases y)
      case (preal r)
      with * have "\<exists>N. \<forall>n\<ge>N. f n \<le> r" using assms by fastsimp
      from LIMSEQ_le_const2[OF `f ----> x` this]
      show "Real x \<le> y" using `0 \<le> x` preal by auto
    qed simp
  qed
qed

lemma SUPR_bound:
  assumes "\<forall>N. f N \<le> x"
  shows "(SUP n. f n) \<le> x"
  using assms by (simp add: SUPR_def Sup_le_iff)

lemma pinfreal_less_eq_diff_eq_sum:
  fixes x y z :: pinfreal
  assumes "y \<le> x" and "x \<noteq> \<omega>"
  shows "z \<le> x - y \<longleftrightarrow> z + y \<le> x"
  using assms
  apply (cases z, cases y, cases x)
  by (simp_all add: field_simps minus_pinfreal_eq)

lemma Real_diff_less_omega: "Real r - x < \<omega>" by (cases x) auto

subsubsection {* Numbers on @{typ pinfreal} *}

instantiation pinfreal :: number
begin
definition [simp]: "number_of x = Real (number_of x)"
instance proof qed
end

subsubsection {* Division on @{typ pinfreal} *}

instantiation pinfreal :: inverse
begin

definition "inverse x = pinfreal_case (\<lambda>x. if x = 0 then \<omega> else Real (inverse x)) 0 x"
definition [simp]: "x / y = x * inverse (y :: pinfreal)"

instance proof qed
end

lemma pinfreal_inverse[simp]:
  "inverse 0 = \<omega>"
  "inverse (Real x) = (if x \<le> 0 then \<omega> else Real (inverse x))"
  "inverse \<omega> = 0"
  "inverse (1::pinfreal) = 1"
  "inverse (inverse x) = x"
  by (simp_all add: inverse_pinfreal_def one_pinfreal_def split: pinfreal_case_split del: Real_1)

lemma pinfreal_inverse_le_eq:
  assumes "x \<noteq> 0" "x \<noteq> \<omega>"
  shows "y \<le> z / x \<longleftrightarrow> x * y \<le> (z :: pinfreal)"
proof -
  from assms obtain r where r: "x = Real r" "0 < r" by (cases x) auto
  { fix p q :: real assume "0 \<le> p" "0 \<le> q"
    have "p \<le> q * inverse r \<longleftrightarrow> p \<le> q / r" by (simp add: divide_inverse)
    also have "... \<longleftrightarrow> p * r \<le> q" using `0 < r` by (auto simp: field_simps)
    finally have "p \<le> q * inverse r \<longleftrightarrow> p * r \<le> q" . }
  with r show ?thesis
    by (cases y, cases z, auto simp: zero_le_mult_iff field_simps)
qed

lemma inverse_antimono_strict:
  fixes x y :: pinfreal
  assumes "x < y" shows "inverse y < inverse x"
  using assms by (cases x, cases y) auto

lemma inverse_antimono:
  fixes x y :: pinfreal
  assumes "x \<le> y" shows "inverse y \<le> inverse x"
  using assms by (cases x, cases y) auto

lemma pinfreal_inverse_\<omega>_iff[simp]: "inverse x = \<omega> \<longleftrightarrow> x = 0"
  by (cases x) auto

subsection "Infinite sum over @{typ pinfreal}"

text {*

The infinite sum over @{typ pinfreal} has the nice property that it is always
defined.

*}

definition psuminf :: "(nat \<Rightarrow> pinfreal) \<Rightarrow> pinfreal" (binder "\<Sum>\<^isub>\<infinity>" 10) where
  "(\<Sum>\<^isub>\<infinity> x. f x) = (SUP n. \<Sum>i<n. f i)"

subsubsection {* Equivalence between @{text "\<Sum> n. f n"} and @{text "\<Sum>\<^isub>\<infinity> n. f n"} *}

lemma setsum_Real:
  assumes "\<forall>x\<in>A. 0 \<le> f x"
  shows "(\<Sum>x\<in>A. Real (f x)) = Real (\<Sum>x\<in>A. f x)"
proof (cases "finite A")
  case True
  thus ?thesis using assms
  proof induct case (insert x s)
    hence "0 \<le> setsum f s" apply-apply(rule setsum_nonneg) by auto
    thus ?case using insert by auto
  qed auto
qed simp

lemma setsum_Real':
  assumes "\<forall>x. 0 \<le> f x"
  shows "(\<Sum>x\<in>A. Real (f x)) = Real (\<Sum>x\<in>A. f x)"
  apply(rule setsum_Real) using assms by auto

lemma setsum_\<omega>:
  "(\<Sum>x\<in>P. f x) = \<omega> \<longleftrightarrow> (finite P \<and> (\<exists>i\<in>P. f i = \<omega>))"
proof safe
  assume *: "setsum f P = \<omega>"
  show "finite P"
  proof (rule ccontr) assume "infinite P" with * show False by auto qed
  show "\<exists>i\<in>P. f i = \<omega>"
  proof (rule ccontr)
    assume "\<not> ?thesis" hence "\<And>i. i\<in>P \<Longrightarrow> f i \<noteq> \<omega>" by auto
    from `finite P` this have "setsum f P \<noteq> \<omega>"
      by induct auto
    with * show False by auto
  qed
next
  fix i assume "finite P" "i \<in> P" "f i = \<omega>"
  thus "setsum f P = \<omega>"
  proof induct
    case (insert x A)
    show ?case using insert by (cases "x = i") auto
  qed simp
qed

lemma real_of_pinfreal_setsum:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<noteq> \<omega>"
  shows "(\<Sum>x\<in>S. real (f x)) = real (setsum f S)"
proof cases
  assume "finite S"
  from this assms show ?thesis
    by induct (simp_all add: real_of_pinfreal_add setsum_\<omega>)
qed simp

lemma setsum_0:
  fixes f :: "'a \<Rightarrow> pinfreal" assumes "finite A"
  shows "(\<Sum>x\<in>A. f x) = 0 \<longleftrightarrow> (\<forall>i\<in>A. f i = 0)"
  using assms by induct auto

lemma suminf_imp_psuminf:
  assumes "f sums x" and "\<forall>n. 0 \<le> f n"
  shows "(\<Sum>\<^isub>\<infinity> x. Real (f x)) = Real x"
  unfolding psuminf_def setsum_Real'[OF assms(2)]
proof (rule SUP_eq_LIMSEQ[THEN iffD2])
  show "mono (\<lambda>n. setsum f {..<n})" (is "mono ?S")
    unfolding mono_iff_le_Suc using assms by simp

  { fix n show "0 \<le> ?S n"
      using setsum_nonneg[of "{..<n}" f] assms by auto }

  thus "0 \<le> x" "?S ----> x"
    using `f sums x` LIMSEQ_le_const
    by (auto simp: atLeast0LessThan sums_def)
qed

lemma psuminf_equality:
  assumes "\<And>n. setsum f {..<n} \<le> x"
  and "\<And>y. y \<noteq> \<omega> \<Longrightarrow> (\<And>n. setsum f {..<n} \<le> y) \<Longrightarrow> x \<le> y"
  shows "psuminf f = x"
  unfolding psuminf_def
proof (safe intro!: pinfreal_SUPI)
  fix n show "setsum f {..<n} \<le> x" using assms(1) .
next
  fix y assume *: "\<forall>n. n \<in> UNIV \<longrightarrow> setsum f {..<n} \<le> y"
  show "x \<le> y"
  proof (cases "y = \<omega>")
    assume "y \<noteq> \<omega>" from assms(2)[OF this] *
    show "x \<le> y" by auto
  qed simp
qed

lemma psuminf_\<omega>:
  assumes "f i = \<omega>"
  shows "(\<Sum>\<^isub>\<infinity> x. f x) = \<omega>"
proof (rule psuminf_equality)
  fix y assume *: "\<And>n. setsum f {..<n} \<le> y"
  have "setsum f {..<Suc i} = \<omega>" 
    using assms by (simp add: setsum_\<omega>)
  thus "\<omega> \<le> y" using *[of "Suc i"] by auto
qed simp

lemma psuminf_imp_suminf:
  assumes "(\<Sum>\<^isub>\<infinity> x. f x) \<noteq> \<omega>"
  shows "(\<lambda>x. real (f x)) sums real (\<Sum>\<^isub>\<infinity> x. f x)"
proof -
  have "\<forall>i. \<exists>r. f i = Real r \<and> 0 \<le> r"
  proof
    fix i show "\<exists>r. f i = Real r \<and> 0 \<le> r" using psuminf_\<omega> assms by (cases "f i") auto
  qed
  from choice[OF this] obtain r where f: "f = (\<lambda>i. Real (r i))"
    and pos: "\<forall>i. 0 \<le> r i"
    by (auto simp: fun_eq_iff)
  hence [simp]: "\<And>i. real (f i) = r i" by auto

  have "mono (\<lambda>n. setsum r {..<n})" (is "mono ?S")
    unfolding mono_iff_le_Suc using pos by simp

  { fix n have "0 \<le> ?S n"
      using setsum_nonneg[of "{..<n}" r] pos by auto }

  from assms obtain p where *: "(\<Sum>\<^isub>\<infinity> x. f x) = Real p" and "0 \<le> p"
    by (cases "(\<Sum>\<^isub>\<infinity> x. f x)") auto
  show ?thesis unfolding * using * pos `0 \<le> p` SUP_eq_LIMSEQ[OF `mono ?S` `\<And>n. 0 \<le> ?S n` `0 \<le> p`]
    by (simp add: f atLeast0LessThan sums_def psuminf_def setsum_Real'[OF pos] f)
qed

lemma psuminf_bound:
  assumes "\<forall>N. (\<Sum>n<N. f n) \<le> x"
  shows "(\<Sum>\<^isub>\<infinity> n. f n) \<le> x"
  using assms by (simp add: psuminf_def SUPR_def Sup_le_iff)

lemma psuminf_bound_add:
  assumes "\<forall>N. (\<Sum>n<N. f n) + y \<le> x"
  shows "(\<Sum>\<^isub>\<infinity> n. f n) + y \<le> x"
proof (cases "x = \<omega>")
  have "y \<le> x" using assms by (auto intro: pinfreal_le_add2)
  assume "x \<noteq> \<omega>"
  note move_y = pinfreal_less_eq_diff_eq_sum[OF `y \<le> x` this]

  have "\<forall>N. (\<Sum>n<N. f n) \<le> x - y" using assms by (simp add: move_y)
  hence "(\<Sum>\<^isub>\<infinity> n. f n) \<le> x - y" by (rule psuminf_bound)
  thus ?thesis by (simp add: move_y)
qed simp

lemma psuminf_finite:
  assumes "\<forall>N\<ge>n. f N = 0"
  shows "(\<Sum>\<^isub>\<infinity> n. f n) = (\<Sum>N<n. f N)"
proof (rule psuminf_equality)
  fix N
  show "setsum f {..<N} \<le> setsum f {..<n}"
  proof (cases rule: linorder_cases)
    assume "N < n" thus ?thesis by (auto intro!: setsum_mono3)
  next
    assume "n < N"
    hence *: "{..<N} = {..<n} \<union> {n..<N}" by auto
    moreover have "setsum f {n..<N} = 0"
      using assms by (auto intro!: setsum_0')
    ultimately show ?thesis unfolding *
      by (subst setsum_Un_disjoint) auto
  qed simp
qed simp

lemma psuminf_upper:
  shows "(\<Sum>n<N. f n) \<le> (\<Sum>\<^isub>\<infinity> n. f n)"
  unfolding psuminf_def SUPR_def
  by (auto intro: complete_lattice_class.Sup_upper image_eqI)

lemma psuminf_le:
  assumes "\<And>N. f N \<le> g N"
  shows "psuminf f \<le> psuminf g"
proof (safe intro!: psuminf_bound)
  fix n
  have "setsum f {..<n} \<le> setsum g {..<n}" using assms by (auto intro: setsum_mono)
  also have "... \<le> psuminf g" by (rule psuminf_upper)
  finally show "setsum f {..<n} \<le> psuminf g" .
qed

lemma psuminf_const[simp]: "psuminf (\<lambda>n. c) = (if c = 0 then 0 else \<omega>)" (is "_ = ?if")
proof (rule psuminf_equality)
  fix y assume *: "\<And>n :: nat. (\<Sum>n<n. c) \<le> y" and "y \<noteq> \<omega>"
  then obtain r p where
    y: "y = Real r" "0 \<le> r" and
    c: "c = Real p" "0 \<le> p"
      using *[of 1] by (cases c, cases y) auto
  show "(if c = 0 then 0 else \<omega>) \<le> y"
  proof (cases "p = 0")
    assume "p = 0" with c show ?thesis by simp
  next
    assume "p \<noteq> 0"
    with * c y have **: "\<And>n :: nat. real n \<le> r / p"
      by (auto simp: zero_le_mult_iff field_simps)
    from ex_less_of_nat[of "r / p"] guess n ..
    with **[of n] show ?thesis by (simp add: real_eq_of_nat)
  qed
qed (cases "c = 0", simp_all)

lemma psuminf_add[simp]: "psuminf (\<lambda>n. f n + g n) = psuminf f + psuminf g"
proof (rule psuminf_equality)
  fix n
  from psuminf_upper[of f n] psuminf_upper[of g n]
  show "(\<Sum>n<n. f n + g n) \<le> psuminf f + psuminf g"
    by (auto simp add: setsum_addf intro!: add_mono)
next
  fix y assume *: "\<And>n. (\<Sum>n<n. f n + g n) \<le> y" and "y \<noteq> \<omega>"
  { fix n m
    have **: "(\<Sum>n<n. f n) + (\<Sum>n<m. g n) \<le> y"
    proof (cases rule: linorder_le_cases)
      assume "n \<le> m"
      hence "(\<Sum>n<n. f n) + (\<Sum>n<m. g n) \<le> (\<Sum>n<m. f n) + (\<Sum>n<m. g n)"
        by (auto intro!: add_right_mono setsum_mono3)
      also have "... \<le> y"
        using * by (simp add: setsum_addf)
      finally show ?thesis .
    next
      assume "m \<le> n"
      hence "(\<Sum>n<n. f n) + (\<Sum>n<m. g n) \<le> (\<Sum>n<n. f n) + (\<Sum>n<n. g n)"
        by (auto intro!: add_left_mono setsum_mono3)
      also have "... \<le> y"
        using * by (simp add: setsum_addf)
      finally show ?thesis .
    qed }
  hence "\<And>m. \<forall>n. (\<Sum>n<n. f n) + (\<Sum>n<m. g n) \<le> y" by simp
  from psuminf_bound_add[OF this]
  have "\<forall>m. (\<Sum>n<m. g n) + psuminf f \<le> y" by (simp add: ac_simps)
  from psuminf_bound_add[OF this]
  show "psuminf f + psuminf g \<le> y" by (simp add: ac_simps)
qed

lemma psuminf_0: "psuminf f = 0 \<longleftrightarrow> (\<forall>i. f i = 0)"
proof safe
  assume "\<forall>i. f i = 0"
  hence "f = (\<lambda>i. 0)" by (simp add: fun_eq_iff)
  thus "psuminf f = 0" using psuminf_const by simp
next
  fix i assume "psuminf f = 0"
  hence "(\<Sum>n<Suc i. f n) = 0" using psuminf_upper[of f "Suc i"] by simp
  thus "f i = 0" by simp
qed

lemma psuminf_cmult_right[simp]: "psuminf (\<lambda>n. c * f n) = c * psuminf f"
proof (rule psuminf_equality)
  fix n show "(\<Sum>n<n. c * f n) \<le> c * psuminf f"
   by (auto simp: setsum_right_distrib[symmetric] intro: mult_left_mono psuminf_upper)
next
  fix y
  assume "\<And>n. (\<Sum>n<n. c * f n) \<le> y"
  hence *: "\<And>n. c * (\<Sum>n<n. f n) \<le> y" by (auto simp add: setsum_right_distrib)
  thus "c * psuminf f \<le> y"
  proof (cases "c = \<omega> \<or> c = 0")
    assume "c = \<omega> \<or> c = 0"
    thus ?thesis
      using * by (fastsimp simp add: psuminf_0 setsum_0 split: split_if_asm)
  next
    assume "\<not> (c = \<omega> \<or> c = 0)"
    hence "c \<noteq> 0" "c \<noteq> \<omega>" by auto
    note rewrite_div = pinfreal_inverse_le_eq[OF this, of _ y]
    hence "\<forall>n. (\<Sum>n<n. f n) \<le> y / c" using * by simp
    hence "psuminf f \<le> y / c" by (rule psuminf_bound)
    thus ?thesis using rewrite_div by simp
  qed
qed

lemma psuminf_cmult_left[simp]: "psuminf (\<lambda>n. f n * c) = psuminf f * c"
  using psuminf_cmult_right[of c f] by (simp add: ac_simps)

lemma psuminf_half_series: "psuminf (\<lambda>n. (1/2)^Suc n) = 1"
  using suminf_imp_psuminf[OF power_half_series] by auto

lemma setsum_pinfsum: "(\<Sum>\<^isub>\<infinity> n. \<Sum>m\<in>A. f n m) = (\<Sum>m\<in>A. (\<Sum>\<^isub>\<infinity> n. f n m))"
proof (cases "finite A")
  assume "finite A"
  thus ?thesis by induct simp_all
qed simp

lemma psuminf_reindex:
  fixes f:: "nat \<Rightarrow> nat" assumes "bij f"
  shows "psuminf (g \<circ> f) = psuminf g"
proof -
  have [intro, simp]: "\<And>A. inj_on f A" using `bij f` unfolding bij_def by (auto intro: subset_inj_on)
  have f[intro, simp]: "\<And>x. f (inv f x) = x"
    using `bij f` unfolding bij_def by (auto intro: surj_f_inv_f)

  show ?thesis
  proof (rule psuminf_equality)
    fix n
    have "setsum (g \<circ> f) {..<n} = setsum g (f ` {..<n})"
      by (simp add: setsum_reindex)
    also have "\<dots> \<le> setsum g {..Max (f ` {..<n})}"
      by (rule setsum_mono3) auto
    also have "\<dots> \<le> psuminf g" unfolding lessThan_Suc_atMost[symmetric] by (rule psuminf_upper)
    finally show "setsum (g \<circ> f) {..<n} \<le> psuminf g" .
  next
    fix y assume *: "\<And>n. setsum (g \<circ> f) {..<n} \<le> y"
    show "psuminf g \<le> y"
    proof (safe intro!: psuminf_bound)
      fix N
      have "setsum g {..<N} \<le> setsum g (f ` {..Max (inv f ` {..<N})})"
        by (rule setsum_mono3) (auto intro!: image_eqI[where f="f", OF f[symmetric]])
      also have "\<dots> = setsum (g \<circ> f) {..Max (inv f ` {..<N})}"
        by (simp add: setsum_reindex)
      also have "\<dots> \<le> y" unfolding lessThan_Suc_atMost[symmetric] by (rule *)
      finally show "setsum g {..<N} \<le> y" .
    qed
  qed
qed

lemma psuminf_2dimen:
  fixes f:: "nat * nat \<Rightarrow> pinfreal"
  assumes fsums: "\<And>m. g m = (\<Sum>\<^isub>\<infinity> n. f (m,n))"
  shows "psuminf (f \<circ> prod_decode) = psuminf g"
proof (rule psuminf_equality)
  fix n :: nat
  let ?P = "prod_decode ` {..<n}"
  have "setsum (f \<circ> prod_decode) {..<n} = setsum f ?P"
    by (auto simp: setsum_reindex inj_prod_decode)
  also have "\<dots> \<le> setsum f ({..Max (fst ` ?P)} \<times> {..Max (snd ` ?P)})"
  proof (safe intro!: setsum_mono3 Max_ge image_eqI)
    fix a b x assume "(a, b) = prod_decode x"
    from this[symmetric] show "a = fst (prod_decode x)" "b = snd (prod_decode x)"
      by simp_all
  qed simp_all
  also have "\<dots> = (\<Sum>m\<le>Max (fst ` ?P). (\<Sum>n\<le>Max (snd ` ?P). f (m,n)))"
    unfolding setsum_cartesian_product by simp
  also have "\<dots> \<le> (\<Sum>m\<le>Max (fst ` ?P). g m)"
    by (auto intro!: setsum_mono psuminf_upper simp del: setsum_lessThan_Suc
        simp: fsums lessThan_Suc_atMost[symmetric])
  also have "\<dots> \<le> psuminf g"
    by (auto intro!: psuminf_upper simp del: setsum_lessThan_Suc
        simp: lessThan_Suc_atMost[symmetric])
  finally show "setsum (f \<circ> prod_decode) {..<n} \<le> psuminf g" .
next
  fix y assume *: "\<And>n. setsum (f \<circ> prod_decode) {..<n} \<le> y"
  have g: "g = (\<lambda>m. \<Sum>\<^isub>\<infinity> n. f (m,n))" unfolding fsums[symmetric] ..
  show "psuminf g \<le> y" unfolding g
  proof (rule psuminf_bound, unfold setsum_pinfsum[symmetric], safe intro!: psuminf_bound)
    fix N M :: nat
    let ?P = "{..<N} \<times> {..<M}"
    let ?M = "Max (prod_encode ` ?P)"
    have "(\<Sum>n<M. \<Sum>m<N. f (m, n)) \<le> (\<Sum>(m, n)\<in>?P. f (m, n))"
      unfolding setsum_commute[of _ _ "{..<M}"] unfolding setsum_cartesian_product ..
    also have "\<dots> \<le> (\<Sum>(m,n)\<in>(prod_decode ` {..?M}). f (m, n))"
      by (auto intro!: setsum_mono3 image_eqI[where f=prod_decode, OF prod_encode_inverse[symmetric]])
    also have "\<dots> \<le> y" using *[of "Suc ?M"]
      by (simp add: lessThan_Suc_atMost[symmetric] setsum_reindex
               inj_prod_decode del: setsum_lessThan_Suc)
    finally show "(\<Sum>n<M. \<Sum>m<N. f (m, n)) \<le> y" .
  qed
qed

lemma pinfreal_mult_less_right:
  assumes "b * a < c * a" "0 < a" "a < \<omega>"
  shows "b < c"
  using assms
  by (cases a, cases b, cases c) (auto split: split_if_asm simp: zero_less_mult_iff zero_le_mult_iff)

lemma pinfreal_\<omega>_eq_plus[simp]: "\<omega> = a + b \<longleftrightarrow> (a = \<omega> \<or> b = \<omega>)"
  by (cases a, cases b) auto

lemma pinfreal_of_nat_le_iff:
  "(of_nat k :: pinfreal) \<le> of_nat m \<longleftrightarrow> k \<le> m" by auto

lemma pinfreal_of_nat_less_iff:
  "(of_nat k :: pinfreal) < of_nat m \<longleftrightarrow> k < m" by auto

lemma pinfreal_bound_add:
  assumes "\<forall>N. f N + y \<le> (x::pinfreal)"
  shows "(SUP n. f n) + y \<le> x"
proof (cases "x = \<omega>")
  have "y \<le> x" using assms by (auto intro: pinfreal_le_add2)
  assume "x \<noteq> \<omega>"
  note move_y = pinfreal_less_eq_diff_eq_sum[OF `y \<le> x` this]

  have "\<forall>N. f N \<le> x - y" using assms by (simp add: move_y)
  hence "(SUP n. f n) \<le> x - y" by (rule SUPR_bound)
  thus ?thesis by (simp add: move_y)
qed simp

lemma SUPR_pinfreal_add:
  fixes f g :: "nat \<Rightarrow> pinfreal"
  assumes f: "\<forall>n. f n \<le> f (Suc n)" and g: "\<forall>n. g n \<le> g (Suc n)"
  shows "(SUP n. f n + g n) = (SUP n. f n) + (SUP n. g n)"
proof (rule pinfreal_SUPI)
  fix n :: nat from le_SUPI[of n UNIV f] le_SUPI[of n UNIV g]
  show "f n + g n \<le> (SUP n. f n) + (SUP n. g n)"
    by (auto intro!: add_mono)
next
  fix y assume *: "\<And>n. n \<in> UNIV \<Longrightarrow> f n + g n \<le> y"
  { fix n m
    have "f n + g m \<le> y"
    proof (cases rule: linorder_le_cases)
      assume "n \<le> m"
      hence "f n + g m \<le> f m + g m"
        using f lift_Suc_mono_le by (auto intro!: add_right_mono)
      also have "\<dots> \<le> y" using * by simp
      finally show ?thesis .
    next
      assume "m \<le> n"
      hence "f n + g m \<le> f n + g n"
        using g lift_Suc_mono_le by (auto intro!: add_left_mono)
      also have "\<dots> \<le> y" using * by simp
      finally show ?thesis .
    qed }
  hence "\<And>m. \<forall>n. f n + g m \<le> y" by simp
  from pinfreal_bound_add[OF this]
  have "\<forall>m. (g m) + (SUP n. f n) \<le> y" by (simp add: ac_simps)
  from pinfreal_bound_add[OF this]
  show "SUPR UNIV f + SUPR UNIV g \<le> y" by (simp add: ac_simps)
qed

lemma SUPR_pinfreal_setsum:
  fixes f :: "'x \<Rightarrow> nat \<Rightarrow> pinfreal"
  assumes "\<And>i. i \<in> P \<Longrightarrow> \<forall>n. f i n \<le> f i (Suc n)"
  shows "(SUP n. \<Sum>i\<in>P. f i n) = (\<Sum>i\<in>P. SUP n. f i n)"
proof cases
  assume "finite P" from this assms show ?thesis
  proof induct
    case (insert i P)
    thus ?case
      apply simp
      apply (subst SUPR_pinfreal_add)
      by (auto intro!: setsum_mono)
  qed simp
qed simp

lemma Real_max:
  assumes "x \<ge> 0" "y \<ge> 0"
  shows "Real (max x y) = max (Real x) (Real y)"
  using assms unfolding max_def by (auto simp add:not_le)

lemma Real_real: "Real (real x) = (if x = \<omega> then 0 else x)"
  using assms by (cases x) auto

lemma inj_on_real: "inj_on real (UNIV - {\<omega>})"
proof (rule inj_onI)
  fix x y assume mem: "x \<in> UNIV - {\<omega>}" "y \<in> UNIV - {\<omega>}" and "real x = real y"
  thus "x = y" by (cases x, cases y) auto
qed

lemma inj_on_Real: "inj_on Real {0..}"
  by (auto intro!: inj_onI)

lemma range_Real[simp]: "range Real = UNIV - {\<omega>}"
proof safe
  fix x assume "x \<notin> range Real"
  thus "x = \<omega>" by (cases x) auto
qed auto

lemma image_Real[simp]: "Real ` {0..} = UNIV - {\<omega>}"
proof safe
  fix x assume "x \<notin> Real ` {0..}"
  thus "x = \<omega>" by (cases x) auto
qed auto

lemma pinfreal_SUP_cmult:
  fixes f :: "'a \<Rightarrow> pinfreal"
  shows "(SUP i : R. z * f i) = z * (SUP i : R. f i)"
proof (rule pinfreal_SUPI)
  fix i assume "i \<in> R"
  from le_SUPI[OF this]
  show "z * f i \<le> z * (SUP i:R. f i)" by (rule pinfreal_mult_cancel)
next
  fix y assume "\<And>i. i\<in>R \<Longrightarrow> z * f i \<le> y"
  hence *: "\<And>i. i\<in>R \<Longrightarrow> z * f i \<le> y" by auto
  show "z * (SUP i:R. f i) \<le> y"
  proof (cases "\<forall>i\<in>R. f i = 0")
    case True
    show ?thesis
    proof cases
      assume "R \<noteq> {}" hence "f ` R = {0}" using True by auto
      thus ?thesis by (simp add: SUPR_def)
    qed (simp add: SUPR_def Sup_empty bot_pinfreal_def)
  next
    case False then obtain i where i: "i \<in> R" and f0: "f i \<noteq> 0" by auto
    show ?thesis
    proof (cases "z = 0 \<or> z = \<omega>")
      case True with f0 *[OF i] show ?thesis by auto
    next
      case False hence z: "z \<noteq> 0" "z \<noteq> \<omega>" by auto
      note div = pinfreal_inverse_le_eq[OF this, symmetric]
      hence "\<And>i. i\<in>R \<Longrightarrow> f i \<le> y / z" using * by auto
      thus ?thesis unfolding div SUP_le_iff by simp
    qed
  qed
qed

instantiation pinfreal :: topological_space
begin

definition "open A \<longleftrightarrow>
  (\<exists>T. open T \<and> (Real ` (T\<inter>{0..}) = A - {\<omega>})) \<and> (\<omega> \<in> A \<longrightarrow> (\<exists>x\<ge>0. {Real x <..} \<subseteq> A))"

lemma open_omega: "open A \<Longrightarrow> \<omega> \<in> A \<Longrightarrow> (\<exists>x\<ge>0. {Real x<..} \<subseteq> A)"
  unfolding open_pinfreal_def by auto

lemma open_omegaD: assumes "open A" "\<omega> \<in> A" obtains x where "x\<ge>0" "{Real x<..} \<subseteq> A"
  using open_omega[OF assms] by auto

lemma pinfreal_openE: assumes "open A" obtains A' x where
  "open A'" "Real ` (A' \<inter> {0..}) = A - {\<omega>}"
  "x \<ge> 0" "\<omega> \<in> A \<Longrightarrow> {Real x<..} \<subseteq> A"
  using assms open_pinfreal_def by auto

instance
proof
  let ?U = "UNIV::pinfreal set"
  show "open ?U" unfolding open_pinfreal_def
    by (auto intro!: exI[of _ "UNIV"] exI[of _ 0])
next
  fix S T::"pinfreal set" assume "open S" and "open T"
  from `open S`[THEN pinfreal_openE] guess S' xS . note S' = this
  from `open T`[THEN pinfreal_openE] guess T' xT . note T' = this

  from S'(1-3) T'(1-3)
  show "open (S \<inter> T)" unfolding open_pinfreal_def
  proof (safe intro!: exI[of _ "S' \<inter> T'"] exI[of _ "max xS xT"])
    fix x assume *: "Real (max xS xT) < x" and "\<omega> \<in> S" "\<omega> \<in> T"
    from `\<omega> \<in> S`[THEN S'(4)] * show "x \<in> S"
      by (cases x, auto simp: max_def split: split_if_asm)
    from `\<omega> \<in> T`[THEN T'(4)] * show "x \<in> T"
      by (cases x, auto simp: max_def split: split_if_asm)
  next
    fix x assume x: "x \<notin> Real ` (S' \<inter> T' \<inter> {0..})"
    have *: "S' \<inter> T' \<inter> {0..} = (S' \<inter> {0..}) \<inter> (T' \<inter> {0..})" by auto
    assume "x \<in> T" "x \<in> S"
    with S'(2) T'(2) show "x = \<omega>"
      using x[unfolded *] inj_on_image_Int[OF inj_on_Real] by auto
  qed auto
next
  fix K assume openK: "\<forall>S \<in> K. open (S:: pinfreal set)"
  hence "\<forall>S\<in>K. \<exists>T. open T \<and> Real ` (T \<inter> {0..}) = S - {\<omega>}" by (auto simp: open_pinfreal_def)
  from bchoice[OF this] guess T .. note T = this[rule_format]

  show "open (\<Union>K)" unfolding open_pinfreal_def
  proof (safe intro!: exI[of _ "\<Union>(T ` K)"])
    fix x S assume "0 \<le> x" "x \<in> T S" "S \<in> K"
    with T[OF `S \<in> K`] show "Real x \<in> \<Union>K" by auto
  next
    fix x S assume x: "x \<notin> Real ` (\<Union>T ` K \<inter> {0..})" "S \<in> K" "x \<in> S"
    hence "x \<notin> Real ` (T S \<inter> {0..})"
      by (auto simp: image_UN UN_simps[symmetric] simp del: UN_simps)
    thus "x = \<omega>" using T[OF `S \<in> K`] `x \<in> S` by auto
  next
    fix S assume "\<omega> \<in> S" "S \<in> K"
    from openK[rule_format, OF `S \<in> K`, THEN pinfreal_openE] guess S' x .
    from this(3, 4) `\<omega> \<in> S`
    show "\<exists>x\<ge>0. {Real x<..} \<subseteq> \<Union>K"
      by (auto intro!: exI[of _ x] bexI[OF _ `S \<in> K`])
  next
    from T[THEN conjunct1] show "open (\<Union>T`K)" by auto
  qed auto
qed
end

lemma open_pinfreal_lessThan[simp]:
  "open {..< a :: pinfreal}"
proof (cases a)
  case (preal x) thus ?thesis unfolding open_pinfreal_def
  proof (safe intro!: exI[of _ "{..< x}"])
    fix y assume "y < Real x"
    moreover assume "y \<notin> Real ` ({..<x} \<inter> {0..})"
    ultimately have "y \<noteq> Real (real y)" using preal by (cases y) auto
    thus "y = \<omega>" by (auto simp: Real_real split: split_if_asm)
  qed auto
next
  case infinite thus ?thesis
    unfolding open_pinfreal_def by (auto intro!: exI[of _ UNIV])
qed

lemma open_pinfreal_greaterThan[simp]:
  "open {a :: pinfreal <..}"
proof (cases a)
  case (preal x) thus ?thesis unfolding open_pinfreal_def
  proof (safe intro!: exI[of _ "{x <..}"])
    fix y assume "Real x < y"
    moreover assume "y \<notin> Real ` ({x<..} \<inter> {0..})"
    ultimately have "y \<noteq> Real (real y)" using preal by (cases y) auto
    thus "y = \<omega>" by (auto simp: Real_real split: split_if_asm)
  qed auto
next
  case infinite thus ?thesis
    unfolding open_pinfreal_def by (auto intro!: exI[of _ "{}"])
qed

lemma pinfreal_open_greaterThanLessThan[simp]: "open {a::pinfreal <..< b}"
  unfolding greaterThanLessThan_def by auto

lemma closed_pinfreal_atLeast[simp, intro]: "closed {a :: pinfreal ..}"
proof -
  have "- {a ..} = {..< a}" by auto
  then show "closed {a ..}"
    unfolding closed_def using open_pinfreal_lessThan by auto
qed

lemma closed_pinfreal_atMost[simp, intro]: "closed {.. b :: pinfreal}"
proof -
  have "- {.. b} = {b <..}" by auto
  then show "closed {.. b}" 
    unfolding closed_def using open_pinfreal_greaterThan by auto
qed

lemma closed_pinfreal_atLeastAtMost[simp, intro]:
  shows "closed {a :: pinfreal .. b}"
  unfolding atLeastAtMost_def by auto

lemma pinfreal_dense:
  fixes x y :: pinfreal assumes "x < y"
  shows "\<exists>z. x < z \<and> z < y"
proof -
  from `x < y` obtain p where p: "x = Real p" "0 \<le> p" by (cases x) auto
  show ?thesis
  proof (cases y)
    case (preal r) with p `x < y` have "p < r" by auto
    with dense obtain z where "p < z" "z < r" by auto
    thus ?thesis using preal p by (auto intro!: exI[of _ "Real z"])
  next
    case infinite thus ?thesis using `x < y` p
      by (auto intro!: exI[of _ "Real p + 1"])
  qed
qed

instance pinfreal :: t2_space
proof
  fix x y :: pinfreal assume "x \<noteq> y"
  let "?P x (y::pinfreal)" = "\<exists> U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"

  { fix x y :: pinfreal assume "x < y"
    from pinfreal_dense[OF this] obtain z where z: "x < z" "z < y" by auto
    have "?P x y"
      apply (rule exI[of _ "{..<z}"])
      apply (rule exI[of _ "{z<..}"])
      using z by auto }
  note * = this

  from `x \<noteq> y`
  show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
  proof (cases rule: linorder_cases)
    assume "x = y" with `x \<noteq> y` show ?thesis by simp
  next assume "x < y" from *[OF this] show ?thesis by auto
  next assume "y < x" from *[OF this] show ?thesis by auto
  qed
qed

definition (in complete_lattice) isoton :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<up>" 50) where
  "A \<up> X \<longleftrightarrow> (\<forall>i. A i \<le> A (Suc i)) \<and> (SUP i. A i) = X"

definition (in complete_lattice) antiton (infix "\<down>" 50) where
  "A \<down> X \<longleftrightarrow> (\<forall>i. A i \<ge> A (Suc i)) \<and> (INF i. A i) = X"

lemma range_const[simp]: "range (\<lambda>x. c) = {c}" by auto

lemma isoton_cmult_right:
  assumes "f \<up> (x::pinfreal)"
  shows "(\<lambda>i. c * f i) \<up> (c * x)"
  using assms unfolding isoton_def pinfreal_SUP_cmult
  by (auto intro: pinfreal_mult_cancel)

lemma isoton_cmult_left:
  "f \<up> (x::pinfreal) \<Longrightarrow> (\<lambda>i. f i * c) \<up> (x * c)"
  by (subst (1 2) mult_commute) (rule isoton_cmult_right)

lemma isoton_add:
  assumes "f \<up> (x::pinfreal)" and "g \<up> y"
  shows "(\<lambda>i. f i + g i) \<up> (x + y)"
  using assms unfolding isoton_def
  by (auto intro: pinfreal_mult_cancel add_mono simp: SUPR_pinfreal_add)

lemma isoton_fun_expand:
  "f \<up> x \<longleftrightarrow> (\<forall>i. (\<lambda>j. f j i) \<up> (x i))"
proof -
  have "\<And>i. {y. \<exists>f'\<in>range f. y = f' i} = range (\<lambda>j. f j i)"
    by auto
  with assms show ?thesis
    by (auto simp add: isoton_def le_fun_def Sup_fun_def SUPR_def)
qed

lemma isoton_indicator:
  assumes "f \<up> g"
  shows "(\<lambda>i x. f i x * indicator A x) \<up> (\<lambda>x. g x * indicator A x :: pinfreal)"
  using assms unfolding isoton_fun_expand by (auto intro!: isoton_cmult_left)

lemma pinfreal_ord_one[simp]:
  "Real p < 1 \<longleftrightarrow> p < 1"
  "Real p \<le> 1 \<longleftrightarrow> p \<le> 1"
  "1 < Real p \<longleftrightarrow> 1 < p"
  "1 \<le> Real p \<longleftrightarrow> 1 \<le> p"
  by (simp_all add: one_pinfreal_def del: Real_1)

lemma isoton_Sup:
  assumes "f \<up> u"
  shows "f i \<le> u"
  using le_SUPI[of i UNIV f] assms
  unfolding isoton_def by auto

lemma isoton_mono:
  assumes iso: "x \<up> a" "y \<up> b" and *: "\<And>n. x n \<le> y (N n)"
  shows "a \<le> b"
proof -
  from iso have "a = (SUP n. x n)" "b = (SUP n. y n)"
    unfolding isoton_def by auto
  with * show ?thesis by (auto intro!: SUP_mono)
qed

lemma pinfreal_le_mult_one_interval:
  fixes x y :: pinfreal
  assumes "\<And>z. \<lbrakk> 0 < z ; z < 1 \<rbrakk> \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
proof (cases x, cases y)
  assume "x = \<omega>"
  with assms[of "1 / 2"]
  show "x \<le> y" by simp
next
  fix r p assume *: "y = Real p" "x = Real r" and **: "0 \<le> r" "0 \<le> p"
  have "r \<le> p"
  proof (rule field_le_mult_one_interval)
    fix z :: real assume "0 < z" and "z < 1"
    with assms[of "Real z"]
    show "z * r \<le> p" using ** * by (auto simp: zero_le_mult_iff)
  qed
  thus "x \<le> y" using ** * by simp
qed simp

lemma pinfreal_greater_0[intro]:
  fixes a :: pinfreal
  assumes "a \<noteq> 0"
  shows "a > 0"
using assms apply (cases a) by auto

lemma pinfreal_mult_strict_right_mono:
  assumes "a < b" and "0 < c" "c < \<omega>"
  shows "a * c < b * c"
  using assms
  by (cases a, cases b, cases c)
     (auto simp: zero_le_mult_iff pinfreal_less_\<omega>)

lemma minus_pinfreal_eq2:
  fixes x y z :: pinfreal
  assumes "y \<le> x" and "y \<noteq> \<omega>" shows "z = x - y \<longleftrightarrow> z + y = x"
  using assms
  apply (subst eq_commute)
  apply (subst minus_pinfreal_eq)
  by (cases x, cases z, auto simp add: ac_simps not_less)

lemma pinfreal_diff_eq_diff_imp_eq:
  assumes "a \<noteq> \<omega>" "b \<le> a" "c \<le> a"
  assumes "a - b = a - c"
  shows "b = c"
  using assms
  by (cases a, cases b, cases c) (auto split: split_if_asm)

lemma pinfreal_inverse_eq_0: "inverse x = 0 \<longleftrightarrow> x = \<omega>"
  by (cases x) auto

lemma pinfreal_mult_inverse:
  "\<lbrakk> x \<noteq> \<omega> ; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x * inverse x = 1"
  by (cases x) auto

lemma pinfreal_zero_less_diff_iff:
  fixes a b :: pinfreal shows "0 < a - b \<longleftrightarrow> b < a"
  apply (cases a, cases b)
  apply (auto simp: pinfreal_noteq_omega_Ex pinfreal_less_\<omega>)
  apply (cases b)
  by auto

lemma pinfreal_less_Real_Ex:
  fixes a b :: pinfreal shows "x < Real r \<longleftrightarrow> (\<exists>p\<ge>0. p < r \<and> x = Real p)"
  by (cases x) auto

lemma open_Real: assumes "open S" shows "open (Real ` ({0..} \<inter> S))"
  unfolding open_pinfreal_def apply(rule,rule,rule,rule assms) by auto

lemma pinfreal_zero_le_diff:
  fixes a b :: pinfreal shows "a - b = 0 \<longleftrightarrow> a \<le> b"
  by (cases a, cases b, simp_all, cases b, auto)

lemma lim_Real[simp]: assumes "\<forall>n. f n \<ge> 0" "m\<ge>0"
  shows "(\<lambda>n. Real (f n)) ----> Real m \<longleftrightarrow> (\<lambda>n. f n) ----> m" (is "?l = ?r")
proof assume ?l show ?r unfolding Lim_sequentially
  proof safe fix e::real assume e:"e>0"
    note open_ball[of m e] note open_Real[OF this]
    note * = `?l`[unfolded tendsto_def,rule_format,OF this]
    have "eventually (\<lambda>x. Real (f x) \<in> Real ` ({0..} \<inter> ball m e)) sequentially"
      apply(rule *) unfolding image_iff using assms(2) e by auto
    thus "\<exists>N. \<forall>n\<ge>N. dist (f n) m < e" unfolding eventually_sequentially 
      apply safe apply(rule_tac x=N in exI,safe) apply(erule_tac x=n in allE,safe)
    proof- fix n x assume "Real (f n) = Real x" "0 \<le> x"
      hence *:"f n = x" using assms(1) by auto
      assume "x \<in> ball m e" thus "dist (f n) m < e" unfolding *
        by (auto simp add:dist_commute)
    qed qed
next assume ?r show ?l unfolding tendsto_def eventually_sequentially 
  proof safe fix S assume S:"open S" "Real m \<in> S"
    guess T y using S(1) apply-apply(erule pinfreal_openE) . note T=this
    have "m\<in>real ` (S - {\<omega>})" unfolding image_iff 
      apply(rule_tac x="Real m" in bexI) using assms(2) S(2) by auto
    hence "m \<in> T" unfolding T(2)[THEN sym] by auto 
    from `?r`[unfolded tendsto_def eventually_sequentially,rule_format,OF T(1) this]
    guess N .. note N=this[rule_format]
    show "\<exists>N. \<forall>n\<ge>N. Real (f n) \<in> S" apply(rule_tac x=N in exI) 
    proof safe fix n assume n:"N\<le>n"
      have "f n \<in> real ` (S - {\<omega>})" using N[OF n] assms unfolding T(2)[THEN sym] 
        unfolding image_iff apply-apply(rule_tac x="Real (f n)" in bexI)
        unfolding real_Real by auto
      then guess x unfolding image_iff .. note x=this
      show "Real (f n) \<in> S" unfolding x apply(subst Real_real) using x by auto
    qed
  qed
qed

lemma pinfreal_INFI:
  fixes x :: pinfreal
  assumes "\<And>i. i \<in> A \<Longrightarrow> x \<le> f i"
  assumes "\<And>y. (\<And>i. i \<in> A \<Longrightarrow> y \<le> f i) \<Longrightarrow> y \<le> x"
  shows "(INF i:A. f i) = x"
  unfolding INFI_def Inf_pinfreal_def
  using assms by (auto intro!: Greatest_equality)

lemma real_of_pinfreal_less:"x < y \<Longrightarrow> y\<noteq>\<omega> \<Longrightarrow> real x < real y"
proof- case goal1
  have *:"y = Real (real y)" "x = Real (real x)" using goal1 Real_real by auto
  show ?case using goal1 apply- apply(subst(asm) *(1))apply(subst(asm) *(2))
    unfolding pinfreal_less by auto
qed

lemma not_less_omega[simp]:"\<not> x < \<omega> \<longleftrightarrow> x = \<omega>"
  by (metis antisym_conv3 pinfreal_less(3)) 

lemma Real_real': assumes "x\<noteq>\<omega>" shows "Real (real x) = x"
proof- have *:"(THE r. 0 \<le> r \<and> x = Real r) = real x"
    apply(rule the_equality) using assms unfolding Real_real by auto
  have "Real (THE r. 0 \<le> r \<and> x = Real r) = x" unfolding *
    using assms unfolding Real_real by auto
  thus ?thesis unfolding real_of_pinfreal_def of_pinfreal_def
    unfolding pinfreal_case_def using assms by auto
qed 

lemma Real_less_plus_one:"Real x < Real (max (x + 1) 1)" 
  unfolding pinfreal_less by auto

lemma Lim_omega: "f ----> \<omega> \<longleftrightarrow> (\<forall>B. \<exists>N. \<forall>n\<ge>N. f n \<ge> Real B)" (is "?l = ?r")
proof assume ?r show ?l apply(rule topological_tendstoI)
    unfolding eventually_sequentially
  proof- fix S assume "open S" "\<omega> \<in> S"
    from open_omega[OF this] guess B .. note B=this
    from `?r`[rule_format,of "(max B 0)+1"] guess N .. note N=this
    show "\<exists>N. \<forall>n\<ge>N. f n \<in> S" apply(rule_tac x=N in exI)
    proof safe case goal1 
      have "Real B < Real ((max B 0) + 1)" by auto
      also have "... \<le> f n" using goal1 N by auto
      finally show ?case using B by fastsimp
    qed
  qed
next assume ?l show ?r
  proof fix B::real have "open {Real B<..}" "\<omega> \<in> {Real B<..}" by auto
    from topological_tendstoD[OF `?l` this,unfolded eventually_sequentially]
    guess N .. note N=this
    show "\<exists>N. \<forall>n\<ge>N. Real B \<le> f n" apply(rule_tac x=N in exI) using N by auto
  qed
qed

lemma Lim_bounded_omgea: assumes lim:"f ----> l" and "\<And>n. f n \<le> Real B" shows "l \<noteq> \<omega>"
proof(rule ccontr,unfold not_not) let ?B = "max (B + 1) 1" assume as:"l=\<omega>"
  from lim[unfolded this Lim_omega,rule_format,of "?B"]
  guess N .. note N=this[rule_format,OF le_refl]
  hence "Real ?B \<le> Real B" using assms(2)[of N] by(rule order_trans) 
  hence "Real ?B < Real ?B" using Real_less_plus_one[of B] by(rule le_less_trans)
  thus False by auto
qed

lemma incseq_le_pinfreal: assumes inc: "\<And>n m. n\<ge>m \<Longrightarrow> X n \<ge> X m"
  and lim: "X ----> (L::pinfreal)" shows "X n \<le> L"
proof(cases "L = \<omega>")
  case False have "\<forall>n. X n \<noteq> \<omega>"
  proof(rule ccontr,unfold not_all not_not,safe)
    case goal1 hence "\<forall>n\<ge>x. X n = \<omega>" using inc[of x] by auto
    hence "X ----> \<omega>" unfolding tendsto_def eventually_sequentially
      apply safe apply(rule_tac x=x in exI) by auto
    note Lim_unique[OF trivial_limit_sequentially this lim]
    with False show False by auto
  qed note * =this[rule_format]

  have **:"\<forall>m n. m \<le> n \<longrightarrow> Real (real (X m)) \<le> Real (real (X n))"
    unfolding Real_real using * inc by auto
  have "real (X n) \<le> real L" apply-apply(rule incseq_le) defer
    apply(subst lim_Real[THEN sym]) apply(rule,rule,rule)
    unfolding Real_real'[OF *] Real_real'[OF False] 
    unfolding incseq_def using ** lim by auto
  hence "Real (real (X n)) \<le> Real (real L)" by auto
  thus ?thesis unfolding Real_real using * False by auto
qed auto

lemma SUP_Lim_pinfreal: assumes "\<And>n m. n\<ge>m \<Longrightarrow> f n \<ge> f m" "f ----> l"
  shows "(SUP n. f n) = (l::pinfreal)" unfolding SUPR_def Sup_pinfreal_def
proof (safe intro!: Least_equality)
  fix n::nat show "f n \<le> l" apply(rule incseq_le_pinfreal)
    using assms by auto
next fix y assume y:"\<forall>x\<in>range f. x \<le> y" show "l \<le> y"
  proof(rule ccontr,cases "y=\<omega>",unfold not_le)
    case False assume as:"y < l"
    have l:"l \<noteq> \<omega>" apply(rule Lim_bounded_omgea[OF assms(2), of "real y"])
      using False y unfolding Real_real by auto

    have yl:"real y < real l" using as apply-
      apply(subst(asm) Real_real'[THEN sym,OF `y\<noteq>\<omega>`])
      apply(subst(asm) Real_real'[THEN sym,OF `l\<noteq>\<omega>`]) 
      unfolding pinfreal_less apply(subst(asm) if_P) by auto
    hence "y + (y - l) * Real (1 / 2) < l" apply-
      apply(subst Real_real'[THEN sym,OF `y\<noteq>\<omega>`]) apply(subst(2) Real_real'[THEN sym,OF `y\<noteq>\<omega>`])
      apply(subst Real_real'[THEN sym,OF `l\<noteq>\<omega>`]) apply(subst(2) Real_real'[THEN sym,OF `l\<noteq>\<omega>`]) by auto
    hence *:"l \<in> {y + (y - l) / 2<..}" by auto
    have "open {y + (y-l)/2 <..}" by auto
    note topological_tendstoD[OF assms(2) this *]
    from this[unfolded eventually_sequentially] guess N .. note this[rule_format, of N]
    hence "y + (y - l) * Real (1 / 2) < y" using y[rule_format,of "f N"] by auto
    hence "Real (real y) + (Real (real y) - Real (real l)) * Real (1 / 2) < Real (real y)"
      unfolding Real_real using `y\<noteq>\<omega>` `l\<noteq>\<omega>` by auto
    thus False using yl by auto
  qed auto
qed

lemma Real_max':"Real x = Real (max x 0)" 
proof(cases "x < 0") case True
  hence *:"max x 0 = 0" by auto
  show ?thesis unfolding * using True by auto
qed auto

lemma lim_pinfreal_increasing: assumes "\<forall>n m. n\<ge>m \<longrightarrow> f n \<ge> f m"
  obtains l where "f ----> (l::pinfreal)"
proof(cases "\<exists>B. \<forall>n. f n < Real B")
  case False thus thesis apply- apply(rule that[of \<omega>]) unfolding Lim_omega not_ex not_all
    apply safe apply(erule_tac x=B in allE,safe) apply(rule_tac x=x in exI,safe)
    apply(rule order_trans[OF _ assms[rule_format]]) by auto
next case True then guess B .. note B = this[rule_format]
  hence *:"\<And>n. f n < \<omega>" apply-apply(rule less_le_trans,assumption) by auto
  have *:"\<And>n. f n \<noteq> \<omega>" proof- case goal1 show ?case using *[of n] by auto qed
  have B':"\<And>n. real (f n) \<le> max 0 B" proof- case goal1 thus ?case
      using B[of n] apply-apply(subst(asm) Real_real'[THEN sym]) defer
      apply(subst(asm)(2) Real_max') unfolding pinfreal_less apply(subst(asm) if_P) using *[of n] by auto
  qed
  have "\<exists>l. (\<lambda>n. real (f n)) ----> l" apply(rule Topology_Euclidean_Space.bounded_increasing_convergent)
  proof safe show "bounded {real (f n) |n. True}"
      unfolding bounded_def apply(rule_tac x=0 in exI,rule_tac x="max 0 B" in exI)
      using B' unfolding dist_norm by auto
    fix n::nat have "Real (real (f n)) \<le> Real (real (f (Suc n)))"
      using assms[rule_format,of n "Suc n"] apply(subst Real_real)+
      using *[of n] *[of "Suc n"] by fastsimp
    thus "real (f n) \<le> real (f (Suc n))" by auto
  qed then guess l .. note l=this
  have "0 \<le> l" apply(rule LIMSEQ_le_const[OF l])
    by(rule_tac x=0 in exI,auto)

  thus ?thesis apply-apply(rule that[of "Real l"])
    using l apply-apply(subst(asm) lim_Real[THEN sym]) prefer 3
    unfolding Real_real using * by auto
qed

lemma setsum_neq_omega: assumes "finite s" "\<And>x. x \<in> s \<Longrightarrow> f x \<noteq> \<omega>"
  shows "setsum f s \<noteq> \<omega>" using assms
proof induct case (insert x s)
  show ?case unfolding setsum.insert[OF insert(1-2)] 
    using insert by auto
qed auto


lemma real_Real': "0 \<le> x \<Longrightarrow> real (Real x) = x"
  unfolding real_Real by auto

lemma real_pinfreal_pos[intro]:
  assumes "x \<noteq> 0" "x \<noteq> \<omega>"
  shows "real x > 0"
  apply(subst real_Real'[THEN sym,of 0]) defer
  apply(rule real_of_pinfreal_less) using assms by auto

lemma Lim_omega_gt: "f ----> \<omega> \<longleftrightarrow> (\<forall>B. \<exists>N. \<forall>n\<ge>N. f n > Real B)" (is "?l = ?r")
proof assume ?l thus ?r unfolding Lim_omega apply safe
    apply(erule_tac x="max B 0 +1" in allE,safe)
    apply(rule_tac x=N in exI,safe) apply(erule_tac x=n in allE,safe)
    apply(rule_tac y="Real (max B 0 + 1)" in less_le_trans) by auto
next assume ?r thus ?l unfolding Lim_omega apply safe
    apply(erule_tac x=B in allE,safe) apply(rule_tac x=N in exI,safe) by auto
qed

lemma pinfreal_minus_le_cancel:
  fixes a b c :: pinfreal
  assumes "b \<le> a"
  shows "c - a \<le> c - b"
  using assms by (cases a, cases b, cases c, simp, simp, simp, cases b, cases c, simp_all)

lemma pinfreal_minus_\<omega>[simp]: "x - \<omega> = 0" by (cases x) simp_all

lemma pinfreal_minus_mono[intro]: "a - x \<le> (a::pinfreal)"
proof- have "a - x \<le> a - 0"
    apply(rule pinfreal_minus_le_cancel) by auto
  thus ?thesis by auto
qed

lemma pinfreal_minus_eq_\<omega>[simp]: "x - y = \<omega> \<longleftrightarrow> (x = \<omega> \<and> y \<noteq> \<omega>)"
  by (cases x, cases y) (auto, cases y, auto)

lemma pinfreal_less_minus_iff:
  fixes a b c :: pinfreal
  shows "a < b - c \<longleftrightarrow> c + a < b"
  by (cases c, cases a, cases b, auto)

lemma pinfreal_minus_less_iff:
  fixes a b c :: pinfreal shows "a - c < b \<longleftrightarrow> (0 < b \<and> (c \<noteq> \<omega> \<longrightarrow> a < b + c))"
  by (cases c, cases a, cases b, auto)

lemma pinfreal_le_minus_iff:
  fixes a b c :: pinfreal
  shows "a \<le> c - b \<longleftrightarrow> ((c \<le> b \<longrightarrow> a = 0) \<and> (b < c \<longrightarrow> a + b \<le> c))"
  by (cases a, cases c, cases b, auto simp: pinfreal_noteq_omega_Ex)

lemma pinfreal_minus_le_iff:
  fixes a b c :: pinfreal
  shows "a - c \<le> b \<longleftrightarrow> (c \<le> a \<longrightarrow> a \<le> b + c)"
  by (cases a, cases c, cases b, auto simp: pinfreal_noteq_omega_Ex)

lemmas pinfreal_minus_order = pinfreal_minus_le_iff pinfreal_minus_less_iff pinfreal_le_minus_iff pinfreal_less_minus_iff

lemma pinfreal_minus_strict_mono:
  assumes "a > 0" "x > 0" "a\<noteq>\<omega>"
  shows "a - x < (a::pinfreal)"
  using assms by(cases x, cases a, auto)

lemma pinfreal_minus':
  "Real r - Real p = (if 0 \<le> r \<and> p \<le> r then if 0 \<le> p then Real (r - p) else Real r else 0)"
  by (auto simp: minus_pinfreal_eq not_less)

lemma pinfreal_minus_plus:
  "x \<le> (a::pinfreal) \<Longrightarrow> a - x + x = a"
  by (cases a, cases x) auto

lemma pinfreal_cancel_plus_minus: "b \<noteq> \<omega> \<Longrightarrow> a + b - b = a"
  by (cases a, cases b) auto

lemma pinfreal_minus_le_cancel_right:
  fixes a b c :: pinfreal
  assumes "a \<le> b" "c \<le> a"
  shows "a - c \<le> b - c"
  using assms by (cases a, cases b, cases c, auto, cases c, auto)

lemma real_of_pinfreal_setsum':
  assumes "\<forall>x \<in> S. f x \<noteq> \<omega>"
  shows "(\<Sum>x\<in>S. real (f x)) = real (setsum f S)"
proof cases
  assume "finite S"
  from this assms show ?thesis
    by induct (simp_all add: real_of_pinfreal_add setsum_\<omega>)
qed simp

lemma Lim_omega_pos: "f ----> \<omega> \<longleftrightarrow> (\<forall>B>0. \<exists>N. \<forall>n\<ge>N. f n \<ge> Real B)" (is "?l = ?r")
  unfolding Lim_omega apply safe defer
  apply(erule_tac x="max 1 B" in allE) apply safe defer
  apply(rule_tac x=N in exI,safe) apply(erule_tac x=n in allE,safe)
  apply(rule_tac y="Real (max 1 B)" in order_trans) by auto

lemma (in complete_lattice) isotonD[dest]:
  assumes "A \<up> X" shows "A i \<le> A (Suc i)" "(SUP i. A i) = X"
  using assms unfolding isoton_def by auto

lemma isotonD'[dest]:
  assumes "(A::_=>_) \<up> X" shows "A i x \<le> A (Suc i) x" "(SUP i. A i) = X"
  using assms unfolding isoton_def le_fun_def by auto

lemma pinfreal_LimI_finite:
  assumes "x \<noteq> \<omega>" "\<And>r. 0 < r \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. u n < x + r \<and> x < u n + r"
  shows "u ----> x"
proof (rule topological_tendstoI, unfold eventually_sequentially)
  fix S assume "open S" "x \<in> S"
  then obtain A where "open A" and A_eq: "Real ` (A \<inter> {0..}) = S - {\<omega>}" by (auto elim!: pinfreal_openE)
  then have "x \<in> Real ` (A \<inter> {0..})" using `x \<in> S` `x \<noteq> \<omega>` by auto
  then have "real x \<in> A" by auto
  then obtain r where "0 < r" and dist: "\<And>y. dist y (real x) < r \<Longrightarrow> y \<in> A"
    using `open A` unfolding open_real_def by auto
  then obtain n where
    upper: "\<And>N. n \<le> N \<Longrightarrow> u N < x + Real r" and
    lower: "\<And>N. n \<le> N \<Longrightarrow> x < u N + Real r" using assms(2)[of "Real r"] by auto
  show "\<exists>N. \<forall>n\<ge>N. u n \<in> S"
  proof (safe intro!: exI[of _ n])
    fix N assume "n \<le> N"
    from upper[OF this] `x \<noteq> \<omega>` `0 < r`
    have "u N \<noteq> \<omega>" by (force simp: pinfreal_noteq_omega_Ex)
    with `x \<noteq> \<omega>` `0 < r` lower[OF `n \<le> N`] upper[OF `n \<le> N`]
    have "dist (real (u N)) (real x) < r" "u N \<noteq> \<omega>"
      by (auto simp: pinfreal_noteq_omega_Ex dist_real_def abs_diff_less_iff field_simps)
    from dist[OF this(1)]
    have "u N \<in> Real ` (A \<inter> {0..})" using `u N \<noteq> \<omega>`
      by (auto intro!: image_eqI[of _ _ "real (u N)"] simp: pinfreal_noteq_omega_Ex Real_real)
    thus "u N \<in> S" using A_eq by simp
  qed
qed

lemma real_Real_max:"real (Real x) = max x 0"
  unfolding real_Real by auto

lemma (in complete_lattice) SUPR_upper:
  "x \<in> A \<Longrightarrow> f x \<le> SUPR A f"
  unfolding SUPR_def apply(rule Sup_upper) by auto

lemma (in complete_lattice) SUPR_subset:
  assumes "A \<subseteq> B" shows "SUPR A f \<le> SUPR B f"
  apply(rule SUP_leI) apply(rule SUPR_upper) using assms by auto

lemma (in complete_lattice) SUPR_mono:
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. f b \<ge> f a"
  shows "SUPR A f \<le> SUPR B f"
  unfolding SUPR_def apply(rule Sup_mono)
  using assms by auto

lemma Sup_lim:
  assumes "\<forall>n. b n \<in> s" "b ----> (a::pinfreal)"
  shows "a \<le> Sup s"
proof(rule ccontr,unfold not_le)
  assume as:"Sup s < a" hence om:"Sup s \<noteq> \<omega>" by auto
  have s:"s \<noteq> {}" using assms by auto
  { presume *:"\<forall>n. b n < a \<Longrightarrow> False"
    show False apply(cases,rule *,assumption,unfold not_all not_less)
    proof- case goal1 then guess n .. note n=this
      thus False using complete_lattice_class.Sup_upper[OF assms(1)[rule_format,of n]]
        using as by auto
    qed
  } assume b:"\<forall>n. b n < a"
  show False
  proof(cases "a = \<omega>")
    case False have *:"a - Sup s > 0" 
      using False as by(auto simp: pinfreal_zero_le_diff)
    have "(a - Sup s) / 2 \<le> a / 2" unfolding divide_pinfreal_def
      apply(rule mult_right_mono) by auto
    also have "... = Real (real (a / 2))" apply(rule Real_real'[THEN sym])
      using False by auto
    also have "... < Real (real a)" unfolding pinfreal_less using as False
      by(auto simp add: real_of_pinfreal_mult[THEN sym])
    also have "... = a" apply(rule Real_real') using False by auto
    finally have asup:"a > (a - Sup s) / 2" .
    have "\<exists>n. a - b n < (a - Sup s) / 2"
    proof(rule ccontr,unfold not_ex not_less)
      case goal1
      have "(a - Sup s) * Real (1 / 2)  > 0" 
        using * by auto
      hence "a - (a - Sup s) * Real (1 / 2) < a"
        apply-apply(rule pinfreal_minus_strict_mono)
        using False * by auto
      hence *:"a \<in> {a - (a - Sup s) / 2<..}"using asup by auto 
      note topological_tendstoD[OF assms(2) open_pinfreal_greaterThan,OF *]
      from this[unfolded eventually_sequentially] guess n .. 
      note n = this[rule_format,of n] 
      have "b n + (a - Sup s) / 2 \<le> a" 
        using add_right_mono[OF goal1[rule_format,of n],of "b n"]
        unfolding pinfreal_minus_plus[OF less_imp_le[OF b[rule_format]]]
        by(auto simp: add_commute)
      hence "b n \<le> a - (a - Sup s) / 2" unfolding pinfreal_le_minus_iff
        using asup by auto
      hence "b n \<notin> {a - (a - Sup s) / 2<..}" by auto
      thus False using n by auto
    qed
    then guess n .. note n = this
    have "Sup s < a - (a - Sup s) / 2"
      using False as om by (cases a) (auto simp: pinfreal_noteq_omega_Ex field_simps)
    also have "... \<le> b n"
    proof- note add_right_mono[OF less_imp_le[OF n],of "b n"]
      note this[unfolded pinfreal_minus_plus[OF less_imp_le[OF b[rule_format]]]]
      hence "a - (a - Sup s) / 2 \<le> (a - Sup s) / 2 + b n - (a - Sup s) / 2"
        apply(rule pinfreal_minus_le_cancel_right) using asup by auto
      also have "... = b n + (a - Sup s) / 2 - (a - Sup s) / 2" 
        by(auto simp add: add_commute)
      also have "... = b n" apply(subst pinfreal_cancel_plus_minus)
      proof(rule ccontr,unfold not_not) case goal1
        show ?case using asup unfolding goal1 by auto 
      qed auto
      finally show ?thesis .
    qed     
    finally show False
      using complete_lattice_class.Sup_upper[OF assms(1)[rule_format,of n]] by auto  
  next case True
    from assms(2)[unfolded True Lim_omega_gt,rule_format,of "real (Sup s)"]
    guess N .. note N = this[rule_format,of N]
    thus False using complete_lattice_class.Sup_upper[OF assms(1)[rule_format,of N]] 
      unfolding Real_real using om by auto
  qed qed

lemma less_SUP_iff:
  fixes a :: pinfreal
  shows "(a < (SUP i:A. f i)) \<longleftrightarrow> (\<exists>x\<in>A. a < f x)"
  unfolding SUPR_def less_Sup_iff by auto

lemma Sup_mono_lim:
  assumes "\<forall>a\<in>A. \<exists>b. \<forall>n. b n \<in> B \<and> b ----> (a::pinfreal)"
  shows "Sup A \<le> Sup B"
  unfolding Sup_le_iff apply(rule) apply(drule assms[rule_format]) apply safe
  apply(rule_tac b=b in Sup_lim) by auto

lemma pinfreal_less_add:
  assumes "x \<noteq> \<omega>" "a < b"
  shows "x + a < x + b"
  using assms by (cases a, cases b, cases x) auto

lemma SUPR_lim:
  assumes "\<forall>n. b n \<in> B" "(\<lambda>n. f (b n)) ----> (f a::pinfreal)"
  shows "f a \<le> SUPR B f"
  unfolding SUPR_def apply(rule Sup_lim[of "\<lambda>n. f (b n)"])
  using assms by auto

lemma SUP_\<omega>_imp:
  assumes "(SUP i. f i) = \<omega>"
  shows "\<exists>i. Real x < f i"
proof (rule ccontr)
  assume "\<not> ?thesis" hence "\<And>i. f i \<le> Real x" by (simp add: not_less)
  hence "(SUP i. f i) \<le> Real x" unfolding SUP_le_iff by auto
  with assms show False by auto
qed

lemma SUPR_mono_lim:
  assumes "\<forall>a\<in>A. \<exists>b. \<forall>n. b n \<in> B \<and> (\<lambda>n. f (b n)) ----> (f a::pinfreal)"
  shows "SUPR A f \<le> SUPR B f"
  unfolding SUPR_def apply(rule Sup_mono_lim)
  apply safe apply(drule assms[rule_format],safe)
  apply(rule_tac x="\<lambda>n. f (b n)" in exI) by auto

lemma real_0_imp_eq_0:
  assumes "x \<noteq> \<omega>" "real x = 0"
  shows "x = 0"
using assms by (cases x) auto

lemma SUPR_mono:
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. f b \<ge> f a"
  shows "SUPR A f \<le> SUPR B f"
  unfolding SUPR_def apply(rule Sup_mono)
  using assms by auto

lemma less_add_Real:
  fixes x :: real
  fixes a b :: pinfreal
  assumes "x \<ge> 0" "a < b"
  shows "a + Real x < b + Real x"
using assms by (cases a, cases b) auto

lemma le_add_Real:
  fixes x :: real
  fixes a b :: pinfreal
  assumes "x \<ge> 0" "a \<le> b"
  shows "a + Real x \<le> b + Real x"
using assms by (cases a, cases b) auto

lemma le_imp_less_pinfreal:
  fixes x :: pinfreal
  assumes "x > 0" "a + x \<le> b" "a \<noteq> \<omega>"
  shows "a < b"
using assms by (cases x, cases a, cases b) auto

lemma pinfreal_INF_minus:
  fixes f :: "nat \<Rightarrow> pinfreal"
  assumes "c \<noteq> \<omega>"
  shows "(INF i. c - f i) = c - (SUP i. f i)"
proof (cases "SUP i. f i")
  case infinite
  from `c \<noteq> \<omega>` obtain x where [simp]: "c = Real x" by (cases c) auto
  from SUP_\<omega>_imp[OF infinite] obtain i where "Real x < f i" by auto
  have "(INF i. c - f i) \<le> c - f i"
    by (auto intro!: complete_lattice_class.INF_leI)
  also have "\<dots> = 0" using `Real x < f i` by (auto simp: minus_pinfreal_eq)
  finally show ?thesis using infinite by auto
next
  case (preal r)
  from `c \<noteq> \<omega>` obtain x where c: "c = Real x" by (cases c) auto

  show ?thesis unfolding c
  proof (rule pinfreal_INFI)
    fix i have "f i \<le> (SUP i. f i)" by (rule le_SUPI) simp
    thus "Real x - (SUP i. f i) \<le> Real x - f i" by (rule pinfreal_minus_le_cancel)
  next
    fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> y \<le> Real x - f i"
    from this[of 0] obtain p where p: "y = Real p" "0 \<le> p"
      by (cases "f 0", cases y, auto split: split_if_asm)
    hence "\<And>i. Real p \<le> Real x - f i" using * by auto
    hence *: "\<And>i. Real x \<le> f i \<Longrightarrow> Real p = 0"
      "\<And>i. f i < Real x \<Longrightarrow> Real p + f i \<le> Real x"
      unfolding pinfreal_le_minus_iff by auto
    show "y \<le> Real x - (SUP i. f i)" unfolding p pinfreal_le_minus_iff
    proof safe
      assume x_less: "Real x \<le> (SUP i. f i)"
      show "Real p = 0"
      proof (rule ccontr)
        assume "Real p \<noteq> 0"
        hence "0 < Real p" by auto
        from Sup_close[OF this, of "range f"]
        obtain i where e: "(SUP i. f i) < f i + Real p"
          using preal unfolding SUPR_def by auto
        hence "Real x \<le> f i + Real p" using x_less by auto
        show False
        proof cases
          assume "\<forall>i. f i < Real x"
          hence "Real p + f i \<le> Real x" using * by auto
          hence "f i + Real p \<le> (SUP i. f i)" using x_less by (auto simp: field_simps)
          thus False using e by auto
        next
          assume "\<not> (\<forall>i. f i < Real x)"
          then obtain i where "Real x \<le> f i" by (auto simp: not_less)
          from *(1)[OF this] show False using `Real p \<noteq> 0` by auto
        qed
      qed
    next
      have "\<And>i. f i \<le> (SUP i. f i)" by (rule complete_lattice_class.le_SUPI) auto
      also assume "(SUP i. f i) < Real x"
      finally have "\<And>i. f i < Real x" by auto
      hence *: "\<And>i. Real p + f i \<le> Real x" using * by auto
      have "Real p \<le> Real x" using *[of 0] by (cases "f 0") (auto split: split_if_asm)

      have SUP_eq: "(SUP i. f i) \<le> Real x - Real p"
      proof (rule SUP_leI)
        fix i show "f i \<le> Real x - Real p" unfolding pinfreal_le_minus_iff
        proof safe
          assume "Real x \<le> Real p"
          with *[of i] show "f i = 0"
            by (cases "f i") (auto split: split_if_asm)
        next
          assume "Real p < Real x"
          show "f i + Real p \<le> Real x" using * by (auto simp: field_simps)
        qed
      qed

      show "Real p + (SUP i. f i) \<le> Real x"
      proof cases
        assume "Real x \<le> Real p"
        with `Real p \<le> Real x` have [simp]: "Real p = Real x" by (rule antisym)
        { fix i have "f i = 0" using *[of i] by (cases "f i") (auto split: split_if_asm) }
        hence "(SUP i. f i) \<le> 0" by (auto intro!: SUP_leI)
        thus ?thesis by simp
      next
        assume "\<not> Real x \<le> Real p" hence "Real p < Real x" unfolding not_le .
        with SUP_eq show ?thesis unfolding pinfreal_le_minus_iff by (auto simp: field_simps)
      qed
    qed
  qed
qed

lemma pinfreal_SUP_minus:
  fixes f :: "nat \<Rightarrow> pinfreal"
  shows "(SUP i. c - f i) = c - (INF i. f i)"
proof (rule pinfreal_SUPI)
  fix i have "(INF i. f i) \<le> f i" by (rule INF_leI) simp
  thus "c - f i \<le> c - (INF i. f i)" by (rule pinfreal_minus_le_cancel)
next
  fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> c - f i \<le> y"
  show "c - (INF i. f i) \<le> y"
  proof (cases y)
    case (preal p)

    show ?thesis unfolding pinfreal_minus_le_iff preal
    proof safe
      assume INF_le_x: "(INF i. f i) \<le> c"
      from * have *: "\<And>i. f i \<le> c \<Longrightarrow> c \<le> Real p + f i"
        unfolding pinfreal_minus_le_iff preal by auto

      have INF_eq: "c - Real p \<le> (INF i. f i)"
      proof (rule le_INFI)
        fix i show "c - Real p \<le> f i" unfolding pinfreal_minus_le_iff
        proof safe
          assume "Real p \<le> c"
          show "c \<le> f i + Real p"
          proof cases
            assume "f i \<le> c" from *[OF this]
            show ?thesis by (simp add: field_simps)
          next
            assume "\<not> f i \<le> c"
            hence "c \<le> f i" by auto
            also have "\<dots> \<le> f i + Real p" by auto
            finally show ?thesis .
          qed
        qed
      qed

      show "c \<le> Real p + (INF i. f i)"
      proof cases
        assume "Real p \<le> c"
        with INF_eq show ?thesis unfolding pinfreal_minus_le_iff by (auto simp: field_simps)
      next
        assume "\<not> Real p \<le> c"
        hence "c \<le> Real p" by auto
        also have "Real p \<le> Real p + (INF i. f i)" by auto
        finally show ?thesis .
      qed
    qed
  qed simp
qed

lemma pinfreal_le_minus_imp_0:
  fixes a b :: pinfreal
  shows "a \<le> a - b \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> a \<noteq> \<omega> \<Longrightarrow> b = 0"
  by (cases a, cases b, auto split: split_if_asm)

lemma lim_INF_le_lim_SUP:
  fixes f :: "nat \<Rightarrow> pinfreal"
  shows "(SUP n. INF m. f (n + m)) \<le> (INF n. SUP m. f (n + m))"
proof (rule complete_lattice_class.SUP_leI, rule complete_lattice_class.le_INFI)
  fix i j show "(INF m. f (i + m)) \<le> (SUP m. f (j + m))"
  proof (cases rule: le_cases)
    assume "i \<le> j"
    have "(INF m. f (i + m)) \<le> f (i + (j - i))" by (rule INF_leI) simp
    also have "\<dots> = f (j + 0)" using `i \<le> j` by auto
    also have "\<dots> \<le> (SUP m. f (j + m))" by (rule le_SUPI) simp
    finally show ?thesis .
  next
    assume "j \<le> i"
    have "(INF m. f (i + m)) \<le> f (i + 0)" by (rule INF_leI) simp
    also have "\<dots> = f (j + (i - j))" using `j \<le> i` by auto
    also have "\<dots> \<le> (SUP m. f (j + m))" by (rule le_SUPI) simp
    finally show ?thesis .
  qed
qed

lemma lim_INF_eq_lim_SUP:
  fixes X :: "nat \<Rightarrow> real"
  assumes "\<And>i. 0 \<le> X i" and "0 \<le> x"
  and lim_INF: "(SUP n. INF m. Real (X (n + m))) = Real x" (is "(SUP n. ?INF n) = _")
  and lim_SUP: "(INF n. SUP m. Real (X (n + m))) = Real x" (is "(INF n. ?SUP n) = _")
  shows "X ----> x"
proof (rule LIMSEQ_I)
  fix r :: real assume "0 < r"
  hence "0 \<le> r" by auto
  from Sup_close[of "Real r" "range ?INF"]
  obtain n where inf: "Real x < ?INF n + Real r"
    unfolding SUPR_def lim_INF[unfolded SUPR_def] using `0 < r` by auto

  from Inf_close[of "range ?SUP" "Real r"]
  obtain n' where sup: "?SUP n' < Real x + Real r"
    unfolding INFI_def lim_SUP[unfolded INFI_def] using `0 < r` by auto

  show "\<exists>N. \<forall>n\<ge>N. norm (X n - x) < r"
  proof (safe intro!: exI[of _ "max n n'"])
    fix m assume "max n n' \<le> m" hence "n \<le> m" "n' \<le> m" by auto

    note inf
    also have "?INF n + Real r \<le> Real (X (n + (m - n))) + Real r"
      by (rule le_add_Real, auto simp: `0 \<le> r` intro: INF_leI)
    finally have up: "x < X m + r"
      using `0 \<le> X m` `0 \<le> x` `0 \<le> r` `n \<le> m` by auto

    have "Real (X (n' + (m - n'))) \<le> ?SUP n'"
      by (auto simp: `0 \<le> r` intro: le_SUPI)
    also note sup
    finally have down: "X m < x + r"
      using `0 \<le> X m` `0 \<le> x` `0 \<le> r` `n' \<le> m` by auto

    show "norm (X m - x) < r" using up down by auto
  qed
qed

lemma Sup_countable_SUPR:
  assumes "Sup A \<noteq> \<omega>" "A \<noteq> {}"
  shows "\<exists> f::nat \<Rightarrow> pinfreal. range f \<subseteq> A \<and> Sup A = SUPR UNIV f"
proof -
  have "\<And>n. 0 < 1 / (of_nat n :: pinfreal)" by auto
  from Sup_close[OF this assms]
  have "\<forall>n. \<exists>x. x \<in> A \<and> Sup A < x + 1 / of_nat n" by blast
  from choice[OF this] obtain f where "range f \<subseteq> A" and
    epsilon: "\<And>n. Sup A < f n + 1 / of_nat n" by blast
  have "SUPR UNIV f = Sup A"
  proof (rule pinfreal_SUPI)
    fix i show "f i \<le> Sup A" using `range f \<subseteq> A`
      by (auto intro!: complete_lattice_class.Sup_upper)
  next
    fix y assume bound: "\<And>i. i \<in> UNIV \<Longrightarrow> f i \<le> y"
    show "Sup A \<le> y"
    proof (rule pinfreal_le_epsilon)
      fix e :: pinfreal assume "0 < e"
      show "Sup A \<le> y + e"
      proof (cases e)
        case (preal r)
        hence "0 < r" using `0 < e` by auto
        then obtain n where *: "inverse (of_nat n) < r" "0 < n"
          using ex_inverse_of_nat_less by auto
        have "Sup A \<le> f n + 1 / of_nat n" using epsilon[of n] by auto
        also have "1 / of_nat n \<le> e" using preal * by (auto simp: real_eq_of_nat)
        with bound have "f n + 1 / of_nat n \<le> y + e" by (rule add_mono) simp
        finally show "Sup A \<le> y + e" .
      qed simp
    qed
  qed
  with `range f \<subseteq> A` show ?thesis by (auto intro!: exI[of _ f])
qed

lemma SUPR_countable_SUPR:
  assumes "SUPR A g \<noteq> \<omega>" "A \<noteq> {}"
  shows "\<exists> f::nat \<Rightarrow> pinfreal. range f \<subseteq> g`A \<and> SUPR A g = SUPR UNIV f"
proof -
  have "Sup (g`A) \<noteq> \<omega>" "g`A \<noteq> {}" using assms unfolding SUPR_def by auto
  from Sup_countable_SUPR[OF this]
  show ?thesis unfolding SUPR_def .
qed

lemma pinfreal_setsum_subtractf:
  assumes "\<And>i. i\<in>A \<Longrightarrow> g i \<le> f i" and "\<And>i. i\<in>A \<Longrightarrow> f i \<noteq> \<omega>"
  shows "(\<Sum>i\<in>A. f i - g i) = (\<Sum>i\<in>A. f i) - (\<Sum>i\<in>A. g i)"
proof cases
  assume "finite A" from this assms show ?thesis
  proof induct
    case (insert x A)
    hence hyp: "(\<Sum>i\<in>A. f i - g i) = (\<Sum>i\<in>A. f i) - (\<Sum>i\<in>A. g i)"
      by auto
    { fix i assume *: "i \<in> insert x A"
      hence "g i \<le> f i" using insert by simp
      also have "f i < \<omega>" using * insert by (simp add: pinfreal_less_\<omega>)
      finally have "g i \<noteq> \<omega>" by (simp add: pinfreal_less_\<omega>) }
    hence "setsum g A \<noteq> \<omega>" "g x \<noteq> \<omega>" by (auto simp: setsum_\<omega>)
    moreover have "setsum f A \<noteq> \<omega>" "f x \<noteq> \<omega>" using insert by (auto simp: setsum_\<omega>)
    moreover have "g x \<le> f x" using insert by auto
    moreover have "(\<Sum>i\<in>A. g i) \<le> (\<Sum>i\<in>A. f i)" using insert by (auto intro!: setsum_mono)
    ultimately show ?case using `finite A` `x \<notin> A` hyp
      by (auto simp: pinfreal_noteq_omega_Ex)
  qed simp
qed simp

lemma real_of_pinfreal_diff:
  "y \<le> x \<Longrightarrow> x \<noteq> \<omega> \<Longrightarrow> real x - real y = real (x - y)"
  by (cases x, cases y) auto

lemma psuminf_minus:
  assumes ord: "\<And>i. g i \<le> f i" and fin: "psuminf g \<noteq> \<omega>" "psuminf f \<noteq> \<omega>"
  shows "(\<Sum>\<^isub>\<infinity> i. f i - g i) = psuminf f - psuminf g"
proof -
  have [simp]: "\<And>i. f i \<noteq> \<omega>" using fin by (auto intro: psuminf_\<omega>)
  from fin have "(\<lambda>x. real (f x)) sums real (\<Sum>\<^isub>\<infinity>x. f x)"
    and "(\<lambda>x. real (g x)) sums real (\<Sum>\<^isub>\<infinity>x. g x)"
    by (auto intro: psuminf_imp_suminf)
  from sums_diff[OF this]
  have "(\<lambda>n. real (f n - g n)) sums (real ((\<Sum>\<^isub>\<infinity>x. f x) - (\<Sum>\<^isub>\<infinity>x. g x)))" using fin ord
    by (subst (asm) (1 2) real_of_pinfreal_diff) (auto simp: psuminf_\<omega> psuminf_le)
  hence "(\<Sum>\<^isub>\<infinity> i. Real (real (f i - g i))) = Real (real ((\<Sum>\<^isub>\<infinity>x. f x) - (\<Sum>\<^isub>\<infinity>x. g x)))"
    by (rule suminf_imp_psuminf) simp
  thus ?thesis using fin by (simp add: Real_real psuminf_\<omega>)
qed

lemma INF_eq_LIMSEQ:
  assumes "mono (\<lambda>i. - f i)" and "\<And>n. 0 \<le> f n" and "0 \<le> x"
  shows "(INF n. Real (f n)) = Real x \<longleftrightarrow> f ----> x"
proof
  assume x: "(INF n. Real (f n)) = Real x"
  { fix n
    have "Real x \<le> Real (f n)" using x[symmetric] by (auto intro: INF_leI)
    hence "x \<le> f n" using assms by simp
    hence "\<bar>f n - x\<bar> = f n - x" by auto }
  note abs_eq = this
  show "f ----> x"
  proof (rule LIMSEQ_I)
    fix r :: real assume "0 < r"
    show "\<exists>no. \<forall>n\<ge>no. norm (f n - x) < r"
    proof (rule ccontr)
      assume *: "\<not> ?thesis"
      { fix N
        from * obtain n where *: "N \<le> n" "r \<le> f n - x"
          using abs_eq by (auto simp: not_less)
        hence "x + r \<le> f n" by auto
        also have "f n \<le> f N" using `mono (\<lambda>i. - f i)` * by (auto dest: monoD)
        finally have "Real (x + r) \<le> Real (f N)" using `0 \<le> f N` by auto }
      hence "Real x < Real (x + r)"
        and "Real (x + r) \<le> (INF n. Real (f n))" using `0 < r` `0 \<le> x` by (auto intro: le_INFI)
      hence "Real x < (INF n. Real (f n))" by (rule less_le_trans)
      thus False using x by auto
    qed
  qed
next
  assume "f ----> x"
  show "(INF n. Real (f n)) = Real x"
  proof (rule pinfreal_INFI)
    fix n
    from decseq_le[OF _ `f ----> x`] assms
    show "Real x \<le> Real (f n)" unfolding decseq_eq_incseq incseq_mono by auto
  next
    fix y assume *: "\<And>n. n\<in>UNIV \<Longrightarrow> y \<le> Real (f n)"
    thus "y \<le> Real x"
    proof (cases y)
      case (preal r)
      with * have "\<exists>N. \<forall>n\<ge>N. r \<le> f n" using assms by fastsimp
      from LIMSEQ_le_const[OF `f ----> x` this]
      show "y \<le> Real x" using `0 \<le> x` preal by auto
    qed simp
  qed
qed

lemma INFI_bound:
  assumes "\<forall>N. x \<le> f N"
  shows "x \<le> (INF n. f n)"
  using assms by (simp add: INFI_def le_Inf_iff)

lemma LIMSEQ_imp_lim_INF:
  assumes pos: "\<And>i. 0 \<le> X i" and lim: "X ----> x"
  shows "(SUP n. INF m. Real (X (n + m))) = Real x"
proof -
  have "0 \<le> x" using assms by (auto intro!: LIMSEQ_le_const)

  have "\<And>n. (INF m. Real (X (n + m))) \<le> Real (X (n + 0))" by (rule INF_leI) simp
  also have "\<And>n. Real (X (n + 0)) < \<omega>" by simp
  finally have "\<forall>n. \<exists>r\<ge>0. (INF m. Real (X (n + m))) = Real r"
    by (auto simp: pinfreal_less_\<omega> pinfreal_noteq_omega_Ex)
  from choice[OF this] obtain r where r: "\<And>n. (INF m. Real (X (n + m))) = Real (r n)" "\<And>n. 0 \<le> r n"
    by auto

  show ?thesis unfolding r
  proof (subst SUP_eq_LIMSEQ)
    show "mono r" unfolding mono_def
    proof safe
      fix x y :: nat assume "x \<le> y"
      have "Real (r x) \<le> Real (r y)" unfolding r(1)[symmetric] using pos
      proof (safe intro!: INF_mono bexI)
        fix m have "x + (m + y - x) = y + m"
          using `x \<le> y` by auto
        thus "Real (X (x + (m + y - x))) \<le> Real (X (y + m))" by simp
      qed simp
      thus "r x \<le> r y" using r by auto
    qed
    show "\<And>n. 0 \<le> r n" by fact
    show "0 \<le> x" by fact
    show "r ----> x"
    proof (rule LIMSEQ_I)
      fix e :: real assume "0 < e"
      hence "0 < e/2" by auto
      from LIMSEQ_D[OF lim this] obtain N where *: "\<And>n. N \<le> n \<Longrightarrow> \<bar>X n - x\<bar> < e/2"
        by auto
      show "\<exists>N. \<forall>n\<ge>N. norm (r n - x) < e"
      proof (safe intro!: exI[of _ N])
        fix n assume "N \<le> n"
        show "norm (r n - x) < e"
        proof cases
          assume "r n < x"
          have "x - r n \<le> e/2"
          proof cases
            assume e: "e/2 \<le> x"
            have "Real (x - e/2) \<le> Real (r n)" unfolding r(1)[symmetric]
            proof (rule le_INFI)
              fix m show "Real (x - e / 2) \<le> Real (X (n + m))"
                using *[of "n + m"] `N \<le> n`
                using pos by (auto simp: field_simps abs_real_def split: split_if_asm)
            qed
            with e show ?thesis using pos `0 \<le> x` r(2) by auto
          next
            assume "\<not> e/2 \<le> x" hence "x - e/2 < 0" by auto
            with `0 \<le> r n` show ?thesis by auto
          qed
          with `r n < x` show ?thesis by simp
        next
          assume e: "\<not> r n < x"
          have "Real (r n) \<le> Real (X (n + 0))" unfolding r(1)[symmetric]
            by (rule INF_leI) simp
          hence "r n - x \<le> X n - x" using r pos by auto
          also have "\<dots> < e/2" using *[OF `N \<le> n`] by (auto simp: field_simps abs_real_def split: split_if_asm)
          finally have "r n - x < e" using `0 < e` by auto
          with e show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma real_of_pinfreal_strict_mono_iff:
  "real a < real b \<longleftrightarrow> (b \<noteq> \<omega> \<and> ((a = \<omega> \<and> 0 < b) \<or> (a < b)))"
proof (cases a)
  case infinite thus ?thesis by (cases b) auto
next
  case preal thus ?thesis by (cases b) auto
qed

lemma real_of_pinfreal_mono_iff:
  "real a \<le> real b \<longleftrightarrow> (a = \<omega> \<or> (b \<noteq> \<omega> \<and> a \<le> b) \<or> (b = \<omega> \<and> a = 0))"
proof (cases a)
  case infinite thus ?thesis by (cases b) auto
next
  case preal thus ?thesis by (cases b)  auto
qed

lemma ex_pinfreal_inverse_of_nat_Suc_less:
  fixes e :: pinfreal assumes "0 < e" shows "\<exists>n. inverse (of_nat (Suc n)) < e"
proof (cases e)
  case (preal r)
  with `0 < e` ex_inverse_of_nat_Suc_less[of r]
  obtain n where "inverse (of_nat (Suc n)) < r" by auto
  with preal show ?thesis
    by (auto simp: real_eq_of_nat[symmetric])
qed auto

lemma Lim_eq_Sup_mono:
  fixes u :: "nat \<Rightarrow> pinfreal" assumes "mono u"
  shows "u ----> (SUP i. u i)"
proof -
  from lim_pinfreal_increasing[of u] `mono u`
  obtain l where l: "u ----> l" unfolding mono_def by auto
  from SUP_Lim_pinfreal[OF _ this] `mono u`
  have "(SUP i. u i) = l" unfolding mono_def by auto
  with l show ?thesis by simp
qed

lemma isotone_Lim:
  fixes x :: pinfreal assumes "u \<up> x"
  shows "u ----> x" (is ?lim) and "mono u" (is ?mono)
proof -
  show ?mono using assms unfolding mono_iff_le_Suc isoton_def by auto
  from Lim_eq_Sup_mono[OF this] `u \<up> x`
  show ?lim unfolding isoton_def by simp
qed

lemma isoton_iff_Lim_mono:
  fixes u :: "nat \<Rightarrow> pinfreal"
  shows "u \<up> x \<longleftrightarrow> (mono u \<and> u ----> x)"
proof safe
  assume "mono u" and x: "u ----> x"
  with SUP_Lim_pinfreal[OF _ x]
  show "u \<up> x" unfolding isoton_def
    using `mono u`[unfolded mono_def]
    using `mono u`[unfolded mono_iff_le_Suc]
    by auto
qed (auto dest: isotone_Lim)

lemma pinfreal_inverse_inverse[simp]:
  fixes x :: pinfreal
  shows "inverse (inverse x) = x"
  by (cases x) auto

lemma atLeastAtMost_omega_eq_atLeast:
  shows "{a .. \<omega>} = {a ..}"
by auto

lemma atLeast0AtMost_eq_atMost: "{0 :: pinfreal .. a} = {.. a}" by auto

lemma greaterThan_omega_Empty: "{\<omega> <..} = {}" by auto

lemma lessThan_0_Empty: "{..< 0 :: pinfreal} = {}" by auto

end
