(*  Title:      HOL/Library/Set_Algebras.thy
    Author:     Jeremy Avigad
    Author:     Kevin Donnelly
    Author:     Florian Haftmann, TUM
*)

section \<open>Algebraic operations on sets\<close>

theory Set_Algebras
  imports Main
begin

text \<open>
  This library lifts operations like addition and multiplication to sets. It
  was designed to support asymptotic calculations for the now-obsolete BigO theory,
  but has other uses.
\<close>

instantiation set :: (plus) plus
begin

definition plus_set :: "'a::plus set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where set_plus_def: "A + B = {c. \<exists>a\<in>A. \<exists>b\<in>B. c = a + b}"

instance ..

end

instantiation set :: (times) times
begin

definition times_set :: "'a::times set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where set_times_def: "A * B = {c. \<exists>a\<in>A. \<exists>b\<in>B. c = a * b}"

instance ..

end

instantiation set :: (zero) zero
begin

definition set_zero[simp]: "(0::'a::zero set) = {0}"

instance ..

end

instantiation set :: (one) one
begin

definition set_one[simp]: "(1::'a::one set) = {1}"

instance ..

end

definition elt_set_plus :: "'a::plus \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl \<open>+o\<close> 70)
  where "a +o B = {c. \<exists>b\<in>B. c = a + b}"

definition elt_set_times :: "'a::times \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl \<open>*o\<close> 80)
  where "a *o B = {c. \<exists>b\<in>B. c = a * b}"

abbreviation (input) elt_set_eq :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infix \<open>=o\<close> 50)
  where "x =o A \<equiv> x \<in> A"

instance set :: (semigroup_add) semigroup_add
  by standard (force simp add: set_plus_def add.assoc)

instance set :: (ab_semigroup_add) ab_semigroup_add
  by standard (force simp add: set_plus_def add.commute)

instance set :: (monoid_add) monoid_add
  by standard (simp_all add: set_plus_def)

instance set :: (comm_monoid_add) comm_monoid_add
  by standard (simp_all add: set_plus_def)

instance set :: (semigroup_mult) semigroup_mult
  by standard (force simp add: set_times_def mult.assoc)

instance set :: (ab_semigroup_mult) ab_semigroup_mult
  by standard (force simp add: set_times_def mult.commute)

instance set :: (monoid_mult) monoid_mult
  by standard (simp_all add: set_times_def)

instance set :: (comm_monoid_mult) comm_monoid_mult
  by standard (simp_all add: set_times_def)

lemma sumset_empty [simp]: "A + {} = {}" "{} + A = {}"
  by (auto simp: set_plus_def)

lemma Un_set_plus: "(A \<union> B) + C = (A+C) \<union> (B+C)" and set_plus_Un: "C + (A \<union> B) = (C+A) \<union> (C+B)"
  by (auto simp: set_plus_def)

lemma 
  fixes A :: "'a::comm_monoid_add set"
  shows insert_set_plus: "(insert a A) + B = (A+B) \<union> (((+)a) ` B)" and set_plus_insert: "B + (insert a A) = (B+A) \<union> (((+)a) ` B)"
  using add.commute by (auto simp: set_plus_def)

lemma set_add_0 [simp]:
  fixes A :: "'a::comm_monoid_add set"
  shows "{0} + A = A"
  by (metis comm_monoid_add_class.add_0 set_zero)

lemma set_add_0_right [simp]:
  fixes A :: "'a::comm_monoid_add set"
  shows "A + {0} = A"
  by (metis add.comm_neutral set_zero)

lemma card_plus_sing:
  fixes A :: "'a::ab_group_add set"
  shows "card (A + {a}) = card A"
proof (rule bij_betw_same_card)
  show "bij_betw ((+) (-a)) (A + {a}) A"
    by (fastforce simp: set_plus_def bij_betw_def image_iff)
qed

lemma set_plus_intro [intro]: "a \<in> C \<Longrightarrow> b \<in> D \<Longrightarrow> a + b \<in> C + D"
  by (auto simp add: set_plus_def)

lemma set_plus_elim:
  assumes "x \<in> A + B"
  obtains a b where "x = a + b" and "a \<in> A" and "b \<in> B"
  using assms unfolding set_plus_def by fast

lemma set_plus_intro2 [intro]: "b \<in> C \<Longrightarrow> a + b \<in> a +o C"
  by (auto simp add: elt_set_plus_def)

lemma set_plus_rearrange: "(a +o C) + (b +o D) = (a + b) +o (C + D)"
  for a b :: "'a::comm_monoid_add"
    by (auto simp: elt_set_plus_def set_plus_def; metis group_cancel.add1 group_cancel.add2)

lemma set_plus_rearrange2: "a +o (b +o C) = (a + b) +o C"
  for a b :: "'a::semigroup_add"
  by (auto simp add: elt_set_plus_def add.assoc)

lemma set_plus_rearrange3: "(a +o B) + C = a +o (B + C)"
  for a :: "'a::semigroup_add"
  by (auto simp add: elt_set_plus_def set_plus_def; metis add.assoc)

theorem set_plus_rearrange4: "C + (a +o D) = a +o (C + D)"
  for a :: "'a::comm_monoid_add"
  by (metis add.commute set_plus_rearrange3)

lemmas set_plus_rearranges = set_plus_rearrange set_plus_rearrange2
  set_plus_rearrange3 set_plus_rearrange4

lemma set_plus_mono [intro!]: "C \<subseteq> D \<Longrightarrow> a +o C \<subseteq> a +o D"
  by (auto simp add: elt_set_plus_def)

lemma set_plus_mono2 [intro]: "C \<subseteq> D \<Longrightarrow> E \<subseteq> F \<Longrightarrow> C + E \<subseteq> D + F"
  for C D E F :: "'a::plus set"
  by (auto simp add: set_plus_def)

lemma set_plus_mono3 [intro]: "a \<in> C \<Longrightarrow> a +o D \<subseteq> C + D"
  by (auto simp add: elt_set_plus_def set_plus_def)

lemma set_plus_mono4 [intro]: "a \<in> C \<Longrightarrow> a +o D \<subseteq> D + C"
  for a :: "'a::comm_monoid_add"
  by (auto simp add: elt_set_plus_def set_plus_def ac_simps)

lemma set_plus_mono5: "a \<in> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> a +o B \<subseteq> C + D"
  using order_subst2 by blast

lemma set_plus_mono_b: "C \<subseteq> D \<Longrightarrow> x \<in> a +o C \<Longrightarrow> x \<in> a +o D"
  using set_plus_mono by blast

lemma set_zero_plus [simp]: "0 +o C = C"
  for C :: "'a::comm_monoid_add set"
  by (auto simp add: elt_set_plus_def)

lemma set_zero_plus2: "0 \<in> A \<Longrightarrow> B \<subseteq> A + B"
  for A B :: "'a::comm_monoid_add set"
  using set_plus_intro by fastforce

lemma set_plus_imp_minus: "a \<in> b +o C \<Longrightarrow> a - b \<in> C"
  for a b :: "'a::ab_group_add"
  by (auto simp add: elt_set_plus_def ac_simps)

lemma set_minus_imp_plus: "a - b \<in> C \<Longrightarrow> a \<in> b +o C"
  for a b :: "'a::ab_group_add"
  by (metis add.commute diff_add_cancel set_plus_intro2)

lemma set_minus_plus: "a - b \<in> C \<longleftrightarrow> a \<in> b +o C"
  for a b :: "'a::ab_group_add"
  by (meson set_minus_imp_plus set_plus_imp_minus)

lemma set_times_intro [intro]: "a \<in> C \<Longrightarrow> b \<in> D \<Longrightarrow> a * b \<in> C * D"
  by (auto simp add: set_times_def)

lemma set_times_elim:
  assumes "x \<in> A * B"
  obtains a b where "x = a * b" and "a \<in> A" and "b \<in> B"
  using assms unfolding set_times_def by fast

lemma set_times_intro2 [intro!]: "b \<in> C \<Longrightarrow> a * b \<in> a *o C"
  by (auto simp add: elt_set_times_def)

lemma set_times_rearrange: "(a *o C) * (b *o D) = (a * b) *o (C * D)"
  for a b :: "'a::comm_monoid_mult"
  by (auto simp add: elt_set_times_def set_times_def; metis mult.assoc mult.left_commute)

lemma set_times_rearrange2: "a *o (b *o C) = (a * b) *o C"
  for a b :: "'a::semigroup_mult"
  by (auto simp add: elt_set_times_def mult.assoc)

lemma set_times_rearrange3: "(a *o B) * C = a *o (B * C)"
  for a :: "'a::semigroup_mult"
  by (auto simp add: elt_set_times_def set_times_def; metis mult.assoc)

theorem set_times_rearrange4: "C * (a *o D) = a *o (C * D)"
  for a :: "'a::comm_monoid_mult"
  by (metis mult.commute set_times_rearrange3)

lemmas set_times_rearranges = set_times_rearrange set_times_rearrange2
  set_times_rearrange3 set_times_rearrange4

lemma set_times_mono [intro]: "C \<subseteq> D \<Longrightarrow> a *o C \<subseteq> a *o D"
  by (auto simp add: elt_set_times_def)

lemma set_times_mono2 [intro]: "C \<subseteq> D \<Longrightarrow> E \<subseteq> F \<Longrightarrow> C * E \<subseteq> D * F"
  for C D E F :: "'a::times set"
  by (auto simp add: set_times_def)

lemma set_times_mono3 [intro]: "a \<in> C \<Longrightarrow> a *o D \<subseteq> C * D"
  by (auto simp add: elt_set_times_def set_times_def)

lemma set_times_mono4 [intro]: "a \<in> C \<Longrightarrow> a *o D \<subseteq> D * C"
  for a :: "'a::comm_monoid_mult"
  by (auto simp add: elt_set_times_def set_times_def ac_simps)

lemma set_times_mono5: "a \<in> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> a *o B \<subseteq> C * D"
  by (meson dual_order.trans set_times_mono set_times_mono3)

lemma set_one_times [simp]: "1 *o C = C"
  for C :: "'a::comm_monoid_mult set"
  by (auto simp add: elt_set_times_def)

lemma set_times_plus_distrib: "a *o (b +o C) = (a * b) +o (a *o C)"
  for a b :: "'a::semiring"
  by (auto simp add: elt_set_plus_def elt_set_times_def ring_distribs)

lemma set_times_plus_distrib2: "a *o (B + C) = (a *o B) + (a *o C)"
  for a :: "'a::semiring"
  by (auto simp: set_plus_def elt_set_times_def; metis distrib_left)

lemma set_times_plus_distrib3: "(a +o C) * D \<subseteq> a *o D + C * D"
  for a :: "'a::semiring"
  using distrib_right 
  by (fastforce simp add: elt_set_plus_def elt_set_times_def set_times_def set_plus_def)

lemmas set_times_plus_distribs =
  set_times_plus_distrib
  set_times_plus_distrib2

lemma set_neg_intro: "a \<in> (- 1) *o C \<Longrightarrow> - a \<in> C"
  for a :: "'a::ring_1"
  by (auto simp add: elt_set_times_def)

lemma set_neg_intro2: "a \<in> C \<Longrightarrow> - a \<in> (- 1) *o C"
  for a :: "'a::ring_1"
  by (auto simp add: elt_set_times_def)

lemma set_plus_image: "S + T = (\<lambda>(x, y). x + y) ` (S \<times> T)"
  by (fastforce simp: set_plus_def image_iff)

lemma set_times_image: "S * T = (\<lambda>(x, y). x * y) ` (S \<times> T)"
  by (fastforce simp: set_times_def image_iff)

lemma finite_set_plus: "finite s \<Longrightarrow> finite t \<Longrightarrow> finite (s + t)"
  by (simp add: set_plus_image)

lemma finite_set_times: "finite s \<Longrightarrow> finite t \<Longrightarrow> finite (s * t)"
  by (simp add: set_times_image)

lemma set_sum_alt:
  assumes fin: "finite I"
  shows "sum S I = {sum s I |s. \<forall>i\<in>I. s i \<in> S i}"
    (is "_ = ?sum I")
  using fin
proof induct
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "sum S (insert x F) = S x + ?sum F"
    using insert.hyps by auto
  also have "\<dots> = {s x + sum s F |s. \<forall> i\<in>insert x F. s i \<in> S i}"
    unfolding set_plus_def
  proof safe
    fix y s
    assume "y \<in> S x" "\<forall>i\<in>F. s i \<in> S i"
    then show "\<exists>s'. y + sum s F = s' x + sum s' F \<and> (\<forall>i\<in>insert x F. s' i \<in> S i)"
      using insert.hyps
      by (intro exI[of _ "\<lambda>i. if i \<in> F then s i else y"]) (auto simp add: set_plus_def)
  qed auto
  finally show ?case
    using insert.hyps by auto
qed

lemma sum_set_cond_linear:
  fixes f :: "'a::comm_monoid_add set \<Rightarrow> 'b::comm_monoid_add set"
  assumes [intro!]: "\<And>A B. P A  \<Longrightarrow> P B  \<Longrightarrow> P (A + B)" "P {0}"
    and f: "\<And>A B. P A  \<Longrightarrow> P B \<Longrightarrow> f (A + B) = f A + f B" "f {0} = {0}"
  assumes all: "\<And>i. i \<in> I \<Longrightarrow> P (S i)"
  shows "f (sum S I) = sum (f \<circ> S) I"
proof (cases "finite I")
  case True
  from this all show ?thesis
  proof induct
    case empty
    then show ?case by (auto intro!: f)
  next
    case (insert x F)
    from \<open>finite F\<close> \<open>\<And>i. i \<in> insert x F \<Longrightarrow> P (S i)\<close> have "P (sum S F)"
      by induct auto
    with insert show ?case
      by (simp, subst f) auto
  qed
next
  case False
  then show ?thesis by (auto intro!: f)
qed

lemma sum_set_linear:
  fixes f :: "'a::comm_monoid_add set \<Rightarrow> 'b::comm_monoid_add set"
  assumes "\<And>A B. f(A) + f(B) = f(A + B)" "f {0} = {0}"
  shows "f (sum S I) = sum (f \<circ> S) I"
  using sum_set_cond_linear[of "\<lambda>x. True" f I S] assms by auto

lemma set_times_Un_distrib:
  "A * (B \<union> C) = A * B \<union> A * C"
  "(A \<union> B) * C = A * C \<union> B * C"
  by (auto simp: set_times_def)

lemma set_times_UNION_distrib:
  "A * \<Union>(M ` I) = (\<Union>i\<in>I. A * M i)"
  "\<Union>(M ` I) * A = (\<Union>i\<in>I. M i * A)"
  by (auto simp: set_times_def)

end
