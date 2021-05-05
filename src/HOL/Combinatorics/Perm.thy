(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Permutations as abstract type\<close>

theory Perm
  imports
    Transposition
begin

text \<open>
  This theory introduces basics about permutations, i.e. almost
  everywhere fix bijections.  But it is by no means complete.
  Grieviously missing are cycles since these would require more
  elaboration, e.g. the concept of distinct lists equivalent
  under rotation, which maybe would also deserve its own theory.
  But see theory \<open>src/HOL/ex/Perm_Fragments.thy\<close> for
  fragments on that.
\<close>

subsection \<open>Abstract type of permutations\<close>

typedef 'a perm = "{f :: 'a \<Rightarrow> 'a. bij f \<and> finite {a. f a \<noteq> a}}"
  morphisms "apply" Perm
proof
  show "id \<in> ?perm" by simp
qed

setup_lifting type_definition_perm

notation "apply" (infixl "\<langle>$\<rangle>" 999)

lemma bij_apply [simp]:
  "bij (apply f)"
  using "apply" [of f] by simp

lemma perm_eqI:
  assumes "\<And>a. f \<langle>$\<rangle> a = g \<langle>$\<rangle> a"
  shows "f = g"
  using assms by transfer (simp add: fun_eq_iff)

lemma perm_eq_iff:
  "f = g \<longleftrightarrow> (\<forall>a. f \<langle>$\<rangle> a = g \<langle>$\<rangle> a)"
  by (auto intro: perm_eqI)

lemma apply_inj:
  "f \<langle>$\<rangle> a = f \<langle>$\<rangle> b \<longleftrightarrow> a = b"
  by (rule inj_eq) (rule bij_is_inj, simp)

lift_definition affected :: "'a perm \<Rightarrow> 'a set"
  is "\<lambda>f. {a. f a \<noteq> a}" .

lemma in_affected:
  "a \<in> affected f \<longleftrightarrow> f \<langle>$\<rangle> a \<noteq> a"
  by transfer simp

lemma finite_affected [simp]:
  "finite (affected f)"
  by transfer simp

lemma apply_affected [simp]:
  "f \<langle>$\<rangle> a \<in> affected f \<longleftrightarrow> a \<in> affected f"
proof transfer
  fix f :: "'a \<Rightarrow> 'a" and a :: 'a
  assume "bij f \<and> finite {b. f b \<noteq> b}"
  then have "bij f" by simp
  interpret bijection f by standard (rule \<open>bij f\<close>)
  have "f a \<in> {a. f a = a} \<longleftrightarrow> a \<in> {a. f a = a}" (is "?P \<longleftrightarrow> ?Q")
    by auto
  then show "f a \<in> {a. f a \<noteq> a} \<longleftrightarrow> a \<in> {a. f a \<noteq> a}"
    by simp
qed

lemma card_affected_not_one:
  "card (affected f) \<noteq> 1"
proof
  interpret bijection "apply f"
    by standard (rule bij_apply)
  assume "card (affected f) = 1"
  then obtain a where *: "affected f = {a}"
    by (rule card_1_singletonE)
  then have **: "f \<langle>$\<rangle> a \<noteq> a"
    by (simp flip: in_affected)
  with * have "f \<langle>$\<rangle> a \<notin> affected f"
    by simp
  then have "f \<langle>$\<rangle> (f \<langle>$\<rangle> a) = f \<langle>$\<rangle> a"
    by (simp add: in_affected)
  then have "inv (apply f) (f \<langle>$\<rangle> (f \<langle>$\<rangle> a)) = inv (apply f) (f \<langle>$\<rangle> a)"
    by simp
  with ** show False by simp
qed


subsection \<open>Identity, composition and inversion\<close>

instantiation Perm.perm :: (type) "{monoid_mult, inverse}"
begin

lift_definition one_perm :: "'a perm"
  is id
  by simp

lemma apply_one [simp]:
  "apply 1 = id"
  by (fact one_perm.rep_eq)

lemma affected_one [simp]:
  "affected 1 = {}"
  by transfer simp

lemma affected_empty_iff [simp]:
  "affected f = {} \<longleftrightarrow> f = 1"
  by transfer auto

lift_definition times_perm :: "'a perm \<Rightarrow> 'a perm \<Rightarrow> 'a perm"
  is comp
proof
  fix f g :: "'a \<Rightarrow> 'a"
  assume "bij f \<and> finite {a. f a \<noteq> a}"
    "bij g \<and>finite {a. g a \<noteq> a}"
  then have "finite ({a. f a \<noteq> a} \<union> {a. g a \<noteq> a})"
    by simp
  moreover have "{a. (f \<circ> g) a \<noteq> a} \<subseteq> {a. f a \<noteq> a} \<union> {a. g a \<noteq> a}"
    by auto
  ultimately show "finite {a. (f \<circ> g) a \<noteq> a}"
    by (auto intro: finite_subset)
qed (auto intro: bij_comp)

lemma apply_times:
  "apply (f * g) = apply f \<circ> apply g"
  by (fact times_perm.rep_eq)

lemma apply_sequence:
  "f \<langle>$\<rangle> (g \<langle>$\<rangle> a) = apply (f * g) a"
  by (simp add: apply_times)

lemma affected_times [simp]:
  "affected (f * g) \<subseteq> affected f \<union> affected g"
  by transfer auto

lift_definition inverse_perm :: "'a perm \<Rightarrow> 'a perm"
  is inv
proof transfer
  fix f :: "'a \<Rightarrow> 'a" and a
  assume "bij f \<and> finite {b. f b \<noteq> b}"
  then have "bij f" and fin: "finite {b. f b \<noteq> b}"
    by auto
  interpret bijection f by standard (rule \<open>bij f\<close>)
  from fin show "bij (inv f) \<and> finite {a. inv f a \<noteq> a}"
    by (simp add: bij_inv)
qed

instance
  by standard (transfer; simp add: comp_assoc)+

end

lemma apply_inverse:
  "apply (inverse f) = inv (apply f)"
  by (fact inverse_perm.rep_eq)

lemma affected_inverse [simp]:
  "affected (inverse f) = affected f"
proof transfer
  fix f :: "'a \<Rightarrow> 'a" and a
  assume "bij f \<and> finite {b. f b \<noteq> b}"
  then have "bij f" by simp
  interpret bijection f by standard (rule \<open>bij f\<close>)
  show "{a. inv f a \<noteq> a} = {a. f a \<noteq> a}"
    by simp
qed

global_interpretation perm: group times "1::'a perm" inverse
proof
  fix f :: "'a perm"
  show "1 * f = f"
    by transfer simp
  show "inverse f * f = 1"
  proof transfer
    fix f :: "'a \<Rightarrow> 'a" and a
    assume "bij f \<and> finite {b. f b \<noteq> b}"
    then have "bij f" by simp
    interpret bijection f by standard (rule \<open>bij f\<close>)
    show "inv f \<circ> f = id"
      by simp
  qed
qed

declare perm.inverse_distrib_swap [simp]

lemma perm_mult_commute:
  assumes "affected f \<inter> affected g = {}"
  shows "g * f = f * g"
proof (rule perm_eqI)
  fix a
  from assms have *: "a \<in> affected f \<Longrightarrow> a \<notin> affected g"
    "a \<in> affected g \<Longrightarrow> a \<notin> affected f" for a
    by auto
  consider "a \<in> affected f \<and> a \<notin> affected g
        \<and> f \<langle>$\<rangle> a \<in> affected f"
    | "a \<notin> affected f \<and> a \<in> affected g
        \<and> f \<langle>$\<rangle> a \<notin> affected f"
    | "a \<notin> affected f \<and> a \<notin> affected g"
    using assms by auto
  then show "(g * f) \<langle>$\<rangle> a = (f * g) \<langle>$\<rangle> a"
  proof cases
    case 1
    with * have "f \<langle>$\<rangle> a \<notin> affected g"
      by auto
    with 1 show ?thesis by (simp add: in_affected apply_times)
  next
    case 2
    with * have "g \<langle>$\<rangle> a \<notin> affected f"
      by auto
    with 2 show ?thesis by (simp add: in_affected apply_times)
  next
    case 3
    then show ?thesis by (simp add: in_affected apply_times)
  qed
qed

lemma apply_power:
  "apply (f ^ n) = apply f ^^ n"
  by (induct n) (simp_all add: apply_times)

lemma perm_power_inverse:
  "inverse f ^ n = inverse ((f :: 'a perm) ^ n)"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then show ?case
    unfolding power_Suc2 [of f] by simp
qed


subsection \<open>Orbit and order of elements\<close>

definition orbit :: "'a perm \<Rightarrow> 'a \<Rightarrow> 'a set"
where
  "orbit f a = range (\<lambda>n. (f ^ n) \<langle>$\<rangle> a)"

lemma in_orbitI:
  assumes "(f ^ n) \<langle>$\<rangle> a = b"
  shows "b \<in> orbit f a"
  using assms by (auto simp add: orbit_def)

lemma apply_power_self_in_orbit [simp]:
  "(f ^ n) \<langle>$\<rangle> a \<in> orbit f a"
  by (rule in_orbitI) rule

lemma in_orbit_self [simp]:
  "a \<in> orbit f a"
  using apply_power_self_in_orbit [of _ 0] by simp

lemma apply_self_in_orbit [simp]:
  "f \<langle>$\<rangle> a \<in> orbit f a"
  using apply_power_self_in_orbit [of _ 1] by simp

lemma orbit_not_empty [simp]:
  "orbit f a \<noteq> {}"
  using in_orbit_self [of a f] by blast

lemma not_in_affected_iff_orbit_eq_singleton:
  "a \<notin> affected f \<longleftrightarrow> orbit f a = {a}" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then have "f \<langle>$\<rangle> a = a"
    by (simp add: in_affected)
  then have "(f ^ n) \<langle>$\<rangle> a = a" for n
    by (induct n) (simp_all add: apply_times)
  then show ?Q
    by (auto simp add: orbit_def)
next
  assume ?Q
  then show ?P
    by (auto simp add: orbit_def in_affected dest: range_eq_singletonD [of _ _ 1])
qed

definition order :: "'a perm \<Rightarrow> 'a \<Rightarrow> nat"
where
  "order f = card \<circ> orbit f"

lemma orbit_subset_eq_affected:
  assumes "a \<in> affected f"
  shows "orbit f a \<subseteq> affected f"
proof (rule ccontr)
  assume "\<not> orbit f a \<subseteq> affected f"
  then obtain b where "b \<in> orbit f a" and "b \<notin> affected f"
    by auto
  then have "b \<in> range (\<lambda>n. (f ^ n) \<langle>$\<rangle> a)"
    by (simp add: orbit_def)
  then obtain n where "b = (f ^ n) \<langle>$\<rangle> a"
    by blast
  with \<open>b \<notin> affected f\<close>
  have "(f ^ n) \<langle>$\<rangle> a \<notin> affected f"
    by simp
  then have "f \<langle>$\<rangle> a \<notin> affected f"
    by (induct n) (simp_all add: apply_times)
  with assms show False
    by simp
qed

lemma finite_orbit [simp]:
  "finite (orbit f a)"
proof (cases "a \<in> affected f")
  case False then show ?thesis
    by (simp add: not_in_affected_iff_orbit_eq_singleton)
next
  case True then have "orbit f a \<subseteq> affected f"
    by (rule orbit_subset_eq_affected)
  then show ?thesis using finite_affected
    by (rule finite_subset)
qed

lemma orbit_1 [simp]:
  "orbit 1 a = {a}"
  by (auto simp add: orbit_def)

lemma order_1 [simp]:
  "order 1 a = 1"
  unfolding order_def by simp

lemma card_orbit_eq [simp]:
  "card (orbit f a) = order f a"
  by (simp add: order_def)

lemma order_greater_zero [simp]:
  "order f a > 0"
  by (simp only: card_gt_0_iff order_def comp_def) simp

lemma order_eq_one_iff:
  "order f a = Suc 0 \<longleftrightarrow> a \<notin> affected f" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P then have "card (orbit f a) = 1"
    by simp
  then obtain b where "orbit f a = {b}"
    by (rule card_1_singletonE)
  with in_orbit_self [of a f]
    have "b = a" by simp
  with \<open>orbit f a = {b}\<close> show ?Q
    by (simp add: not_in_affected_iff_orbit_eq_singleton)
next
  assume ?Q
  then have "orbit f a = {a}"
    by (simp add: not_in_affected_iff_orbit_eq_singleton)
  then have "card (orbit f a) = 1"
    by simp
  then show ?P
    by simp
qed

lemma order_greater_eq_two_iff:
  "order f a \<ge> 2 \<longleftrightarrow> a \<in> affected f"
  using order_eq_one_iff [of f a]
  apply (auto simp add: neq_iff)
  using order_greater_zero [of f a]
  apply simp
  done

lemma order_less_eq_affected:
  assumes "f \<noteq> 1"
  shows "order f a \<le> card (affected f)"
proof (cases "a \<in> affected f")
  from assms have "affected f \<noteq> {}"
    by simp
  then obtain B b where "affected f = insert b B"
    by blast
  with finite_affected [of f] have "card (affected f) \<ge> 1"
    by (simp add: card.insert_remove)
  case False then have "order f a = 1"
    by (simp add: order_eq_one_iff)
  with \<open>card (affected f) \<ge> 1\<close> show ?thesis
    by simp
next
  case True
  have "card (orbit f a) \<le> card (affected f)"
    by (rule card_mono) (simp_all add: True orbit_subset_eq_affected card_mono)
  then show ?thesis
    by simp
qed

lemma affected_order_greater_eq_two:
  assumes "a \<in> affected f"
  shows "order f a \<ge> 2"
proof (rule ccontr)
  assume "\<not> 2 \<le> order f a"
  then have "order f a < 2"
    by (simp add: not_le)
  with order_greater_zero [of f a] have "order f a = 1"
    by arith
  with assms show False
    by (simp add: order_eq_one_iff)
qed

lemma order_witness_unfold:
  assumes "n > 0" and "(f ^ n) \<langle>$\<rangle> a = a"
  shows "order f a = card ((\<lambda>m. (f ^ m) \<langle>$\<rangle> a) ` {0..<n})"
proof  -
  have "orbit f a = (\<lambda>m. (f ^ m) \<langle>$\<rangle> a) ` {0..<n}" (is "_ = ?B")
  proof (rule set_eqI, rule)
    fix b
    assume "b \<in> orbit f a"
    then obtain m where "(f ^ m) \<langle>$\<rangle> a = b"
      by (auto simp add: orbit_def)
    then have "b = (f ^ (m mod n + n * (m div n))) \<langle>$\<rangle> a"
      by simp
    also have "\<dots> = (f ^ (m mod n)) \<langle>$\<rangle> ((f ^ (n * (m div n))) \<langle>$\<rangle> a)"
      by (simp only: power_add apply_times) simp
    also have "(f ^ (n * q)) \<langle>$\<rangle> a = a" for q
      by (induct q)
        (simp_all add: power_add apply_times assms)
    finally have "b = (f ^ (m mod n)) \<langle>$\<rangle> a" .
    moreover from \<open>n > 0\<close>
    have "m mod n < n" 
      by simp
    ultimately show "b \<in> ?B"
      by auto
  next
    fix b
    assume "b \<in> ?B"
    then obtain m where "(f ^ m) \<langle>$\<rangle> a = b"
      by blast
    then show "b \<in> orbit f a"
      by (rule in_orbitI)
  qed
  then have "card (orbit f a) = card ?B"
    by (simp only:)
  then show ?thesis
    by simp
qed
    
lemma inj_on_apply_range:
  "inj_on (\<lambda>m. (f ^ m) \<langle>$\<rangle> a) {..<order f a}"
proof -
  have "inj_on (\<lambda>m. (f ^ m) \<langle>$\<rangle> a) {..<n}"
    if "n \<le> order f a" for n
  using that proof (induct n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    then have prem: "n < order f a"
      by simp
    with Suc.hyps have hyp: "inj_on (\<lambda>m. (f ^ m) \<langle>$\<rangle> a) {..<n}"
      by simp
    have "(f ^ n) \<langle>$\<rangle> a \<notin> (\<lambda>m. (f ^ m) \<langle>$\<rangle> a) ` {..<n}"
    proof
      assume "(f ^ n) \<langle>$\<rangle> a \<in> (\<lambda>m. (f ^ m) \<langle>$\<rangle> a) ` {..<n}"
      then obtain m where *: "(f ^ m) \<langle>$\<rangle> a = (f ^ n) \<langle>$\<rangle> a" and "m < n"
        by auto
      interpret bijection "apply (f ^ m)"
        by standard simp
      from \<open>m < n\<close> have "n = m + (n - m)"
        and nm: "0 < n - m" "n - m \<le> n"
        by arith+
      with * have "(f ^ m) \<langle>$\<rangle> a = (f ^ (m + (n - m))) \<langle>$\<rangle> a"
        by simp
      then have "(f ^ m) \<langle>$\<rangle> a = (f ^ m) \<langle>$\<rangle> ((f ^ (n - m)) \<langle>$\<rangle> a)"
        by (simp add: power_add apply_times)
      then have "(f ^ (n - m)) \<langle>$\<rangle> a = a"
        by simp
      with \<open>n - m > 0\<close>
      have "order f a = card ((\<lambda>m. (f ^ m) \<langle>$\<rangle> a) ` {0..<n - m})"
         by (rule order_witness_unfold)
      also have "card ((\<lambda>m. (f ^ m) \<langle>$\<rangle> a) ` {0..<n - m}) \<le> card {0..<n - m}"
        by (rule card_image_le) simp
      finally have "order f a \<le> n - m"
        by simp
      with prem show False by simp
    qed
    with hyp show ?case
      by (simp add: lessThan_Suc)
  qed
  then show ?thesis by simp
qed

lemma orbit_unfold_image:
  "orbit f a = (\<lambda>n. (f ^ n) \<langle>$\<rangle> a) ` {..<order f a}" (is "_ = ?A")
proof (rule sym, rule card_subset_eq)
  show "finite (orbit f a)"
    by simp
  show "?A \<subseteq> orbit f a"
    by (auto simp add: orbit_def)
  from inj_on_apply_range [of f a]
  have "card ?A = order f a"
    by (auto simp add: card_image)
  then show "card ?A = card (orbit f a)"
    by simp
qed

lemma in_orbitE:
  assumes "b \<in> orbit f a"
  obtains n where "b = (f ^ n) \<langle>$\<rangle> a" and "n < order f a"
  using assms unfolding orbit_unfold_image by blast

lemma apply_power_order [simp]:
  "(f ^ order f a) \<langle>$\<rangle> a = a"
proof -
  have "(f ^ order f a) \<langle>$\<rangle> a \<in> orbit f a"
    by simp
  then obtain n where
    *: "(f ^ order f a) \<langle>$\<rangle> a = (f ^ n) \<langle>$\<rangle> a"
    and "n < order f a"
    by (rule in_orbitE)
  show ?thesis
  proof (cases n)
    case 0 with * show ?thesis by simp
  next
    case (Suc m)
    from order_greater_zero [of f a]
      have "Suc (order f a - 1) = order f a"
      by arith
    from Suc \<open>n < order f a\<close>
      have "m < order f a"
      by simp
    with Suc *
    have "(inverse f) \<langle>$\<rangle> ((f ^ Suc (order f a - 1)) \<langle>$\<rangle> a) =
      (inverse f) \<langle>$\<rangle> ((f ^ Suc m) \<langle>$\<rangle> a)"
      by simp
    then have "(f ^ (order f a - 1)) \<langle>$\<rangle> a =
      (f ^ m) \<langle>$\<rangle> a"
      by (simp only: power_Suc apply_times)
        (simp add: apply_sequence mult.assoc [symmetric])
    with inj_on_apply_range
    have "order f a - 1 = m"
      by (rule inj_onD)
        (simp_all add: \<open>m < order f a\<close>)
    with Suc have "n = order f a"
      by auto
    with \<open>n < order f a\<close>
    show ?thesis by simp
  qed
qed

lemma apply_power_left_mult_order [simp]:
  "(f ^ (n * order f a)) \<langle>$\<rangle> a = a"
  by (induct n) (simp_all add: power_add apply_times)

lemma apply_power_right_mult_order [simp]:
  "(f ^ (order f a * n)) \<langle>$\<rangle> a = a"
  by (simp add: ac_simps)

lemma apply_power_mod_order_eq [simp]:
  "(f ^ (n mod order f a)) \<langle>$\<rangle> a = (f ^ n) \<langle>$\<rangle> a"
proof -
  have "(f ^ n) \<langle>$\<rangle> a = (f ^ (n mod order f a + order f a * (n div order f a))) \<langle>$\<rangle> a"
    by simp
  also have "\<dots> = (f ^ (n mod order f a) * f ^ (order f a * (n div order f a))) \<langle>$\<rangle> a"
    by (simp flip: power_add)
  finally show ?thesis
    by (simp add: apply_times)
qed  

lemma apply_power_eq_iff:
  "(f ^ m) \<langle>$\<rangle> a = (f ^ n) \<langle>$\<rangle> a \<longleftrightarrow> m mod order f a = n mod order f a" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q
  then have "(f ^ (m mod order f a)) \<langle>$\<rangle> a = (f ^ (n mod order f a)) \<langle>$\<rangle> a"
    by simp
  then show ?P
    by simp
next
  assume ?P
  then have "(f ^ (m mod order f a)) \<langle>$\<rangle> a = (f ^ (n mod order f a)) \<langle>$\<rangle> a"
    by simp
  with inj_on_apply_range
  show ?Q
    by (rule inj_onD) simp_all
qed

lemma apply_inverse_eq_apply_power_order_minus_one:
  "(inverse f) \<langle>$\<rangle> a = (f ^ (order f a - 1)) \<langle>$\<rangle> a"
proof (cases "order f a")
  case 0 with order_greater_zero [of f a] show ?thesis
    by simp
next
  case (Suc n)
  moreover have "(f ^ order f a) \<langle>$\<rangle> a = a"
    by simp
  then have *: "(inverse f) \<langle>$\<rangle> ((f ^ order f a) \<langle>$\<rangle> a) = (inverse f) \<langle>$\<rangle> a"
    by simp
  ultimately show ?thesis
    by (simp add: apply_sequence mult.assoc [symmetric])
qed

lemma apply_inverse_self_in_orbit [simp]:
  "(inverse f) \<langle>$\<rangle> a \<in> orbit f a"
  using apply_inverse_eq_apply_power_order_minus_one [symmetric]
  by (rule in_orbitI)

lemma apply_inverse_power_eq:
  "(inverse (f ^ n)) \<langle>$\<rangle> a = (f ^ (order f a - n mod order f a)) \<langle>$\<rangle> a"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  define m where "m = order f a - n mod order f a - 1"
  moreover have "order f a - n mod order f a > 0"
    by simp
  ultimately have *: "order f a - n mod order f a = Suc m"
    by arith
  moreover from * have m2: "order f a - Suc n mod order f a = (if m = 0 then order f a else m)"
    by (auto simp add: mod_Suc)
  ultimately show ?case
    using Suc
      by (simp_all add: apply_times power_Suc2 [of _ n] power_Suc [of _ m] del: power_Suc)
        (simp add: apply_sequence mult.assoc [symmetric])
qed

lemma apply_power_eq_self_iff:
  "(f ^ n) \<langle>$\<rangle> a = a \<longleftrightarrow> order f a dvd n"
  using apply_power_eq_iff [of f n a 0]
    by (simp add: mod_eq_0_iff_dvd)
  
lemma orbit_equiv:
  assumes "b \<in> orbit f a"
  shows "orbit f b = orbit f a" (is "?B = ?A")
proof
  from assms obtain n where "n < order f a" and b: "b = (f ^ n) \<langle>$\<rangle> a"
    by (rule in_orbitE)
  then show "?B \<subseteq> ?A"
    by (auto simp add: apply_sequence power_add [symmetric] intro: in_orbitI elim!: in_orbitE)
  from b have "(inverse (f ^ n)) \<langle>$\<rangle> b = (inverse (f ^ n)) \<langle>$\<rangle> ((f ^ n) \<langle>$\<rangle> a)"
    by simp
  then have a: "a = (inverse (f ^ n)) \<langle>$\<rangle> b"
    by (simp add: apply_sequence)
  then show "?A \<subseteq> ?B"
    apply (auto simp add: apply_sequence power_add [symmetric] intro: in_orbitI elim!: in_orbitE)
    unfolding apply_times comp_def apply_inverse_power_eq
    unfolding apply_sequence power_add [symmetric]
    apply (rule in_orbitI) apply rule
    done
qed

lemma orbit_apply [simp]:
  "orbit f (f \<langle>$\<rangle> a) = orbit f a"
  by (rule orbit_equiv) simp
  
lemma order_apply [simp]:
  "order f (f \<langle>$\<rangle> a) = order f a"
  by (simp only: order_def comp_def orbit_apply)

lemma orbit_apply_inverse [simp]:
  "orbit f (inverse f \<langle>$\<rangle> a) = orbit f a"
  by (rule orbit_equiv) simp

lemma order_apply_inverse [simp]:
  "order f (inverse f \<langle>$\<rangle> a) = order f a"
  by (simp only: order_def comp_def orbit_apply_inverse)

lemma orbit_apply_power [simp]:
  "orbit f ((f ^ n) \<langle>$\<rangle> a) = orbit f a"
  by (rule orbit_equiv) simp

lemma order_apply_power [simp]:
  "order f ((f ^ n) \<langle>$\<rangle> a) = order f a"
  by (simp only: order_def comp_def orbit_apply_power)

lemma orbit_inverse [simp]:
  "orbit (inverse f) = orbit f"
proof (rule ext, rule set_eqI, rule)
  fix b a
  assume "b \<in> orbit f a"
  then obtain n where b: "b = (f ^ n) \<langle>$\<rangle> a" "n < order f a"
    by (rule in_orbitE)
  then have "b = apply (inverse (inverse f) ^ n) a"
    by simp
  then have "b = apply (inverse (inverse f ^ n)) a"
    by (simp add: perm_power_inverse)
  then have "b = apply (inverse f ^ (n * (order (inverse f ^ n) a - 1))) a"
    by (simp add: apply_inverse_eq_apply_power_order_minus_one power_mult)
  then show "b \<in> orbit (inverse f) a"
    by simp
next
  fix b a
  assume "b \<in> orbit (inverse f) a"
  then show "b \<in> orbit f a"
    by (rule in_orbitE)
      (simp add: apply_inverse_eq_apply_power_order_minus_one
      perm_power_inverse power_mult [symmetric])
qed

lemma order_inverse [simp]:
  "order (inverse f) = order f"
  by (simp add: order_def)

lemma orbit_disjoint:
  assumes "orbit f a \<noteq> orbit f b"
  shows "orbit f a \<inter> orbit f b = {}"
proof (rule ccontr)
  assume "orbit f a \<inter> orbit f b \<noteq> {}"
  then obtain c where "c \<in> orbit f a \<inter> orbit f b"
    by blast
  then have "c \<in> orbit f a" and "c \<in> orbit f b"
    by auto
  then obtain m n where "c = (f ^ m) \<langle>$\<rangle> a"
    and "c = apply (f ^ n) b" by (blast elim!: in_orbitE)
  then have "(f ^ m) \<langle>$\<rangle> a = apply (f ^ n) b"
    by simp
  then have "apply (inverse f ^ m) ((f ^ m) \<langle>$\<rangle> a) =
    apply (inverse f ^ m) (apply (f ^ n) b)"
    by simp
  then have *: "apply (inverse f ^ m * f ^ n) b = a"
    by (simp add: apply_sequence perm_power_inverse)
  have "a \<in> orbit f b"
  proof (cases n m rule: linorder_cases)
    case equal with * show ?thesis
      by (simp add: perm_power_inverse)
  next
    case less
    moreover define q where "q = m - n"
    ultimately have "m = q + n" by arith
    with * have "apply (inverse f ^ q) b = a"
      by (simp add: power_add mult.assoc perm_power_inverse)
    then have "a \<in> orbit (inverse f) b"
      by (rule in_orbitI)
    then show ?thesis
      by simp
  next
    case greater
    moreover define q where "q = n - m"
    ultimately have "n = m + q" by arith
    with * have "apply (f ^ q) b = a"
      by (simp add: power_add mult.assoc [symmetric] perm_power_inverse)
    then show ?thesis
      by (rule in_orbitI)
  qed
  with assms show False
    by (auto dest: orbit_equiv)
qed


subsection \<open>Swaps\<close>

lift_definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a perm"  ("\<langle>_ \<leftrightarrow> _\<rangle>")
  is "\<lambda>a b. Fun.swap a b id"
proof
  fix a b :: 'a
  have "{c. Fun.swap a b id c \<noteq> c} \<subseteq> {a, b}"
    by (auto simp add: Fun.swap_def)
  then show "finite {c. Fun.swap a b id c \<noteq> c}"
    by (rule finite_subset) simp
qed simp

lemma apply_swap_simp [simp]:
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> a = b"
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> b = a"
  by (transfer; simp)+

lemma apply_swap_same [simp]:
  "c \<noteq> a \<Longrightarrow> c \<noteq> b \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> c = c"
  by transfer simp

lemma apply_swap_eq_iff [simp]:
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> c = a \<longleftrightarrow> c = b"
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> c = b \<longleftrightarrow> c = a"
  by (transfer; auto simp add: Fun.swap_def)+

lemma swap_1 [simp]:
  "\<langle>a \<leftrightarrow> a\<rangle> = 1"
  by transfer simp

lemma swap_sym:
  "\<langle>b \<leftrightarrow> a\<rangle> = \<langle>a \<leftrightarrow> b\<rangle>"
  by (transfer; auto simp add: Fun.swap_def)+

lemma swap_self [simp]:
  "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>a \<leftrightarrow> b\<rangle> = 1"
  by transfer (simp add: Fun.swap_def fun_eq_iff)

lemma affected_swap:
  "a \<noteq> b \<Longrightarrow> affected \<langle>a \<leftrightarrow> b\<rangle> = {a, b}"
  by transfer (auto simp add: Fun.swap_def)

lemma inverse_swap [simp]:
  "inverse \<langle>a \<leftrightarrow> b\<rangle> = \<langle>a \<leftrightarrow> b\<rangle>"
  by transfer (auto intro: inv_equality simp: Fun.swap_def)


subsection \<open>Permutations specified by cycles\<close>

fun cycle :: "'a list \<Rightarrow> 'a perm"  ("\<langle>_\<rangle>")
where
  "\<langle>[]\<rangle> = 1"
| "\<langle>[a]\<rangle> = 1"
| "\<langle>a # b # as\<rangle> = \<langle>a # as\<rangle> * \<langle>a\<leftrightarrow>b\<rangle>"

text \<open>
  We do not continue and restrict ourselves to syntax from here.
  See also introductory note.
\<close>


subsection \<open>Syntax\<close>

bundle no_permutation_syntax
begin
  no_notation swap    ("\<langle>_ \<leftrightarrow> _\<rangle>")
  no_notation cycle   ("\<langle>_\<rangle>")
  no_notation "apply" (infixl "\<langle>$\<rangle>" 999)
end

bundle permutation_syntax
begin
  notation swap       ("\<langle>_ \<leftrightarrow> _\<rangle>")
  notation cycle      ("\<langle>_\<rangle>")
  notation "apply"    (infixl "\<langle>$\<rangle>" 999)
end

unbundle no_permutation_syntax

end
