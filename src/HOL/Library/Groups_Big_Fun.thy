(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Big sum and product over function bodies\<close>

theory Groups_Big_Fun
imports
  Main
begin

subsection \<open>Abstract product\<close>

locale comm_monoid_fun = comm_monoid
begin

definition G :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  expand_set: "G g = comm_monoid_set.F f \<^bold>1 g {a. g a \<noteq> \<^bold>1}"

interpretation F: comm_monoid_set f "\<^bold>1"
  ..

lemma expand_superset:
  assumes "finite A" and "{a. g a \<noteq> \<^bold>1} \<subseteq> A"
  shows "G g = F.F g A"
  using F.mono_neutral_right assms expand_set by fastforce

lemma conditionalize:
  assumes "finite A"
  shows "F.F g A = G (\<lambda>a. if a \<in> A then g a else \<^bold>1)"
  using assms
  by (smt (verit, ccfv_threshold) Diff_iff F.mono_neutral_cong_right expand_set mem_Collect_eq subsetI)


lemma neutral [simp]:
  "G (\<lambda>a. \<^bold>1) = \<^bold>1"
  by (simp add: expand_set)

lemma update [simp]:
  assumes "finite {a. g a \<noteq> \<^bold>1}"
  assumes "g a = \<^bold>1"
  shows "G (g(a := b)) = b \<^bold>* G g"
proof (cases "b = \<^bold>1")
  case True with \<open>g a = \<^bold>1\<close> show ?thesis
    by (simp add: expand_set) (rule F.cong, auto)
next
  case False
  moreover have "{a'. a' \<noteq> a \<longrightarrow> g a' \<noteq> \<^bold>1} = insert a {a. g a \<noteq> \<^bold>1}"
    by auto
  moreover from \<open>g a = \<^bold>1\<close> have "a \<notin> {a. g a \<noteq> \<^bold>1}"
    by simp
  moreover have "F.F (\<lambda>a'. if a' = a then b else g a') {a. g a \<noteq> \<^bold>1} = F.F g {a. g a \<noteq> \<^bold>1}"
    by (rule F.cong) (auto simp add: \<open>g a = \<^bold>1\<close>)
  ultimately show ?thesis using \<open>finite {a. g a \<noteq> \<^bold>1}\<close> by (simp add: expand_set)
qed

lemma infinite [simp]:
  "\<not> finite {a. g a \<noteq> \<^bold>1} \<Longrightarrow> G g = \<^bold>1"
  by (simp add: expand_set)

lemma cong [cong]:
  assumes "\<And>a. g a = h a"
  shows "G g = G h"
  using assms by (simp add: expand_set)

lemma not_neutral_obtains_not_neutral:
  assumes "G g \<noteq> \<^bold>1"
  obtains a where "g a \<noteq> \<^bold>1"
  using assms by (auto elim: F.not_neutral_contains_not_neutral simp add: expand_set)

lemma reindex_cong:
  assumes "bij l"
  assumes "g \<circ> l = h"
  shows "G g = G h"
proof -
  from assms have unfold: "h = g \<circ> l" by simp
  from \<open>bij l\<close> have "inj l" by (rule bij_is_inj)
  then have "inj_on l {a. h a \<noteq> \<^bold>1}" by (rule subset_inj_on) simp
  moreover from \<open>bij l\<close> have "{a. g a \<noteq> \<^bold>1} = l ` {a. h a \<noteq> \<^bold>1}"
    by (auto simp add: image_Collect unfold elim: bij_pointE)
  moreover have "\<And>x. x \<in> {a. h a \<noteq> \<^bold>1} \<Longrightarrow> g (l x) = h x"
    by (simp add: unfold)
  ultimately have "F.F g {a. g a \<noteq> \<^bold>1} = F.F h {a. h a \<noteq> \<^bold>1}"
    by (rule F.reindex_cong)
  then show ?thesis by (simp add: expand_set)
qed

lemma distrib:
  assumes "finite {a. g a \<noteq> \<^bold>1}" and "finite {a. h a \<noteq> \<^bold>1}"
  shows "G (\<lambda>a. g a \<^bold>* h a) = G g \<^bold>* G h"
proof -
  from assms have "finite ({a. g a \<noteq> \<^bold>1} \<union> {a. h a \<noteq> \<^bold>1})" by simp
  moreover have "{a. g a \<^bold>* h a \<noteq> \<^bold>1} \<subseteq> {a. g a \<noteq> \<^bold>1} \<union> {a. h a \<noteq> \<^bold>1}"
    by auto (drule sym, simp)
  ultimately show ?thesis
    using assms
    by (simp add: expand_superset [of "{a. g a \<noteq> \<^bold>1} \<union> {a. h a \<noteq> \<^bold>1}"] F.distrib)
qed

lemma swap:
  assumes "finite C"
  assumes subset: "{a. \<exists>b. g a b \<noteq> \<^bold>1} \<times> {b. \<exists>a. g a b \<noteq> \<^bold>1} \<subseteq> C" (is "?A \<times> ?B \<subseteq> C")
  shows "G (\<lambda>a. G (g a)) = G (\<lambda>b. G (\<lambda>a. g a b))"
proof -
  from \<open>finite C\<close> subset
    have "finite ({a. \<exists>b. g a b \<noteq> \<^bold>1} \<times> {b. \<exists>a. g a b \<noteq> \<^bold>1})"
    by (rule rev_finite_subset)
  then have fins:
    "finite {b. \<exists>a. g a b \<noteq> \<^bold>1}" "finite {a. \<exists>b. g a b \<noteq> \<^bold>1}"
    by (auto simp add: finite_cartesian_product_iff)
  have subsets: "\<And>a. {b. g a b \<noteq> \<^bold>1} \<subseteq> {b. \<exists>a. g a b \<noteq> \<^bold>1}"
    "\<And>b. {a. g a b \<noteq> \<^bold>1} \<subseteq> {a. \<exists>b. g a b \<noteq> \<^bold>1}"
    "{a. F.F (g a) {b. \<exists>a. g a b \<noteq> \<^bold>1} \<noteq> \<^bold>1} \<subseteq> {a. \<exists>b. g a b \<noteq> \<^bold>1}"
    "{a. F.F (\<lambda>aa. g aa a) {a. \<exists>b. g a b \<noteq> \<^bold>1} \<noteq> \<^bold>1} \<subseteq> {b. \<exists>a. g a b \<noteq> \<^bold>1}"
    by (auto elim: F.not_neutral_contains_not_neutral)
  from F.swap have
    "F.F (\<lambda>a. F.F (g a) {b. \<exists>a. g a b \<noteq> \<^bold>1}) {a. \<exists>b. g a b \<noteq> \<^bold>1} =
      F.F (\<lambda>b. F.F (\<lambda>a. g a b) {a. \<exists>b. g a b \<noteq> \<^bold>1}) {b. \<exists>a. g a b \<noteq> \<^bold>1}" .
  with subsets fins have "G (\<lambda>a. F.F (g a) {b. \<exists>a. g a b \<noteq> \<^bold>1}) =
    G (\<lambda>b. F.F (\<lambda>a. g a b) {a. \<exists>b. g a b \<noteq> \<^bold>1})"
    by (auto simp add: expand_superset [of "{b. \<exists>a. g a b \<noteq> \<^bold>1}"]
      expand_superset [of "{a. \<exists>b. g a b \<noteq> \<^bold>1}"])
  with subsets fins show ?thesis
    by (auto simp add: expand_superset [of "{b. \<exists>a. g a b \<noteq> \<^bold>1}"]
      expand_superset [of "{a. \<exists>b. g a b \<noteq> \<^bold>1}"])
qed

lemma cartesian_product:
  assumes "finite C"
  assumes subset: "{a. \<exists>b. g a b \<noteq> \<^bold>1} \<times> {b. \<exists>a. g a b \<noteq> \<^bold>1} \<subseteq> C" (is "?A \<times> ?B \<subseteq> C")
  shows "G (\<lambda>a. G (g a)) = G (\<lambda>(a, b). g a b)"
proof -
  from subset \<open>finite C\<close> have fin_prod: "finite (?A \<times> ?B)"
    by (rule finite_subset)
  from fin_prod have "finite ?A" and "finite ?B"
    by (auto simp add: finite_cartesian_product_iff)
  have *: "G (\<lambda>a. G (g a)) =
    (F.F (\<lambda>a. F.F (g a) {b. \<exists>a. g a b \<noteq> \<^bold>1}) {a. \<exists>b. g a b \<noteq> \<^bold>1})"
    using \<open>finite ?A\<close> \<open>finite ?B\<close> expand_superset
    by (smt (verit, del_insts) Collect_mono local.cong not_neutral_obtains_not_neutral)
  have **: "{p. (case p of (a, b) \<Rightarrow> g a b) \<noteq> \<^bold>1} \<subseteq> ?A \<times> ?B"
    by auto
  show ?thesis
    using \<open>finite C\<close> expand_superset
    using "*" ** F.cartesian_product fin_prod by force
qed

lemma cartesian_product2:
  assumes fin: "finite D"
  assumes subset: "{(a, b). \<exists>c. g a b c \<noteq> \<^bold>1} \<times> {c. \<exists>a b. g a b c \<noteq> \<^bold>1} \<subseteq> D" (is "?AB \<times> ?C \<subseteq> D")
  shows "G (\<lambda>(a, b). G (g a b)) = G (\<lambda>(a, b, c). g a b c)"
proof -
  have bij: "bij (\<lambda>(a, b, c). ((a, b), c))"
    by (auto intro!: bijI injI simp add: image_def)
  have "{p. \<exists>c. g (fst p) (snd p) c \<noteq> \<^bold>1} \<times> {c. \<exists>p. g (fst p) (snd p) c \<noteq> \<^bold>1} \<subseteq> D"
    by auto (insert subset, blast)
  with fin have "G (\<lambda>p. G (g (fst p) (snd p))) = G (\<lambda>(p, c). g (fst p) (snd p) c)"
    by (rule cartesian_product)
  then have "G (\<lambda>(a, b). G (g a b)) = G (\<lambda>((a, b), c). g a b c)"
    by (auto simp add: split_def)
  also have "G (\<lambda>((a, b), c). g a b c) = G (\<lambda>(a, b, c). g a b c)"
    using bij by (rule reindex_cong [of "\<lambda>(a, b, c). ((a, b), c)"]) (simp add: fun_eq_iff)
  finally show ?thesis .
qed

lemma delta [simp]:
  "G (\<lambda>b. if b = a then g b else \<^bold>1) = g a"
proof -
  have "{b. (if b = a then g b else \<^bold>1) \<noteq> \<^bold>1} \<subseteq> {a}" by auto
  then show ?thesis by (simp add: expand_superset [of "{a}"])
qed

lemma delta' [simp]:
  "G (\<lambda>b. if a = b then g b else \<^bold>1) = g a"
proof -
  have "(\<lambda>b. if a = b then g b else \<^bold>1) = (\<lambda>b. if b = a then g b else \<^bold>1)"
    by (simp add: fun_eq_iff)
  then have "G (\<lambda>b. if a = b then g b else \<^bold>1) = G (\<lambda>b. if b = a then g b else \<^bold>1)"
    by (simp cong del: cong)
  then show ?thesis by simp
qed

end


subsection \<open>Concrete sum\<close>

context comm_monoid_add
begin

sublocale Sum_any: comm_monoid_fun plus 0
  rewrites "comm_monoid_set.F plus 0 = sum"
  defines Sum_any = Sum_any.G
proof -
  show "comm_monoid_fun plus 0" ..
  then interpret Sum_any: comm_monoid_fun plus 0 .
  from sum_def show "comm_monoid_set.F plus 0 = sum" by (auto intro: sym)
qed

end

syntax (ASCII)
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"    ("(3SUM _. _)" [0, 10] 10)
syntax
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"    ("(3\<Sum>_. _)" [0, 10] 10)
syntax_consts
  "_Sum_any" \<rightleftharpoons> Sum_any
translations
  "\<Sum>a. b" \<rightleftharpoons> "CONST Sum_any (\<lambda>a. b)"

lemma Sum_any_left_distrib:
  fixes r :: "'a :: semiring_0"
  assumes "finite {a. g a \<noteq> 0}"
  shows "Sum_any g * r = (\<Sum>n. g n * r)"
  by (metis (mono_tags, lifting) Collect_mono Sum_any.expand_superset assms mult_zero_left sum_distrib_right)

lemma Sum_any_right_distrib:
  fixes r :: "'a :: semiring_0"
  assumes "finite {a. g a \<noteq> 0}"
  shows "r * Sum_any g = (\<Sum>n. r * g n)"
  by (metis (mono_tags, lifting) Collect_mono Sum_any.expand_superset assms mult_zero_right sum_distrib_left)

lemma Sum_any_product:
  fixes f g :: "'b \<Rightarrow> 'a::semiring_0"
  assumes "finite {a. f a \<noteq> 0}" and "finite {b. g b \<noteq> 0}"
  shows "Sum_any f * Sum_any g = (\<Sum>a. \<Sum>b. f a * g b)"
proof -
  have "\<forall>a. (\<Sum>b. a * g b) = a * Sum_any g"
    by (simp add: Sum_any_right_distrib assms(2))
  then show ?thesis
    by (simp add: Sum_any_left_distrib assms(1))
qed

lemma Sum_any_eq_zero_iff [simp]: 
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {a. f a \<noteq> 0}"
  shows "Sum_any f = 0 \<longleftrightarrow> f = (\<lambda>_. 0)"
  using assms by (simp add: Sum_any.expand_set fun_eq_iff)


subsection \<open>Concrete product\<close>

context comm_monoid_mult
begin

sublocale Prod_any: comm_monoid_fun times 1
  rewrites "comm_monoid_set.F times 1 = prod"
  defines Prod_any = Prod_any.G
proof -
  show "comm_monoid_fun times 1" ..
  then interpret Prod_any: comm_monoid_fun times 1 .
  from prod_def show "comm_monoid_set.F times 1 = prod" by (auto intro: sym)
qed

end

syntax (ASCII)
  "_Prod_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_mult"  ("(3PROD _. _)" [0, 10] 10)
syntax
  "_Prod_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_mult"  ("(3\<Prod>_. _)" [0, 10] 10)
syntax_consts
  "_Prod_any" == Prod_any
translations
  "\<Prod>a. b" == "CONST Prod_any (\<lambda>a. b)"

lemma Prod_any_zero:
  fixes f :: "'b \<Rightarrow> 'a :: comm_semiring_1"
  assumes "finite {a. f a \<noteq> 1}"
  assumes "f a = 0"
  shows "(\<Prod>a. f a) = 0"
proof -
  from \<open>f a = 0\<close> have "f a \<noteq> 1" by simp
  with \<open>f a = 0\<close> have "\<exists>a. f a \<noteq> 1 \<and> f a = 0" by blast
  with \<open>finite {a. f a \<noteq> 1}\<close> show ?thesis
    by (simp add: Prod_any.expand_set prod_zero)
qed

lemma Prod_any_not_zero:
  fixes f :: "'b \<Rightarrow> 'a :: comm_semiring_1"
  assumes "finite {a. f a \<noteq> 1}"
  assumes "(\<Prod>a. f a) \<noteq> 0"
  shows "f a \<noteq> 0"
  using assms Prod_any_zero [of f] by blast

lemma power_Sum_any:
  assumes "finite {a. f a \<noteq> 0}"
  shows "c ^ (\<Sum>a. f a) = (\<Prod>a. c ^ f a)"
proof -
  have "{a. c ^ f a \<noteq> 1} \<subseteq> {a. f a \<noteq> 0}"
    by (auto intro: ccontr)
  with assms show ?thesis
    by (simp add: Sum_any.expand_set Prod_any.expand_superset power_sum)
qed

end
