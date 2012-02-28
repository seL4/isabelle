(*  Title:      HOL/Probability/Sigma_Algebra.thy
    Author:     Stefan Richter, Markus Wenzel, TU München
    Author:     Johannes Hölzl, TU München
    Plus material from the Hurd/Coble measure theory development,
    translated by Lawrence Paulson.
*)

header {* Sigma Algebras *}

theory Sigma_Algebra
imports
  Complex_Main
  "~~/src/HOL/Library/Countable"
  "~~/src/HOL/Library/FuncSet"
  "~~/src/HOL/Library/Indicator_Function"
begin

text {* Sigma algebras are an elementary concept in measure
  theory. To measure --- that is to integrate --- functions, we first have
  to measure sets. Unfortunately, when dealing with a large universe,
  it is often not possible to consistently assign a measure to every
  subset. Therefore it is necessary to define the set of measurable
  subsets of the universe. A sigma algebra is such a set that has
  three very natural and desirable properties. *}

subsection {* Algebras *}

record 'a algebra =
  space :: "'a set"
  sets :: "'a set set"

locale subset_class =
  fixes M :: "('a, 'b) algebra_scheme"
  assumes space_closed: "sets M \<subseteq> Pow (space M)"

lemma (in subset_class) sets_into_space: "x \<in> sets M \<Longrightarrow> x \<subseteq> space M"
  by (metis PowD contra_subsetD space_closed)

locale ring_of_sets = subset_class +
  assumes empty_sets [iff]: "{} \<in> sets M"
     and  Diff [intro]: "\<And>a b. a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a - b \<in> sets M"
     and  Un [intro]: "\<And>a b. a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<union> b \<in> sets M"

lemma (in ring_of_sets) Int [intro]:
  assumes a: "a \<in> sets M" and b: "b \<in> sets M" shows "a \<inter> b \<in> sets M"
proof -
  have "a \<inter> b = a - (a - b)"
    by auto
  then show "a \<inter> b \<in> sets M"
    using a b by auto
qed

lemma (in ring_of_sets) finite_Union [intro]:
  "finite X \<Longrightarrow> X \<subseteq> sets M \<Longrightarrow> Union X \<in> sets M"
  by (induct set: finite) (auto simp add: Un)

lemma (in ring_of_sets) finite_UN[intro]:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(\<Union>i\<in>I. A i) \<in> sets M"
  using assms by induct auto

lemma (in ring_of_sets) finite_INT[intro]:
  assumes "finite I" "I \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(\<Inter>i\<in>I. A i) \<in> sets M"
  using assms by (induct rule: finite_ne_induct) auto

lemma (in ring_of_sets) insert_in_sets:
  assumes "{x} \<in> sets M" "A \<in> sets M" shows "insert x A \<in> sets M"
proof -
  have "{x} \<union> A \<in> sets M" using assms by (rule Un)
  thus ?thesis by auto
qed

lemma (in ring_of_sets) Int_space_eq1 [simp]: "x \<in> sets M \<Longrightarrow> space M \<inter> x = x"
  by (metis Int_absorb1 sets_into_space)

lemma (in ring_of_sets) Int_space_eq2 [simp]: "x \<in> sets M \<Longrightarrow> x \<inter> space M = x"
  by (metis Int_absorb2 sets_into_space)

lemma (in ring_of_sets) sets_Collect_conj:
  assumes "{x\<in>space M. P x} \<in> sets M" "{x\<in>space M. Q x} \<in> sets M"
  shows "{x\<in>space M. Q x \<and> P x} \<in> sets M"
proof -
  have "{x\<in>space M. Q x \<and> P x} = {x\<in>space M. Q x} \<inter> {x\<in>space M. P x}"
    by auto
  with assms show ?thesis by auto
qed

lemma (in ring_of_sets) sets_Collect_disj:
  assumes "{x\<in>space M. P x} \<in> sets M" "{x\<in>space M. Q x} \<in> sets M"
  shows "{x\<in>space M. Q x \<or> P x} \<in> sets M"
proof -
  have "{x\<in>space M. Q x \<or> P x} = {x\<in>space M. Q x} \<union> {x\<in>space M. P x}"
    by auto
  with assms show ?thesis by auto
qed

lemma (in ring_of_sets) sets_Collect_finite_All:
  assumes "\<And>i. i \<in> S \<Longrightarrow> {x\<in>space M. P i x} \<in> sets M" "finite S" "S \<noteq> {}"
  shows "{x\<in>space M. \<forall>i\<in>S. P i x} \<in> sets M"
proof -
  have "{x\<in>space M. \<forall>i\<in>S. P i x} = (\<Inter>i\<in>S. {x\<in>space M. P i x})"
    using `S \<noteq> {}` by auto
  with assms show ?thesis by auto
qed

lemma (in ring_of_sets) sets_Collect_finite_Ex:
  assumes "\<And>i. i \<in> S \<Longrightarrow> {x\<in>space M. P i x} \<in> sets M" "finite S"
  shows "{x\<in>space M. \<exists>i\<in>S. P i x} \<in> sets M"
proof -
  have "{x\<in>space M. \<exists>i\<in>S. P i x} = (\<Union>i\<in>S. {x\<in>space M. P i x})"
    by auto
  with assms show ?thesis by auto
qed

locale algebra = ring_of_sets +
  assumes top [iff]: "space M \<in> sets M"

lemma (in algebra) compl_sets [intro]:
  "a \<in> sets M \<Longrightarrow> space M - a \<in> sets M"
  by auto

lemma algebra_iff_Un:
  "algebra M \<longleftrightarrow>
    sets M \<subseteq> Pow (space M) &
    {} \<in> sets M &
    (\<forall>a \<in> sets M. space M - a \<in> sets M) &
    (\<forall>a \<in> sets M. \<forall> b \<in> sets M. a \<union> b \<in> sets M)" (is "_ \<longleftrightarrow> ?Un")
proof
  assume "algebra M"
  then interpret algebra M .
  show ?Un using sets_into_space by auto
next
  assume ?Un
  show "algebra M"
  proof
    show space: "sets M \<subseteq> Pow (space M)" "{} \<in> sets M" "space M \<in> sets M"
      using `?Un` by auto
    fix a b assume a: "a \<in> sets M" and b: "b \<in> sets M"
    then show "a \<union> b \<in> sets M" using `?Un` by auto
    have "a - b = space M - ((space M - a) \<union> b)"
      using space a b by auto
    then show "a - b \<in> sets M"
      using a b  `?Un` by auto
  qed
qed

lemma algebra_iff_Int:
     "algebra M \<longleftrightarrow>
       sets M \<subseteq> Pow (space M) & {} \<in> sets M &
       (\<forall>a \<in> sets M. space M - a \<in> sets M) &
       (\<forall>a \<in> sets M. \<forall> b \<in> sets M. a \<inter> b \<in> sets M)" (is "_ \<longleftrightarrow> ?Int")
proof
  assume "algebra M"
  then interpret algebra M .
  show ?Int using sets_into_space by auto
next
  assume ?Int
  show "algebra M"
  proof (unfold algebra_iff_Un, intro conjI ballI)
    show space: "sets M \<subseteq> Pow (space M)" "{} \<in> sets M"
      using `?Int` by auto
    from `?Int` show "\<And>a. a \<in> sets M \<Longrightarrow> space M - a \<in> sets M" by auto
    fix a b assume sets: "a \<in> sets M" "b \<in> sets M"
    hence "a \<union> b = space M - ((space M - a) \<inter> (space M - b))"
      using space by blast
    also have "... \<in> sets M"
      using sets `?Int` by auto
    finally show "a \<union> b \<in> sets M" .
  qed
qed

lemma (in algebra) sets_Collect_neg:
  assumes "{x\<in>space M. P x} \<in> sets M"
  shows "{x\<in>space M. \<not> P x} \<in> sets M"
proof -
  have "{x\<in>space M. \<not> P x} = space M - {x\<in>space M. P x}" by auto
  with assms show ?thesis by auto
qed

lemma (in algebra) sets_Collect_imp:
  "{x\<in>space M. P x} \<in> sets M \<Longrightarrow> {x\<in>space M. Q x} \<in> sets M \<Longrightarrow> {x\<in>space M. Q x \<longrightarrow> P x} \<in> sets M"
  unfolding imp_conv_disj by (intro sets_Collect_disj sets_Collect_neg)

lemma (in algebra) sets_Collect_const:
  "{x\<in>space M. P} \<in> sets M"
  by (cases P) auto

lemma algebra_single_set:
  assumes "X \<subseteq> S"
  shows "algebra \<lparr> space = S, sets = { {}, X, S - X, S }\<rparr>"
  by default (insert `X \<subseteq> S`, auto)

section {* Restricted algebras *}

abbreviation (in algebra)
  "restricted_space A \<equiv> \<lparr> space = A, sets = (\<lambda>S. (A \<inter> S)) ` sets M, \<dots> = more M \<rparr>"

lemma (in algebra) restricted_algebra:
  assumes "A \<in> sets M" shows "algebra (restricted_space A)"
  using assms by unfold_locales auto

subsection {* Sigma Algebras *}

locale sigma_algebra = algebra +
  assumes countable_nat_UN [intro]:
         "!!A. range A \<subseteq> sets M \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"

lemma (in algebra) is_sigma_algebra:
  assumes "finite (sets M)"
  shows "sigma_algebra M"
proof
  fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets M"
  then have "(\<Union>i. A i) = (\<Union>s\<in>sets M \<inter> range A. s)"
    by auto
  also have "(\<Union>s\<in>sets M \<inter> range A. s) \<in> sets M"
    using `finite (sets M)` by auto
  finally show "(\<Union>i. A i) \<in> sets M" .
qed

lemma countable_UN_eq:
  fixes A :: "'i::countable \<Rightarrow> 'a set"
  shows "(range A \<subseteq> sets M \<longrightarrow> (\<Union>i. A i) \<in> sets M) \<longleftrightarrow>
    (range (A \<circ> from_nat) \<subseteq> sets M \<longrightarrow> (\<Union>i. (A \<circ> from_nat) i) \<in> sets M)"
proof -
  let ?A' = "A \<circ> from_nat"
  have *: "(\<Union>i. ?A' i) = (\<Union>i. A i)" (is "?l = ?r")
  proof safe
    fix x i assume "x \<in> A i" thus "x \<in> ?l"
      by (auto intro!: exI[of _ "to_nat i"])
  next
    fix x i assume "x \<in> ?A' i" thus "x \<in> ?r"
      by (auto intro!: exI[of _ "from_nat i"])
  qed
  have **: "range ?A' = range A"
    using surj_from_nat
    by (auto simp: image_compose intro!: imageI)
  show ?thesis unfolding * ** ..
qed

lemma (in sigma_algebra) countable_UN[intro]:
  fixes A :: "'i::countable \<Rightarrow> 'a set"
  assumes "A`X \<subseteq> sets M"
  shows  "(\<Union>x\<in>X. A x) \<in> sets M"
proof -
  let ?A = "\<lambda>i. if i \<in> X then A i else {}"
  from assms have "range ?A \<subseteq> sets M" by auto
  with countable_nat_UN[of "?A \<circ> from_nat"] countable_UN_eq[of ?A M]
  have "(\<Union>x. ?A x) \<in> sets M" by auto
  moreover have "(\<Union>x. ?A x) = (\<Union>x\<in>X. A x)" by (auto split: split_if_asm)
  ultimately show ?thesis by simp
qed

lemma (in sigma_algebra) countable_INT [intro]:
  fixes A :: "'i::countable \<Rightarrow> 'a set"
  assumes A: "A`X \<subseteq> sets M" "X \<noteq> {}"
  shows "(\<Inter>i\<in>X. A i) \<in> sets M"
proof -
  from A have "\<forall>i\<in>X. A i \<in> sets M" by fast
  hence "space M - (\<Union>i\<in>X. space M - A i) \<in> sets M" by blast
  moreover
  have "(\<Inter>i\<in>X. A i) = space M - (\<Union>i\<in>X. space M - A i)" using space_closed A
    by blast
  ultimately show ?thesis by metis
qed

lemma ring_of_sets_Pow:
 "ring_of_sets \<lparr> space = sp, sets = Pow sp, \<dots> = X \<rparr>"
  by default auto

lemma algebra_Pow:
  "algebra \<lparr> space = sp, sets = Pow sp, \<dots> = X \<rparr>"
  by default auto

lemma sigma_algebra_Pow:
     "sigma_algebra \<lparr> space = sp, sets = Pow sp, \<dots> = X \<rparr>"
  by default auto

lemma sigma_algebra_iff:
     "sigma_algebra M \<longleftrightarrow>
      algebra M \<and> (\<forall>A. range A \<subseteq> sets M \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"
  by (simp add: sigma_algebra_def sigma_algebra_axioms_def)

lemma (in sigma_algebra) sets_Collect_countable_All:
  assumes "\<And>i. {x\<in>space M. P i x} \<in> sets M"
  shows "{x\<in>space M. \<forall>i::'i::countable. P i x} \<in> sets M"
proof -
  have "{x\<in>space M. \<forall>i::'i::countable. P i x} = (\<Inter>i. {x\<in>space M. P i x})" by auto
  with assms show ?thesis by auto
qed

lemma (in sigma_algebra) sets_Collect_countable_Ex:
  assumes "\<And>i. {x\<in>space M. P i x} \<in> sets M"
  shows "{x\<in>space M. \<exists>i::'i::countable. P i x} \<in> sets M"
proof -
  have "{x\<in>space M. \<exists>i::'i::countable. P i x} = (\<Union>i. {x\<in>space M. P i x})" by auto
  with assms show ?thesis by auto
qed

lemmas (in sigma_algebra) sets_Collect =
  sets_Collect_imp sets_Collect_disj sets_Collect_conj sets_Collect_neg sets_Collect_const
  sets_Collect_countable_All sets_Collect_countable_Ex sets_Collect_countable_All

lemma sigma_algebra_single_set:
  assumes "X \<subseteq> S"
  shows "sigma_algebra \<lparr> space = S, sets = { {}, X, S - X, S }\<rparr>"
  using algebra.is_sigma_algebra[OF algebra_single_set[OF `X \<subseteq> S`]] by simp

subsection {* Binary Unions *}

definition binary :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "binary a b =  (\<lambda>\<^isup>x. b)(0 := a)"

lemma range_binary_eq: "range(binary a b) = {a,b}"
  by (auto simp add: binary_def)

lemma Un_range_binary: "a \<union> b = (\<Union>i::nat. binary a b i)"
  by (simp add: SUP_def range_binary_eq)

lemma Int_range_binary: "a \<inter> b = (\<Inter>i::nat. binary a b i)"
  by (simp add: INF_def range_binary_eq)

lemma sigma_algebra_iff2:
     "sigma_algebra M \<longleftrightarrow>
       sets M \<subseteq> Pow (space M) \<and>
       {} \<in> sets M \<and> (\<forall>s \<in> sets M. space M - s \<in> sets M) \<and>
       (\<forall>A. range A \<subseteq> sets M \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"
  by (auto simp add: range_binary_eq sigma_algebra_def sigma_algebra_axioms_def
         algebra_iff_Un Un_range_binary)

subsection {* Initial Sigma Algebra *}

text {*Sigma algebras can naturally be created as the closure of any set of
  sets with regard to the properties just postulated.  *}

inductive_set
  sigma_sets :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  for sp :: "'a set" and A :: "'a set set"
  where
    Basic: "a \<in> A \<Longrightarrow> a \<in> sigma_sets sp A"
  | Empty: "{} \<in> sigma_sets sp A"
  | Compl: "a \<in> sigma_sets sp A \<Longrightarrow> sp - a \<in> sigma_sets sp A"
  | Union: "(\<And>i::nat. a i \<in> sigma_sets sp A) \<Longrightarrow> (\<Union>i. a i) \<in> sigma_sets sp A"

definition
  "sigma M = \<lparr> space = space M, sets = sigma_sets (space M) (sets M), \<dots> = more M \<rparr>"

lemma (in sigma_algebra) sigma_sets_subset:
  assumes a: "a \<subseteq> sets M"
  shows "sigma_sets (space M) a \<subseteq> sets M"
proof
  fix x
  assume "x \<in> sigma_sets (space M) a"
  from this show "x \<in> sets M"
    by (induct rule: sigma_sets.induct, auto) (metis a subsetD)
qed

lemma sigma_sets_into_sp: "A \<subseteq> Pow sp \<Longrightarrow> x \<in> sigma_sets sp A \<Longrightarrow> x \<subseteq> sp"
  by (erule sigma_sets.induct, auto)

lemma sigma_algebra_sigma_sets:
     "a \<subseteq> Pow (space M) \<Longrightarrow> sets M = sigma_sets (space M) a \<Longrightarrow> sigma_algebra M"
  by (auto simp add: sigma_algebra_iff2 dest: sigma_sets_into_sp
           intro!: sigma_sets.Union sigma_sets.Empty sigma_sets.Compl)

lemma sigma_sets_least_sigma_algebra:
  assumes "A \<subseteq> Pow S"
  shows "sigma_sets S A = \<Inter>{B. A \<subseteq> B \<and> sigma_algebra \<lparr>space = S, sets = B\<rparr>}"
proof safe
  fix B X assume "A \<subseteq> B" and sa: "sigma_algebra \<lparr> space = S, sets = B \<rparr>"
    and X: "X \<in> sigma_sets S A"
  from sigma_algebra.sigma_sets_subset[OF sa, simplified, OF `A \<subseteq> B`] X
  show "X \<in> B" by auto
next
  fix X assume "X \<in> \<Inter>{B. A \<subseteq> B \<and> sigma_algebra \<lparr>space = S, sets = B\<rparr>}"
  then have [intro!]: "\<And>B. A \<subseteq> B \<Longrightarrow> sigma_algebra \<lparr>space = S, sets = B\<rparr> \<Longrightarrow> X \<in> B"
     by simp
  have "A \<subseteq> sigma_sets S A" using assms
    by (auto intro!: sigma_sets.Basic)
  moreover have "sigma_algebra \<lparr>space = S, sets = sigma_sets S A\<rparr>"
    using assms by (intro sigma_algebra_sigma_sets[of A]) auto
  ultimately show "X \<in> sigma_sets S A" by auto
qed

lemma sets_sigma: "sets (sigma M) = sigma_sets (space M) (sets M)"
  unfolding sigma_def by simp

lemma space_sigma [simp]: "space (sigma M) = space M"
  by (simp add: sigma_def)

lemma sigma_sets_top: "sp \<in> sigma_sets sp A"
  by (metis Diff_empty sigma_sets.Compl sigma_sets.Empty)

lemma sigma_sets_Un:
  "a \<in> sigma_sets sp A \<Longrightarrow> b \<in> sigma_sets sp A \<Longrightarrow> a \<union> b \<in> sigma_sets sp A"
apply (simp add: Un_range_binary range_binary_eq)
apply (rule Union, simp add: binary_def)
done

lemma sigma_sets_Inter:
  assumes Asb: "A \<subseteq> Pow sp"
  shows "(\<And>i::nat. a i \<in> sigma_sets sp A) \<Longrightarrow> (\<Inter>i. a i) \<in> sigma_sets sp A"
proof -
  assume ai: "\<And>i::nat. a i \<in> sigma_sets sp A"
  hence "\<And>i::nat. sp-(a i) \<in> sigma_sets sp A"
    by (rule sigma_sets.Compl)
  hence "(\<Union>i. sp-(a i)) \<in> sigma_sets sp A"
    by (rule sigma_sets.Union)
  hence "sp-(\<Union>i. sp-(a i)) \<in> sigma_sets sp A"
    by (rule sigma_sets.Compl)
  also have "sp-(\<Union>i. sp-(a i)) = sp Int (\<Inter>i. a i)"
    by auto
  also have "... = (\<Inter>i. a i)" using ai
    by (blast dest: sigma_sets_into_sp [OF Asb])
  finally show ?thesis .
qed

lemma sigma_sets_INTER:
  assumes Asb: "A \<subseteq> Pow sp"
      and ai: "\<And>i::nat. i \<in> S \<Longrightarrow> a i \<in> sigma_sets sp A" and non: "S \<noteq> {}"
  shows "(\<Inter>i\<in>S. a i) \<in> sigma_sets sp A"
proof -
  from ai have "\<And>i. (if i\<in>S then a i else sp) \<in> sigma_sets sp A"
    by (simp add: sigma_sets.intros sigma_sets_top)
  hence "(\<Inter>i. (if i\<in>S then a i else sp)) \<in> sigma_sets sp A"
    by (rule sigma_sets_Inter [OF Asb])
  also have "(\<Inter>i. (if i\<in>S then a i else sp)) = (\<Inter>i\<in>S. a i)"
    by auto (metis ai non sigma_sets_into_sp subset_empty subset_iff Asb)+
  finally show ?thesis .
qed

lemma (in sigma_algebra) sigma_sets_eq:
     "sigma_sets (space M) (sets M) = sets M"
proof
  show "sets M \<subseteq> sigma_sets (space M) (sets M)"
    by (metis Set.subsetI sigma_sets.Basic)
  next
  show "sigma_sets (space M) (sets M) \<subseteq> sets M"
    by (metis sigma_sets_subset subset_refl)
qed

lemma sigma_sets_eqI:
  assumes A: "\<And>a. a \<in> A \<Longrightarrow> a \<in> sigma_sets M B"
  assumes B: "\<And>b. b \<in> B \<Longrightarrow> b \<in> sigma_sets M A"
  shows "sigma_sets M A = sigma_sets M B"
proof (intro set_eqI iffI)
  fix a assume "a \<in> sigma_sets M A"
  from this A show "a \<in> sigma_sets M B"
    by induct (auto intro!: sigma_sets.intros del: sigma_sets.Basic)
next
  fix b assume "b \<in> sigma_sets M B"
  from this B show "b \<in> sigma_sets M A"
    by induct (auto intro!: sigma_sets.intros del: sigma_sets.Basic)
qed

lemma sigma_algebra_sigma:
    "sets M \<subseteq> Pow (space M) \<Longrightarrow> sigma_algebra (sigma M)"
  apply (rule sigma_algebra_sigma_sets)
  apply (auto simp add: sigma_def)
  done

lemma (in sigma_algebra) sigma_subset:
    "sets N \<subseteq> sets M \<Longrightarrow> space N = space M \<Longrightarrow> sets (sigma N) \<subseteq> (sets M)"
  by (simp add: sigma_def sigma_sets_subset)

lemma sigma_sets_subseteq: assumes "A \<subseteq> B" shows "sigma_sets X A \<subseteq> sigma_sets X B"
proof
  fix x assume "x \<in> sigma_sets X A" then show "x \<in> sigma_sets X B"
    by induct (insert `A \<subseteq> B`, auto intro: sigma_sets.intros)
qed

lemma (in sigma_algebra) restriction_in_sets:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes "S \<in> sets M"
  and *: "range A \<subseteq> (\<lambda>A. S \<inter> A) ` sets M" (is "_ \<subseteq> ?r")
  shows "range A \<subseteq> sets M" "(\<Union>i. A i) \<in> (\<lambda>A. S \<inter> A) ` sets M"
proof -
  { fix i have "A i \<in> ?r" using * by auto
    hence "\<exists>B. A i = B \<inter> S \<and> B \<in> sets M" by auto
    hence "A i \<subseteq> S" "A i \<in> sets M" using `S \<in> sets M` by auto }
  thus "range A \<subseteq> sets M" "(\<Union>i. A i) \<in> (\<lambda>A. S \<inter> A) ` sets M"
    by (auto intro!: image_eqI[of _ _ "(\<Union>i. A i)"])
qed

lemma (in sigma_algebra) restricted_sigma_algebra:
  assumes "S \<in> sets M"
  shows "sigma_algebra (restricted_space S)"
  unfolding sigma_algebra_def sigma_algebra_axioms_def
proof safe
  show "algebra (restricted_space S)" using restricted_algebra[OF assms] .
next
  fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets (restricted_space S)"
  from restriction_in_sets[OF assms this[simplified]]
  show "(\<Union>i. A i) \<in> sets (restricted_space S)" by simp
qed

lemma sigma_sets_Int:
  assumes "A \<in> sigma_sets sp st" "A \<subseteq> sp"
  shows "op \<inter> A ` sigma_sets sp st = sigma_sets A (op \<inter> A ` st)"
proof (intro equalityI subsetI)
  fix x assume "x \<in> op \<inter> A ` sigma_sets sp st"
  then obtain y where "y \<in> sigma_sets sp st" "x = y \<inter> A" by auto
  then have "x \<in> sigma_sets (A \<inter> sp) (op \<inter> A ` st)"
  proof (induct arbitrary: x)
    case (Compl a)
    then show ?case
      by (force intro!: sigma_sets.Compl simp: Diff_Int_distrib ac_simps)
  next
    case (Union a)
    then show ?case
      by (auto intro!: sigma_sets.Union
               simp add: UN_extend_simps simp del: UN_simps)
  qed (auto intro!: sigma_sets.intros)
  then show "x \<in> sigma_sets A (op \<inter> A ` st)"
    using `A \<subseteq> sp` by (simp add: Int_absorb2)
next
  fix x assume "x \<in> sigma_sets A (op \<inter> A ` st)"
  then show "x \<in> op \<inter> A ` sigma_sets sp st"
  proof induct
    case (Compl a)
    then obtain x where "a = A \<inter> x" "x \<in> sigma_sets sp st" by auto
    then show ?case using `A \<subseteq> sp`
      by (force simp add: image_iff intro!: bexI[of _ "sp - x"] sigma_sets.Compl)
  next
    case (Union a)
    then have "\<forall>i. \<exists>x. x \<in> sigma_sets sp st \<and> a i = A \<inter> x"
      by (auto simp: image_iff Bex_def)
    from choice[OF this] guess f ..
    then show ?case
      by (auto intro!: bexI[of _ "(\<Union>x. f x)"] sigma_sets.Union
               simp add: image_iff)
  qed (auto intro!: sigma_sets.intros)
qed

lemma sigma_sets_single[simp]: "sigma_sets {X} {{X}} = {{}, {X}}"
proof (intro set_eqI iffI)
  fix x assume "x \<in> sigma_sets {X} {{X}}"
  from sigma_sets_into_sp[OF _ this]
  show "x \<in> {{}, {X}}" by auto
next
  fix x assume "x \<in> {{}, {X}}"
  then show "x \<in> sigma_sets {X} {{X}}"
    by (auto intro: sigma_sets.Empty sigma_sets_top)
qed

lemma (in sigma_algebra) sets_sigma_subset:
  assumes "space N = space M"
  assumes "sets N \<subseteq> sets M"
  shows "sets (sigma N) \<subseteq> sets M"
  by (unfold assms sets_sigma, rule sigma_sets_subset, rule assms)

lemma in_sigma[intro, simp]: "A \<in> sets M \<Longrightarrow> A \<in> sets (sigma M)"
  unfolding sigma_def by (auto intro!: sigma_sets.Basic)

lemma (in sigma_algebra) sigma_eq[simp]: "sigma M = M"
  unfolding sigma_def sigma_sets_eq by simp

lemma sigma_sigma_eq:
  assumes "sets M \<subseteq> Pow (space M)"
  shows "sigma (sigma M) = sigma M"
  using sigma_algebra.sigma_eq[OF sigma_algebra_sigma, OF assms] .

lemma sigma_sets_sigma_sets_eq:
  "M \<subseteq> Pow S \<Longrightarrow> sigma_sets S (sigma_sets S M) = sigma_sets S M"
  using sigma_sigma_eq[of "\<lparr> space = S, sets = M \<rparr>"]
  by (simp add: sigma_def)

lemma sigma_sets_singleton:
  assumes "X \<subseteq> S"
  shows "sigma_sets S { X } = { {}, X, S - X, S }"
proof -
  interpret sigma_algebra "\<lparr> space = S, sets = { {}, X, S - X, S }\<rparr>"
    by (rule sigma_algebra_single_set) fact
  have "sigma_sets S { X } \<subseteq> sigma_sets S { {}, X, S - X, S }"
    by (rule sigma_sets_subseteq) simp
  moreover have "\<dots> = { {}, X, S - X, S }"
    using sigma_eq unfolding sigma_def by simp
  moreover
  { fix A assume "A \<in> { {}, X, S - X, S }"
    then have "A \<in> sigma_sets S { X }"
      by (auto intro: sigma_sets.intros sigma_sets_top) }
  ultimately have "sigma_sets S { X } = sigma_sets S { {}, X, S - X, S }"
    by (intro antisym) auto
  with sigma_eq show ?thesis
    unfolding sigma_def by simp
qed

lemma restricted_sigma:
  assumes S: "S \<in> sets (sigma M)" and M: "sets M \<subseteq> Pow (space M)"
  shows "algebra.restricted_space (sigma M) S = sigma (algebra.restricted_space M S)"
proof -
  from S sigma_sets_into_sp[OF M]
  have "S \<in> sigma_sets (space M) (sets M)" "S \<subseteq> space M"
    by (auto simp: sigma_def)
  from sigma_sets_Int[OF this]
  show ?thesis
    by (simp add: sigma_def)
qed

lemma sigma_sets_vimage_commute:
  assumes X: "X \<in> space M \<rightarrow> space M'"
  shows "{X -` A \<inter> space M |A. A \<in> sets (sigma M')}
       = sigma_sets (space M) {X -` A \<inter> space M |A. A \<in> sets M'}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof clarify
    fix A assume "A \<in> sets (sigma M')"
    then have "A \<in> sigma_sets (space M') (sets M')" by (simp add: sets_sigma)
    then show "X -` A \<inter> space M \<in> ?R"
    proof induct
      case (Basic B) then show ?case
        by (auto intro!: sigma_sets.Basic)
    next
      case Empty then show ?case
        by (auto intro!: sigma_sets.Empty)
    next
      case (Compl B)
      have [simp]: "X -` (space M' - B) \<inter> space M = space M - (X -` B \<inter> space M)"
        by (auto simp add: funcset_mem [OF X])
      with Compl show ?case
        by (auto intro!: sigma_sets.Compl)
    next
      case (Union F)
      then show ?case
        by (auto simp add: vimage_UN UN_extend_simps(4) simp del: UN_simps
                 intro!: sigma_sets.Union)
    qed
  qed
  show "?R \<subseteq> ?L"
  proof clarify
    fix A assume "A \<in> ?R"
    then show "\<exists>B. A = X -` B \<inter> space M \<and> B \<in> sets (sigma M')"
    proof induct
      case (Basic B) then show ?case by auto
    next
      case Empty then show ?case
        by (auto simp: sets_sigma intro!: sigma_sets.Empty exI[of _ "{}"])
    next
      case (Compl B)
      then obtain A where A: "B = X -` A \<inter> space M" "A \<in> sets (sigma M')" by auto
      then have [simp]: "space M - B = X -` (space M' - A) \<inter> space M"
        by (auto simp add: funcset_mem [OF X])
      with A(2) show ?case
        by (auto simp: sets_sigma intro: sigma_sets.Compl)
    next
      case (Union F)
      then have "\<forall>i. \<exists>B. F i = X -` B \<inter> space M \<and> B \<in> sets (sigma M')" by auto
      from choice[OF this] guess A .. note A = this
      with A show ?case
        by (auto simp: sets_sigma vimage_UN[symmetric] intro: sigma_sets.Union)
    qed
  qed
qed

section {* Measurable functions *}

definition
  "measurable A B = {f \<in> space A -> space B. \<forall>y \<in> sets B. f -` y \<inter> space A \<in> sets A}"

lemma (in sigma_algebra) measurable_sigma:
  assumes B: "sets N \<subseteq> Pow (space N)"
      and f: "f \<in> space M -> space N"
      and ba: "\<And>y. y \<in> sets N \<Longrightarrow> (f -` y) \<inter> space M \<in> sets M"
  shows "f \<in> measurable M (sigma N)"
proof -
  have "sigma_sets (space N) (sets N) \<subseteq> {y . (f -` y) \<inter> space M \<in> sets M & y \<subseteq> space N}"
    proof clarify
      fix x
      assume "x \<in> sigma_sets (space N) (sets N)"
      thus "f -` x \<inter> space M \<in> sets M \<and> x \<subseteq> space N"
        proof induct
          case (Basic a)
          thus ?case
            by (auto simp add: ba) (metis B subsetD PowD)
        next
          case Empty
          thus ?case
            by auto
        next
          case (Compl a)
          have [simp]: "f -` space N \<inter> space M = space M"
            by (auto simp add: funcset_mem [OF f])
          thus ?case
            by (auto simp add: vimage_Diff Diff_Int_distrib2 compl_sets Compl)
        next
          case (Union a)
          thus ?case
            by (simp add: vimage_UN, simp only: UN_extend_simps(4)) blast
        qed
    qed
  thus ?thesis
    by (simp add: measurable_def sigma_algebra_axioms sigma_algebra_sigma B f)
       (auto simp add: sigma_def)
qed

lemma measurable_cong:
  assumes "\<And> w. w \<in> space M \<Longrightarrow> f w = g w"
  shows "f \<in> measurable M M' \<longleftrightarrow> g \<in> measurable M M'"
  unfolding measurable_def using assms
  by (simp cong: vimage_inter_cong Pi_cong)

lemma measurable_space:
  "f \<in> measurable M A \<Longrightarrow> x \<in> space M \<Longrightarrow> f x \<in> space A"
   unfolding measurable_def by auto

lemma measurable_sets:
  "f \<in> measurable M A \<Longrightarrow> S \<in> sets A \<Longrightarrow> f -` S \<inter> space M \<in> sets M"
   unfolding measurable_def by auto

lemma (in sigma_algebra) measurable_subset:
     "(\<And>S. S \<in> sets A \<Longrightarrow> S \<subseteq> space A) \<Longrightarrow> measurable M A \<subseteq> measurable M (sigma A)"
  by (auto intro: measurable_sigma measurable_sets measurable_space)

lemma measurable_eqI:
     "\<lbrakk> space m1 = space m1' ; space m2 = space m2' ;
        sets m1 = sets m1' ; sets m2 = sets m2' \<rbrakk>
      \<Longrightarrow> measurable m1 m2 = measurable m1' m2'"
  by (simp add: measurable_def sigma_algebra_iff2)

lemma (in sigma_algebra) measurable_const[intro, simp]:
  assumes "c \<in> space M'"
  shows "(\<lambda>x. c) \<in> measurable M M'"
  using assms by (auto simp add: measurable_def)

lemma (in sigma_algebra) measurable_If:
  assumes measure: "f \<in> measurable M M'" "g \<in> measurable M M'"
  assumes P: "{x\<in>space M. P x} \<in> sets M"
  shows "(\<lambda>x. if P x then f x else g x) \<in> measurable M M'"
  unfolding measurable_def
proof safe
  fix x assume "x \<in> space M"
  thus "(if P x then f x else g x) \<in> space M'"
    using measure unfolding measurable_def by auto
next
  fix A assume "A \<in> sets M'"
  hence *: "(\<lambda>x. if P x then f x else g x) -` A \<inter> space M =
    ((f -` A \<inter> space M) \<inter> {x\<in>space M. P x}) \<union>
    ((g -` A \<inter> space M) \<inter> (space M - {x\<in>space M. P x}))"
    using measure unfolding measurable_def by (auto split: split_if_asm)
  show "(\<lambda>x. if P x then f x else g x) -` A \<inter> space M \<in> sets M"
    using `A \<in> sets M'` measure P unfolding * measurable_def
    by (auto intro!: Un)
qed

lemma (in sigma_algebra) measurable_If_set:
  assumes measure: "f \<in> measurable M M'" "g \<in> measurable M M'"
  assumes P: "A \<in> sets M"
  shows "(\<lambda>x. if x \<in> A then f x else g x) \<in> measurable M M'"
proof (rule measurable_If[OF measure])
  have "{x \<in> space M. x \<in> A} = A" using `A \<in> sets M` sets_into_space by auto
  thus "{x \<in> space M. x \<in> A} \<in> sets M" using `A \<in> sets M` by auto
qed

lemma (in ring_of_sets) measurable_ident[intro, simp]: "id \<in> measurable M M"
  by (auto simp add: measurable_def)

lemma measurable_comp[intro]:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
  shows "f \<in> measurable a b \<Longrightarrow> g \<in> measurable b c \<Longrightarrow> (g o f) \<in> measurable a c"
  apply (auto simp add: measurable_def vimage_compose)
  apply (subgoal_tac "f -` g -` y \<inter> space a = f -` (g -` y \<inter> space b) \<inter> space a")
  apply force+
  done

lemma measurable_strong:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
  assumes f: "f \<in> measurable a b" and g: "g \<in> (space b -> space c)"
      and a: "sigma_algebra a" and b: "sigma_algebra b" and c: "sigma_algebra c"
      and t: "f ` (space a) \<subseteq> t"
      and cb: "\<And>s. s \<in> sets c \<Longrightarrow> (g -` s) \<inter> t \<in> sets b"
  shows "(g o f) \<in> measurable a c"
proof -
  have fab: "f \<in> (space a -> space b)"
   and ba: "\<And>y. y \<in> sets b \<Longrightarrow> (f -` y) \<inter> (space a) \<in> sets a" using f
     by (auto simp add: measurable_def)
  have eq: "f -` g -` y \<inter> space a = f -` (g -` y \<inter> t) \<inter> space a" using t
    by force
  show ?thesis
    apply (auto simp add: measurable_def vimage_compose a c)
    apply (metis funcset_mem fab g)
    apply (subst eq, metis ba cb)
    done
qed

lemma measurable_mono1:
     "a \<subseteq> b \<Longrightarrow> sigma_algebra \<lparr>space = X, sets = b\<rparr>
      \<Longrightarrow> measurable \<lparr>space = X, sets = a\<rparr> c \<subseteq> measurable \<lparr>space = X, sets = b\<rparr> c"
  by (auto simp add: measurable_def)

lemma measurable_up_sigma:
  "measurable A M \<subseteq> measurable (sigma A) M"
  unfolding measurable_def
  by (auto simp: sigma_def intro: sigma_sets.Basic)

lemma (in sigma_algebra) measurable_range_reduce:
   "\<lbrakk> f \<in> measurable M \<lparr>space = s, sets = Pow s\<rparr> ; s \<noteq> {} \<rbrakk>
    \<Longrightarrow> f \<in> measurable M \<lparr>space = s \<inter> (f ` space M), sets = Pow (s \<inter> (f ` space M))\<rparr>"
  by (simp add: measurable_def sigma_algebra_Pow del: Pow_Int_eq) blast

lemma (in sigma_algebra) measurable_Pow_to_Pow:
   "(sets M = Pow (space M)) \<Longrightarrow> f \<in> measurable M \<lparr>space = UNIV, sets = Pow UNIV\<rparr>"
  by (auto simp add: measurable_def sigma_algebra_def sigma_algebra_axioms_def algebra_def)

lemma (in sigma_algebra) measurable_Pow_to_Pow_image:
   "sets M = Pow (space M)
    \<Longrightarrow> f \<in> measurable M \<lparr>space = f ` space M, sets = Pow (f ` space M)\<rparr>"
  by (simp add: measurable_def sigma_algebra_Pow) intro_locales

lemma (in sigma_algebra) measurable_iff_sigma:
  assumes "sets E \<subseteq> Pow (space E)" and "f \<in> space M \<rightarrow> space E"
  shows "f \<in> measurable M (sigma E) \<longleftrightarrow> (\<forall>A\<in>sets E. f -` A \<inter> space M \<in> sets M)"
  using measurable_sigma[OF assms]
  by (fastforce simp: measurable_def sets_sigma intro: sigma_sets.intros)

section "Disjoint families"

definition
  disjoint_family_on  where
  "disjoint_family_on A S \<longleftrightarrow> (\<forall>m\<in>S. \<forall>n\<in>S. m \<noteq> n \<longrightarrow> A m \<inter> A n = {})"

abbreviation
  "disjoint_family A \<equiv> disjoint_family_on A UNIV"

lemma range_subsetD: "range f \<subseteq> B \<Longrightarrow> f i \<in> B"
  by blast

lemma Int_Diff_disjoint: "A \<inter> B \<inter> (A - B) = {}"
  by blast

lemma Int_Diff_Un: "A \<inter> B \<union> (A - B) = A"
  by blast

lemma disjoint_family_subset:
     "disjoint_family A \<Longrightarrow> (!!x. B x \<subseteq> A x) \<Longrightarrow> disjoint_family B"
  by (force simp add: disjoint_family_on_def)

lemma disjoint_family_on_bisimulation:
  assumes "disjoint_family_on f S"
  and "\<And>n m. n \<in> S \<Longrightarrow> m \<in> S \<Longrightarrow> n \<noteq> m \<Longrightarrow> f n \<inter> f m = {} \<Longrightarrow> g n \<inter> g m = {}"
  shows "disjoint_family_on g S"
  using assms unfolding disjoint_family_on_def by auto

lemma disjoint_family_on_mono:
  "A \<subseteq> B \<Longrightarrow> disjoint_family_on f B \<Longrightarrow> disjoint_family_on f A"
  unfolding disjoint_family_on_def by auto

lemma disjoint_family_Suc:
  assumes Suc: "!!n. A n \<subseteq> A (Suc n)"
  shows "disjoint_family (\<lambda>i. A (Suc i) - A i)"
proof -
  {
    fix m
    have "!!n. A n \<subseteq> A (m+n)"
    proof (induct m)
      case 0 show ?case by simp
    next
      case (Suc m) thus ?case
        by (metis Suc_eq_plus1 assms nat_add_commute nat_add_left_commute subset_trans)
    qed
  }
  hence "!!m n. m < n \<Longrightarrow> A m \<subseteq> A n"
    by (metis add_commute le_add_diff_inverse nat_less_le)
  thus ?thesis
    by (auto simp add: disjoint_family_on_def)
      (metis insert_absorb insert_subset le_SucE le_antisym not_leE)
qed

lemma setsum_indicator_disjoint_family:
  fixes f :: "'d \<Rightarrow> 'e::semiring_1"
  assumes d: "disjoint_family_on A P" and "x \<in> A j" and "finite P" and "j \<in> P"
  shows "(\<Sum>i\<in>P. f i * indicator (A i) x) = f j"
proof -
  have "P \<inter> {i. x \<in> A i} = {j}"
    using d `x \<in> A j` `j \<in> P` unfolding disjoint_family_on_def
    by auto
  thus ?thesis
    unfolding indicator_def
    by (simp add: if_distrib setsum_cases[OF `finite P`])
qed

definition disjointed :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set "
  where "disjointed A n = A n - (\<Union>i\<in>{0..<n}. A i)"

lemma finite_UN_disjointed_eq: "(\<Union>i\<in>{0..<n}. disjointed A i) = (\<Union>i\<in>{0..<n}. A i)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case by (simp add: atLeastLessThanSuc disjointed_def)
qed

lemma UN_disjointed_eq: "(\<Union>i. disjointed A i) = (\<Union>i. A i)"
  apply (rule UN_finite2_eq [where k=0])
  apply (simp add: finite_UN_disjointed_eq)
  done

lemma less_disjoint_disjointed: "m<n \<Longrightarrow> disjointed A m \<inter> disjointed A n = {}"
  by (auto simp add: disjointed_def)

lemma disjoint_family_disjointed: "disjoint_family (disjointed A)"
  by (simp add: disjoint_family_on_def)
     (metis neq_iff Int_commute less_disjoint_disjointed)

lemma disjointed_subset: "disjointed A n \<subseteq> A n"
  by (auto simp add: disjointed_def)

lemma (in ring_of_sets) UNION_in_sets:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes A: "range A \<subseteq> sets M "
  shows  "(\<Union>i\<in>{0..<n}. A i) \<in> sets M"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case
    by (simp add: atLeastLessThanSuc) (metis A Un UNIV_I image_subset_iff)
qed

lemma (in ring_of_sets) range_disjointed_sets:
  assumes A: "range A \<subseteq> sets M "
  shows  "range (disjointed A) \<subseteq> sets M"
proof (auto simp add: disjointed_def)
  fix n
  show "A n - (\<Union>i\<in>{0..<n}. A i) \<in> sets M" using UNION_in_sets
    by (metis A Diff UNIV_I image_subset_iff)
qed

lemma (in algebra) range_disjointed_sets':
  "range A \<subseteq> sets M \<Longrightarrow> range (disjointed A) \<subseteq> sets M"
  using range_disjointed_sets .

lemma disjointed_0[simp]: "disjointed A 0 = A 0"
  by (simp add: disjointed_def)

lemma incseq_Un:
  "incseq A \<Longrightarrow> (\<Union>i\<le>n. A i) = A n"
  unfolding incseq_def by auto

lemma disjointed_incseq:
  "incseq A \<Longrightarrow> disjointed A (Suc n) = A (Suc n) - A n"
  using incseq_Un[of A]
  by (simp add: disjointed_def atLeastLessThanSuc_atLeastAtMost atLeast0AtMost)

lemma sigma_algebra_disjoint_iff:
     "sigma_algebra M \<longleftrightarrow>
      algebra M &
      (\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow>
           (\<Union>i::nat. A i) \<in> sets M)"
proof (auto simp add: sigma_algebra_iff)
  fix A :: "nat \<Rightarrow> 'a set"
  assume M: "algebra M"
     and A: "range A \<subseteq> sets M"
     and UnA: "\<forall>A. range A \<subseteq> sets M \<longrightarrow>
               disjoint_family A \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  hence "range (disjointed A) \<subseteq> sets M \<longrightarrow>
         disjoint_family (disjointed A) \<longrightarrow>
         (\<Union>i. disjointed A i) \<in> sets M" by blast
  hence "(\<Union>i. disjointed A i) \<in> sets M"
    by (simp add: algebra.range_disjointed_sets' M A disjoint_family_disjointed)
  thus "(\<Union>i::nat. A i) \<in> sets M" by (simp add: UN_disjointed_eq)
qed

subsection {* Sigma algebra generated by function preimages *}

definition (in sigma_algebra)
  "vimage_algebra S f = \<lparr> space = S, sets = (\<lambda>A. f -` A \<inter> S) ` sets M, \<dots> = more M \<rparr>"

lemma (in sigma_algebra) in_vimage_algebra[simp]:
  "A \<in> sets (vimage_algebra S f) \<longleftrightarrow> (\<exists>B\<in>sets M. A = f -` B \<inter> S)"
  by (simp add: vimage_algebra_def image_iff)

lemma (in sigma_algebra) space_vimage_algebra[simp]:
  "space (vimage_algebra S f) = S"
  by (simp add: vimage_algebra_def)

lemma (in sigma_algebra) sigma_algebra_preimages:
  fixes f :: "'x \<Rightarrow> 'a"
  assumes "f \<in> A \<rightarrow> space M"
  shows "sigma_algebra \<lparr> space = A, sets = (\<lambda>M. f -` M \<inter> A) ` sets M \<rparr>"
    (is "sigma_algebra \<lparr> space = _, sets = ?F ` sets M \<rparr>")
proof (simp add: sigma_algebra_iff2, safe)
  show "{} \<in> ?F ` sets M" by blast
next
  fix S assume "S \<in> sets M"
  moreover have "A - ?F S = ?F (space M - S)"
    using assms by auto
  ultimately show "A - ?F S \<in> ?F ` sets M"
    by blast
next
  fix S :: "nat \<Rightarrow> 'x set" assume *: "range S \<subseteq> ?F ` sets M"
  have "\<forall>i. \<exists>b. b \<in> sets M \<and> S i = ?F b"
  proof safe
    fix i
    have "S i \<in> ?F ` sets M" using * by auto
    then show "\<exists>b. b \<in> sets M \<and> S i = ?F b" by auto
  qed
  from choice[OF this] obtain b where b: "range b \<subseteq> sets M" "\<And>i. S i = ?F (b i)"
    by auto
  then have "(\<Union>i. S i) = ?F (\<Union>i. b i)" by auto
  then show "(\<Union>i. S i) \<in> ?F ` sets M" using b(1) by blast
qed

lemma (in sigma_algebra) sigma_algebra_vimage:
  fixes S :: "'c set" assumes "f \<in> S \<rightarrow> space M"
  shows "sigma_algebra (vimage_algebra S f)"
proof -
  from sigma_algebra_preimages[OF assms]
  show ?thesis unfolding vimage_algebra_def by (auto simp: sigma_algebra_iff2)
qed

lemma (in sigma_algebra) measurable_vimage_algebra:
  fixes S :: "'c set" assumes "f \<in> S \<rightarrow> space M"
  shows "f \<in> measurable (vimage_algebra S f) M"
    unfolding measurable_def using assms by force

lemma (in sigma_algebra) measurable_vimage:
  fixes g :: "'a \<Rightarrow> 'c" and f :: "'d \<Rightarrow> 'a"
  assumes "g \<in> measurable M M2" "f \<in> S \<rightarrow> space M"
  shows "(\<lambda>x. g (f x)) \<in> measurable (vimage_algebra S f) M2"
proof -
  note measurable_vimage_algebra[OF assms(2)]
  from measurable_comp[OF this assms(1)]
  show ?thesis by (simp add: comp_def)
qed

lemma sigma_sets_vimage:
  assumes "f \<in> S' \<rightarrow> S" and "A \<subseteq> Pow S"
  shows "sigma_sets S' ((\<lambda>X. f -` X \<inter> S') ` A) = (\<lambda>X. f -` X \<inter> S') ` sigma_sets S A"
proof (intro set_eqI iffI)
  let ?F = "\<lambda>X. f -` X \<inter> S'"
  fix X assume "X \<in> sigma_sets S' (?F ` A)"
  then show "X \<in> ?F ` sigma_sets S A"
  proof induct
    case (Basic X) then obtain X' where "X = ?F X'" "X' \<in> A"
      by auto
    then show ?case by (auto intro!: sigma_sets.Basic)
  next
    case Empty then show ?case
      by (auto intro!: image_eqI[of _ _ "{}"] sigma_sets.Empty)
  next
    case (Compl X) then obtain X' where X: "X = ?F X'" and "X' \<in> sigma_sets S A"
      by auto
    then have "S - X' \<in> sigma_sets S A"
      by (auto intro!: sigma_sets.Compl)
    then show ?case
      using X assms by (auto intro!: image_eqI[where x="S - X'"])
  next
    case (Union F)
    then have "\<forall>i. \<exists>F'.  F' \<in> sigma_sets S A \<and> F i = f -` F' \<inter> S'"
      by (auto simp: image_iff Bex_def)
    from choice[OF this] obtain F' where
      "\<And>i. F' i \<in> sigma_sets S A" and "\<And>i. F i = f -` F' i \<inter> S'"
      by auto
    then show ?case
      by (auto intro!: sigma_sets.Union image_eqI[where x="\<Union>i. F' i"])
  qed
next
  let ?F = "\<lambda>X. f -` X \<inter> S'"
  fix X assume "X \<in> ?F ` sigma_sets S A"
  then obtain X' where "X' \<in> sigma_sets S A" "X = ?F X'" by auto
  then show "X \<in> sigma_sets S' (?F ` A)"
  proof (induct arbitrary: X)
    case (Basic X') then show ?case by (auto intro: sigma_sets.Basic)
  next
    case Empty then show ?case by (auto intro: sigma_sets.Empty)
  next
    case (Compl X')
    have "S' - (S' - X) \<in> sigma_sets S' (?F ` A)"
      apply (rule sigma_sets.Compl)
      using assms by (auto intro!: Compl.hyps simp: Compl.prems)
    also have "S' - (S' - X) = X"
      using assms Compl by auto
    finally show ?case .
  next
    case (Union F)
    have "(\<Union>i. f -` F i \<inter> S') \<in> sigma_sets S' (?F ` A)"
      by (intro sigma_sets.Union Union.hyps) simp
    also have "(\<Union>i. f -` F i \<inter> S') = X"
      using assms Union by auto
    finally show ?case .
  qed
qed

section {* Conditional space *}

definition (in algebra)
  "image_space X = \<lparr> space = X`space M, sets = (\<lambda>S. X`S) ` sets M, \<dots> = more M \<rparr>"

definition (in algebra)
  "conditional_space X A = algebra.image_space (restricted_space A) X"

lemma (in algebra) space_conditional_space:
  assumes "A \<in> sets M" shows "space (conditional_space X A) = X`A"
proof -
  interpret r: algebra "restricted_space A" using assms by (rule restricted_algebra)
  show ?thesis unfolding conditional_space_def r.image_space_def
    by simp
qed

subsection {* A Two-Element Series *}

definition binaryset :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set "
  where "binaryset A B = (\<lambda>\<^isup>x. {})(0 := A, Suc 0 := B)"

lemma range_binaryset_eq: "range(binaryset A B) = {A,B,{}}"
  apply (simp add: binaryset_def)
  apply (rule set_eqI)
  apply (auto simp add: image_iff)
  done

lemma UN_binaryset_eq: "(\<Union>i. binaryset A B i) = A \<union> B"
  by (simp add: SUP_def range_binaryset_eq)

section {* Closed CDI *}

definition
  closed_cdi  where
  "closed_cdi M \<longleftrightarrow>
   sets M \<subseteq> Pow (space M) &
   (\<forall>s \<in> sets M. space M - s \<in> sets M) &
   (\<forall>A. (range A \<subseteq> sets M) & (A 0 = {}) & (\<forall>n. A n \<subseteq> A (Suc n)) \<longrightarrow>
        (\<Union>i. A i) \<in> sets M) &
   (\<forall>A. (range A \<subseteq> sets M) & disjoint_family A \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M)"

inductive_set
  smallest_ccdi_sets :: "('a, 'b) algebra_scheme \<Rightarrow> 'a set set"
  for M
  where
    Basic [intro]:
      "a \<in> sets M \<Longrightarrow> a \<in> smallest_ccdi_sets M"
  | Compl [intro]:
      "a \<in> smallest_ccdi_sets M \<Longrightarrow> space M - a \<in> smallest_ccdi_sets M"
  | Inc:
      "range A \<in> Pow(smallest_ccdi_sets M) \<Longrightarrow> A 0 = {} \<Longrightarrow> (\<And>n. A n \<subseteq> A (Suc n))
       \<Longrightarrow> (\<Union>i. A i) \<in> smallest_ccdi_sets M"
  | Disj:
      "range A \<in> Pow(smallest_ccdi_sets M) \<Longrightarrow> disjoint_family A
       \<Longrightarrow> (\<Union>i::nat. A i) \<in> smallest_ccdi_sets M"


definition
  smallest_closed_cdi  where
  "smallest_closed_cdi M = (|space = space M, sets = smallest_ccdi_sets M|)"

lemma space_smallest_closed_cdi [simp]:
     "space (smallest_closed_cdi M) = space M"
  by (simp add: smallest_closed_cdi_def)

lemma (in algebra) smallest_closed_cdi1: "sets M \<subseteq> sets (smallest_closed_cdi M)"
  by (auto simp add: smallest_closed_cdi_def)

lemma (in algebra) smallest_ccdi_sets:
     "smallest_ccdi_sets M \<subseteq> Pow (space M)"
  apply (rule subsetI)
  apply (erule smallest_ccdi_sets.induct)
  apply (auto intro: range_subsetD dest: sets_into_space)
  done

lemma (in algebra) smallest_closed_cdi2: "closed_cdi (smallest_closed_cdi M)"
  apply (auto simp add: closed_cdi_def smallest_closed_cdi_def smallest_ccdi_sets)
  apply (blast intro: smallest_ccdi_sets.Inc smallest_ccdi_sets.Disj) +
  done

lemma (in algebra) smallest_closed_cdi3:
     "sets (smallest_closed_cdi M) \<subseteq> Pow (space M)"
  by (simp add: smallest_closed_cdi_def smallest_ccdi_sets)

lemma closed_cdi_subset: "closed_cdi M \<Longrightarrow> sets M \<subseteq> Pow (space M)"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Compl: "closed_cdi M \<Longrightarrow> s \<in> sets M \<Longrightarrow> space M - s \<in> sets M"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Inc:
     "closed_cdi M \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> A 0 = {} \<Longrightarrow> (!!n. A n \<subseteq> A (Suc n)) \<Longrightarrow>
        (\<Union>i. A i) \<in> sets M"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Disj:
     "closed_cdi M \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  by (simp add: closed_cdi_def)

lemma closed_cdi_Un:
  assumes cdi: "closed_cdi M" and empty: "{} \<in> sets M"
      and A: "A \<in> sets M" and B: "B \<in> sets M"
      and disj: "A \<inter> B = {}"
    shows "A \<union> B \<in> sets M"
proof -
  have ra: "range (binaryset A B) \<subseteq> sets M"
   by (simp add: range_binaryset_eq empty A B)
 have di:  "disjoint_family (binaryset A B)" using disj
   by (simp add: disjoint_family_on_def binaryset_def Int_commute)
 from closed_cdi_Disj [OF cdi ra di]
 show ?thesis
   by (simp add: UN_binaryset_eq)
qed

lemma (in algebra) smallest_ccdi_sets_Un:
  assumes A: "A \<in> smallest_ccdi_sets M" and B: "B \<in> smallest_ccdi_sets M"
      and disj: "A \<inter> B = {}"
    shows "A \<union> B \<in> smallest_ccdi_sets M"
proof -
  have ra: "range (binaryset A B) \<in> Pow (smallest_ccdi_sets M)"
    by (simp add: range_binaryset_eq  A B smallest_ccdi_sets.Basic)
  have di:  "disjoint_family (binaryset A B)" using disj
    by (simp add: disjoint_family_on_def binaryset_def Int_commute)
  from Disj [OF ra di]
  show ?thesis
    by (simp add: UN_binaryset_eq)
qed

lemma (in algebra) smallest_ccdi_sets_Int1:
  assumes a: "a \<in> sets M"
  shows "b \<in> smallest_ccdi_sets M \<Longrightarrow> a \<inter> b \<in> smallest_ccdi_sets M"
proof (induct rule: smallest_ccdi_sets.induct)
  case (Basic x)
  thus ?case
    by (metis a Int smallest_ccdi_sets.Basic)
next
  case (Compl x)
  have "a \<inter> (space M - x) = space M - ((space M - a) \<union> (a \<inter> x))"
    by blast
  also have "... \<in> smallest_ccdi_sets M"
    by (metis smallest_ccdi_sets.Compl a Compl(2) Diff_Int2 Diff_Int_distrib2
           Diff_disjoint Int_Diff Int_empty_right Un_commute
           smallest_ccdi_sets.Basic smallest_ccdi_sets.Compl
           smallest_ccdi_sets_Un)
  finally show ?case .
next
  case (Inc A)
  have 1: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) = a \<inter> (\<Union>i. A i)"
    by blast
  have "range (\<lambda>i. a \<inter> A i) \<in> Pow(smallest_ccdi_sets M)" using Inc
    by blast
  moreover have "(\<lambda>i. a \<inter> A i) 0 = {}"
    by (simp add: Inc)
  moreover have "!!n. (\<lambda>i. a \<inter> A i) n \<subseteq> (\<lambda>i. a \<inter> A i) (Suc n)" using Inc
    by blast
  ultimately have 2: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Inc)
  show ?case
    by (metis 1 2)
next
  case (Disj A)
  have 1: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) = a \<inter> (\<Union>i. A i)"
    by blast
  have "range (\<lambda>i. a \<inter> A i) \<in> Pow(smallest_ccdi_sets M)" using Disj
    by blast
  moreover have "disjoint_family (\<lambda>i. a \<inter> A i)" using Disj
    by (auto simp add: disjoint_family_on_def)
  ultimately have 2: "(\<Union>i. (\<lambda>i. a \<inter> A i) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Disj)
  show ?case
    by (metis 1 2)
qed


lemma (in algebra) smallest_ccdi_sets_Int:
  assumes b: "b \<in> smallest_ccdi_sets M"
  shows "a \<in> smallest_ccdi_sets M \<Longrightarrow> a \<inter> b \<in> smallest_ccdi_sets M"
proof (induct rule: smallest_ccdi_sets.induct)
  case (Basic x)
  thus ?case
    by (metis b smallest_ccdi_sets_Int1)
next
  case (Compl x)
  have "(space M - x) \<inter> b = space M - (x \<inter> b \<union> (space M - b))"
    by blast
  also have "... \<in> smallest_ccdi_sets M"
    by (metis Compl(2) Diff_disjoint Int_Diff Int_commute Int_empty_right b
           smallest_ccdi_sets.Compl smallest_ccdi_sets_Un)
  finally show ?case .
next
  case (Inc A)
  have 1: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) = (\<Union>i. A i) \<inter> b"
    by blast
  have "range (\<lambda>i. A i \<inter> b) \<in> Pow(smallest_ccdi_sets M)" using Inc
    by blast
  moreover have "(\<lambda>i. A i \<inter> b) 0 = {}"
    by (simp add: Inc)
  moreover have "!!n. (\<lambda>i. A i \<inter> b) n \<subseteq> (\<lambda>i. A i \<inter> b) (Suc n)" using Inc
    by blast
  ultimately have 2: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Inc)
  show ?case
    by (metis 1 2)
next
  case (Disj A)
  have 1: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) = (\<Union>i. A i) \<inter> b"
    by blast
  have "range (\<lambda>i. A i \<inter> b) \<in> Pow(smallest_ccdi_sets M)" using Disj
    by blast
  moreover have "disjoint_family (\<lambda>i. A i \<inter> b)" using Disj
    by (auto simp add: disjoint_family_on_def)
  ultimately have 2: "(\<Union>i. (\<lambda>i. A i \<inter> b) i) \<in> smallest_ccdi_sets M"
    by (rule smallest_ccdi_sets.Disj)
  show ?case
    by (metis 1 2)
qed

lemma (in algebra) sets_smallest_closed_cdi_Int:
   "a \<in> sets (smallest_closed_cdi M) \<Longrightarrow> b \<in> sets (smallest_closed_cdi M)
    \<Longrightarrow> a \<inter> b \<in> sets (smallest_closed_cdi M)"
  by (simp add: smallest_ccdi_sets_Int smallest_closed_cdi_def)

lemma (in algebra) sigma_property_disjoint_lemma:
  assumes sbC: "sets M \<subseteq> C"
      and ccdi: "closed_cdi (|space = space M, sets = C|)"
  shows "sigma_sets (space M) (sets M) \<subseteq> C"
proof -
  have "smallest_ccdi_sets M \<in> {B . sets M \<subseteq> B \<and> sigma_algebra (|space = space M, sets = B|)}"
    apply (auto simp add: sigma_algebra_disjoint_iff algebra_iff_Int
            smallest_ccdi_sets_Int)
    apply (metis Union_Pow_eq Union_upper subsetD smallest_ccdi_sets)
    apply (blast intro: smallest_ccdi_sets.Disj)
    done
  hence "sigma_sets (space M) (sets M) \<subseteq> smallest_ccdi_sets M"
    by clarsimp
       (drule sigma_algebra.sigma_sets_subset [where a="sets M"], auto)
  also have "...  \<subseteq> C"
    proof
      fix x
      assume x: "x \<in> smallest_ccdi_sets M"
      thus "x \<in> C"
        proof (induct rule: smallest_ccdi_sets.induct)
          case (Basic x)
          thus ?case
            by (metis Basic subsetD sbC)
        next
          case (Compl x)
          thus ?case
            by (blast intro: closed_cdi_Compl [OF ccdi, simplified])
        next
          case (Inc A)
          thus ?case
               by (auto intro: closed_cdi_Inc [OF ccdi, simplified])
        next
          case (Disj A)
          thus ?case
               by (auto intro: closed_cdi_Disj [OF ccdi, simplified])
        qed
    qed
  finally show ?thesis .
qed

lemma (in algebra) sigma_property_disjoint:
  assumes sbC: "sets M \<subseteq> C"
      and compl: "!!s. s \<in> C \<inter> sigma_sets (space M) (sets M) \<Longrightarrow> space M - s \<in> C"
      and inc: "!!A. range A \<subseteq> C \<inter> sigma_sets (space M) (sets M)
                     \<Longrightarrow> A 0 = {} \<Longrightarrow> (!!n. A n \<subseteq> A (Suc n))
                     \<Longrightarrow> (\<Union>i. A i) \<in> C"
      and disj: "!!A. range A \<subseteq> C \<inter> sigma_sets (space M) (sets M)
                      \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Union>i::nat. A i) \<in> C"
  shows "sigma_sets (space M) (sets M) \<subseteq> C"
proof -
  have "sigma_sets (space M) (sets M) \<subseteq> C \<inter> sigma_sets (space M) (sets M)"
    proof (rule sigma_property_disjoint_lemma)
      show "sets M \<subseteq> C \<inter> sigma_sets (space M) (sets M)"
        by (metis Int_greatest Set.subsetI sbC sigma_sets.Basic)
    next
      show "closed_cdi \<lparr>space = space M, sets = C \<inter> sigma_sets (space M) (sets M)\<rparr>"
        by (simp add: closed_cdi_def compl inc disj)
           (metis PowI Set.subsetI le_infI2 sigma_sets_into_sp space_closed
             IntE sigma_sets.Compl range_subsetD sigma_sets.Union)
    qed
  thus ?thesis
    by blast
qed

section {* Dynkin systems *}

locale dynkin_system = subset_class +
  assumes space: "space M \<in> sets M"
    and   compl[intro!]: "\<And>A. A \<in> sets M \<Longrightarrow> space M - A \<in> sets M"
    and   UN[intro!]: "\<And>A. disjoint_family A \<Longrightarrow> range A \<subseteq> sets M
                           \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"

lemma (in dynkin_system) empty[intro, simp]: "{} \<in> sets M"
  using space compl[of "space M"] by simp

lemma (in dynkin_system) diff:
  assumes sets: "D \<in> sets M" "E \<in> sets M" and "D \<subseteq> E"
  shows "E - D \<in> sets M"
proof -
  let ?f = "\<lambda>x. if x = 0 then D else if x = Suc 0 then space M - E else {}"
  have "range ?f = {D, space M - E, {}}"
    by (auto simp: image_iff)
  moreover have "D \<union> (space M - E) = (\<Union>i. ?f i)"
    by (auto simp: image_iff split: split_if_asm)
  moreover
  then have "disjoint_family ?f" unfolding disjoint_family_on_def
    using `D \<in> sets M`[THEN sets_into_space] `D \<subseteq> E` by auto
  ultimately have "space M - (D \<union> (space M - E)) \<in> sets M"
    using sets by auto
  also have "space M - (D \<union> (space M - E)) = E - D"
    using assms sets_into_space by auto
  finally show ?thesis .
qed

lemma dynkin_systemI:
  assumes "\<And> A. A \<in> sets M \<Longrightarrow> A \<subseteq> space M" "space M \<in> sets M"
  assumes "\<And> A. A \<in> sets M \<Longrightarrow> space M - A \<in> sets M"
  assumes "\<And> A. disjoint_family A \<Longrightarrow> range A \<subseteq> sets M
          \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  shows "dynkin_system M"
  using assms by (auto simp: dynkin_system_def dynkin_system_axioms_def subset_class_def)

lemma dynkin_systemI':
  assumes 1: "\<And> A. A \<in> sets M \<Longrightarrow> A \<subseteq> space M"
  assumes empty: "{} \<in> sets M"
  assumes Diff: "\<And> A. A \<in> sets M \<Longrightarrow> space M - A \<in> sets M"
  assumes 2: "\<And> A. disjoint_family A \<Longrightarrow> range A \<subseteq> sets M
          \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  shows "dynkin_system M"
proof -
  from Diff[OF empty] have "space M \<in> sets M" by auto
  from 1 this Diff 2 show ?thesis
    by (intro dynkin_systemI) auto
qed

lemma dynkin_system_trivial:
  shows "dynkin_system \<lparr> space = A, sets = Pow A \<rparr>"
  by (rule dynkin_systemI) auto

lemma sigma_algebra_imp_dynkin_system:
  assumes "sigma_algebra M" shows "dynkin_system M"
proof -
  interpret sigma_algebra M by fact
  show ?thesis using sets_into_space by (fastforce intro!: dynkin_systemI)
qed

subsection "Intersection stable algebras"

definition "Int_stable M \<longleftrightarrow> (\<forall> a \<in> sets M. \<forall> b \<in> sets M. a \<inter> b \<in> sets M)"

lemma (in algebra) Int_stable: "Int_stable M"
  unfolding Int_stable_def by auto

lemma Int_stableI:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<inter> b \<in> A) \<Longrightarrow> Int_stable \<lparr> space = \<Omega>, sets = A \<rparr>"
  unfolding Int_stable_def by auto

lemma Int_stableD:
  "Int_stable M \<Longrightarrow> a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<inter> b \<in> sets M"
  unfolding Int_stable_def by auto

lemma (in dynkin_system) sigma_algebra_eq_Int_stable:
  "sigma_algebra M \<longleftrightarrow> Int_stable M"
proof
  assume "sigma_algebra M" then show "Int_stable M"
    unfolding sigma_algebra_def using algebra.Int_stable by auto
next
  assume "Int_stable M"
  show "sigma_algebra M"
    unfolding sigma_algebra_disjoint_iff algebra_iff_Un
  proof (intro conjI ballI allI impI)
    show "sets M \<subseteq> Pow (space M)" using sets_into_space by auto
  next
    fix A B assume "A \<in> sets M" "B \<in> sets M"
    then have "A \<union> B = space M - ((space M - A) \<inter> (space M - B))"
              "space M - A \<in> sets M" "space M - B \<in> sets M"
      using sets_into_space by auto
    then show "A \<union> B \<in> sets M"
      using `Int_stable M` unfolding Int_stable_def by auto
  qed auto
qed

subsection "Smallest Dynkin systems"

definition dynkin where
  "dynkin M = \<lparr> space = space M,
     sets = \<Inter>{D. dynkin_system \<lparr> space = space M, sets = D \<rparr> \<and> sets M \<subseteq> D},
     \<dots> = more M \<rparr>"

lemma dynkin_system_dynkin:
  assumes "sets M \<subseteq> Pow (space M)"
  shows "dynkin_system (dynkin M)"
proof (rule dynkin_systemI)
  fix A assume "A \<in> sets (dynkin M)"
  moreover
  { fix D assume "A \<in> D" and d: "dynkin_system \<lparr> space = space M, sets = D \<rparr>"
    then have "A \<subseteq> space M" by (auto simp: dynkin_system_def subset_class_def) }
  moreover have "{D. dynkin_system \<lparr> space = space M, sets = D\<rparr> \<and> sets M \<subseteq> D} \<noteq> {}"
    using assms dynkin_system_trivial by fastforce
  ultimately show "A \<subseteq> space (dynkin M)"
    unfolding dynkin_def using assms
    by simp (metis dynkin_system_def subset_class_def in_mono)
next
  show "space (dynkin M) \<in> sets (dynkin M)"
    unfolding dynkin_def using dynkin_system.space by fastforce
next
  fix A assume "A \<in> sets (dynkin M)"
  then show "space (dynkin M) - A \<in> sets (dynkin M)"
    unfolding dynkin_def using dynkin_system.compl by force
next
  fix A :: "nat \<Rightarrow> 'a set"
  assume A: "disjoint_family A" "range A \<subseteq> sets (dynkin M)"
  show "(\<Union>i. A i) \<in> sets (dynkin M)" unfolding dynkin_def
  proof (simp, safe)
    fix D assume "dynkin_system \<lparr>space = space M, sets = D\<rparr>" "sets M \<subseteq> D"
    with A have "(\<Union>i. A i) \<in> sets \<lparr>space = space M, sets = D\<rparr>"
      by (intro dynkin_system.UN) (auto simp: dynkin_def)
    then show "(\<Union>i. A i) \<in> D" by auto
  qed
qed

lemma dynkin_Basic[intro]:
  "A \<in> sets M \<Longrightarrow> A \<in> sets (dynkin M)"
  unfolding dynkin_def by auto

lemma dynkin_space[simp]:
  "space (dynkin M) = space M"
  unfolding dynkin_def by auto

lemma (in dynkin_system) restricted_dynkin_system:
  assumes "D \<in> sets M"
  shows "dynkin_system \<lparr> space = space M,
                         sets = {Q. Q \<subseteq> space M \<and> Q \<inter> D \<in> sets M} \<rparr>"
proof (rule dynkin_systemI, simp_all)
  have "space M \<inter> D = D"
    using `D \<in> sets M` sets_into_space by auto
  then show "space M \<inter> D \<in> sets M"
    using `D \<in> sets M` by auto
next
  fix A assume "A \<subseteq> space M \<and> A \<inter> D \<in> sets M"
  moreover have "(space M - A) \<inter> D = (space M - (A \<inter> D)) - (space M - D)"
    by auto
  ultimately show "space M - A \<subseteq> space M \<and> (space M - A) \<inter> D \<in> sets M"
    using  `D \<in> sets M` by (auto intro: diff)
next
  fix A :: "nat \<Rightarrow> 'a set"
  assume "disjoint_family A" "range A \<subseteq> {Q. Q \<subseteq> space M \<and> Q \<inter> D \<in> sets M}"
  then have "\<And>i. A i \<subseteq> space M" "disjoint_family (\<lambda>i. A i \<inter> D)"
    "range (\<lambda>i. A i \<inter> D) \<subseteq> sets M" "(\<Union>x. A x) \<inter> D = (\<Union>x. A x \<inter> D)"
    by ((fastforce simp: disjoint_family_on_def)+)
  then show "(\<Union>x. A x) \<subseteq> space M \<and> (\<Union>x. A x) \<inter> D \<in> sets M"
    by (auto simp del: UN_simps)
qed

lemma (in dynkin_system) dynkin_subset:
  assumes "sets N \<subseteq> sets M"
  assumes "space N = space M"
  shows "sets (dynkin N) \<subseteq> sets M"
proof -
  have "dynkin_system M" by default
  then have "dynkin_system \<lparr>space = space N, sets = sets M \<rparr>"
    using assms unfolding dynkin_system_def dynkin_system_axioms_def subset_class_def by simp
  with `sets N \<subseteq> sets M` show ?thesis by (auto simp add: dynkin_def)
qed

lemma sigma_eq_dynkin:
  assumes sets: "sets M \<subseteq> Pow (space M)"
  assumes "Int_stable M"
  shows "sigma M = dynkin M"
proof -
  have "sets (dynkin M) \<subseteq> sigma_sets (space M) (sets M)"
    using sigma_algebra_imp_dynkin_system
    unfolding dynkin_def sigma_def sigma_sets_least_sigma_algebra[OF sets] by auto
  moreover
  interpret dynkin_system "dynkin M"
    using dynkin_system_dynkin[OF sets] .
  have "sigma_algebra (dynkin M)"
    unfolding sigma_algebra_eq_Int_stable Int_stable_def
  proof (intro ballI)
    fix A B assume "A \<in> sets (dynkin M)" "B \<in> sets (dynkin M)"
    let ?D = "\<lambda>E. \<lparr> space = space M,
                    sets = {Q. Q \<subseteq> space M \<and> Q \<inter> E \<in> sets (dynkin M)} \<rparr>"
    have "sets M \<subseteq> sets (?D B)"
    proof
      fix E assume "E \<in> sets M"
      then have "sets M \<subseteq> sets (?D E)" "E \<in> sets (dynkin M)"
        using sets_into_space `Int_stable M` by (auto simp: Int_stable_def)
      then have "sets (dynkin M) \<subseteq> sets (?D E)"
        using restricted_dynkin_system `E \<in> sets (dynkin M)`
        by (intro dynkin_system.dynkin_subset) simp_all
      then have "B \<in> sets (?D E)"
        using `B \<in> sets (dynkin M)` by auto
      then have "E \<inter> B \<in> sets (dynkin M)"
        by (subst Int_commute) simp
      then show "E \<in> sets (?D B)"
        using sets `E \<in> sets M` by auto
    qed
    then have "sets (dynkin M) \<subseteq> sets (?D B)"
      using restricted_dynkin_system `B \<in> sets (dynkin M)`
      by (intro dynkin_system.dynkin_subset) simp_all
    then show "A \<inter> B \<in> sets (dynkin M)"
      using `A \<in> sets (dynkin M)` sets_into_space by auto
  qed
  from sigma_algebra.sigma_sets_subset[OF this, of "sets M"]
  have "sigma_sets (space M) (sets M) \<subseteq> sets (dynkin M)" by auto
  ultimately have "sigma_sets (space M) (sets M) = sets (dynkin M)" by auto
  then show ?thesis
    by (auto intro!: algebra.equality simp: sigma_def dynkin_def)
qed

lemma (in dynkin_system) dynkin_idem:
  "dynkin M = M"
proof -
  have "sets (dynkin M) = sets M"
  proof
    show "sets M \<subseteq> sets (dynkin M)"
      using dynkin_Basic by auto
    show "sets (dynkin M) \<subseteq> sets M"
      by (intro dynkin_subset) auto
  qed
  then show ?thesis
    by (auto intro!: algebra.equality simp: dynkin_def)
qed

lemma (in dynkin_system) dynkin_lemma:
  assumes "Int_stable E"
  and E: "sets E \<subseteq> sets M" "space E = space M" "sets M \<subseteq> sets (sigma E)"
  shows "sets (sigma E) = sets M"
proof -
  have "sets E \<subseteq> Pow (space E)"
    using E sets_into_space by force
  then have "sigma E = dynkin E"
    using `Int_stable E` by (rule sigma_eq_dynkin)
  moreover then have "sets (dynkin E) = sets M"
    using assms dynkin_subset[OF E(1,2)] by simp
  ultimately show ?thesis
    using assms by (auto intro!: algebra.equality simp: dynkin_def)
qed

subsection "Sigma algebras on finite sets"

locale finite_sigma_algebra = sigma_algebra +
  assumes finite_space: "finite (space M)"
  and sets_eq_Pow[simp]: "sets M = Pow (space M)"

lemma (in finite_sigma_algebra) sets_image_space_eq_Pow:
  "sets (image_space X) = Pow (space (image_space X))"
proof safe
  fix x S assume "S \<in> sets (image_space X)" "x \<in> S"
  then show "x \<in> space (image_space X)"
    using sets_into_space by (auto intro!: imageI simp: image_space_def)
next
  fix S assume "S \<subseteq> space (image_space X)"
  then obtain S' where "S = X`S'" "S'\<in>sets M"
    by (auto simp: subset_image_iff image_space_def)
  then show "S \<in> sets (image_space X)"
    by (auto simp: image_space_def)
qed

lemma measurable_sigma_sigma:
  assumes M: "sets M \<subseteq> Pow (space M)" and N: "sets N \<subseteq> Pow (space N)"
  shows "f \<in> measurable M N \<Longrightarrow> f \<in> measurable (sigma M) (sigma N)"
  using sigma_algebra.measurable_subset[OF sigma_algebra_sigma[OF M], of N]
  using measurable_up_sigma[of M N] N by auto

lemma (in sigma_algebra) measurable_Least:
  assumes meas: "\<And>i::nat. {x\<in>space M. P i x} \<in> sets M"
  shows "(\<lambda>x. LEAST j. P j x) -` A \<inter> space M \<in> sets M"
proof -
  { fix i have "(\<lambda>x. LEAST j. P j x) -` {i} \<inter> space M \<in> sets M"
    proof cases
      assume i: "(LEAST j. False) = i"
      have "(\<lambda>x. LEAST j. P j x) -` {i} \<inter> space M =
        {x\<in>space M. P i x} \<inter> (space M - (\<Union>j<i. {x\<in>space M. P j x})) \<union> (space M - (\<Union>i. {x\<in>space M. P i x}))"
        by (simp add: set_eq_iff, safe)
           (insert i, auto dest: Least_le intro: LeastI intro!: Least_equality)
      with meas show ?thesis
        by (auto intro!: Int)
    next
      assume i: "(LEAST j. False) \<noteq> i"
      then have "(\<lambda>x. LEAST j. P j x) -` {i} \<inter> space M =
        {x\<in>space M. P i x} \<inter> (space M - (\<Union>j<i. {x\<in>space M. P j x}))"
      proof (simp add: set_eq_iff, safe)
        fix x assume neq: "(LEAST j. False) \<noteq> (LEAST j. P j x)"
        have "\<exists>j. P j x"
          by (rule ccontr) (insert neq, auto)
        then show "P (LEAST j. P j x) x" by (rule LeastI_ex)
      qed (auto dest: Least_le intro!: Least_equality)
      with meas show ?thesis
        by (auto intro!: Int)
    qed }
  then have "(\<Union>i\<in>A. (\<lambda>x. LEAST j. P j x) -` {i} \<inter> space M) \<in> sets M"
    by (intro countable_UN) auto
  moreover have "(\<Union>i\<in>A. (\<lambda>x. LEAST j. P j x) -` {i} \<inter> space M) =
    (\<lambda>x. LEAST j. P j x) -` A \<inter> space M" by auto
  ultimately show ?thesis by auto
qed

end
