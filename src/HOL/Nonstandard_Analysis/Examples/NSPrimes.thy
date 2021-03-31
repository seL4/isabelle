(*  Title       : NSPrimes.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2002 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

section \<open>The Nonstandard Primes as an Extension of the Prime Numbers\<close>

theory NSPrimes
  imports "HOL-Computational_Algebra.Primes" "HOL-Nonstandard_Analysis.Hyperreal"
begin

text \<open>These can be used to derive an alternative proof of the infinitude of
primes by considering a property of nonstandard sets.\<close>

definition starprime :: "hypnat set"
  where [transfer_unfold]: "starprime = *s* {p. prime p}"

definition choicefun :: "'a set \<Rightarrow> 'a"
  where "choicefun E = (SOME x. \<exists>X \<in> Pow E - {{}}. x \<in> X)"

primrec injf_max :: "nat \<Rightarrow> 'a::order set \<Rightarrow> 'a"
where
  injf_max_zero: "injf_max 0 E = choicefun E"
| injf_max_Suc: "injf_max (Suc n) E = choicefun ({e. e \<in> E \<and> injf_max n E < e})"

lemma dvd_by_all2: "\<exists>N>0. \<forall>m. 0 < m \<and> m \<le> M \<longrightarrow> m dvd N"
  for M :: nat
  apply (induct M)
   apply auto
  apply (rule_tac x = "N * Suc M" in exI)
  apply auto
  apply (metis dvdI dvd_add_times_triv_left_iff dvd_add_triv_right_iff dvd_refl dvd_trans le_Suc_eq mult_Suc_right)
  done

lemma dvd_by_all: "\<forall>M::nat. \<exists>N>0. \<forall>m. 0 < m \<and> m \<le> M \<longrightarrow> m dvd N"
  using dvd_by_all2 by blast

lemma hypnat_of_nat_le_zero_iff [simp]: "hypnat_of_nat n \<le> 0 \<longleftrightarrow> n = 0"
  by transfer simp

text \<open>Goldblatt: Exercise 5.11(2) -- p. 57.\<close>
lemma hdvd_by_all: "\<forall>M. \<exists>N. 0 < N \<and> (\<forall>m::hypnat. 0 < m \<and> m \<le> M \<longrightarrow> m dvd N)"
  by transfer (rule dvd_by_all)

lemmas hdvd_by_all2 = hdvd_by_all [THEN spec]

text \<open>Goldblatt: Exercise 5.11(2) -- p. 57.\<close>
lemma hypnat_dvd_all_hypnat_of_nat:
  "\<exists>N::hypnat. 0 < N \<and> (\<forall>n \<in> - {0::nat}. hypnat_of_nat n dvd N)"
  apply (cut_tac hdvd_by_all)
  apply (drule_tac x = whn in spec)
  apply auto
  apply (rule exI)
  apply auto
  apply (drule_tac x = "hypnat_of_nat n" in spec)
  apply (auto simp add: linorder_not_less)
  done


text \<open>The nonstandard extension of the set prime numbers consists of precisely
  those hypernaturals exceeding 1 that have no nontrivial factors.\<close>

text \<open>Goldblatt: Exercise 5.11(3a) -- p 57.\<close>
lemma starprime: "starprime = {p. 1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> m = 1 \<or> m = p)}"
  by transfer (auto simp add: prime_nat_iff)

text \<open>Goldblatt Exercise 5.11(3b) -- p 57.\<close>
lemma hyperprime_factor_exists: "\<And>n. 1 < n \<Longrightarrow> \<exists>k \<in> starprime. k dvd n"
  by transfer (simp add: prime_factor_nat)

text \<open>Goldblatt Exercise 3.10(1) -- p. 29.\<close>
lemma NatStar_hypnat_of_nat: "finite A \<Longrightarrow> *s* A = hypnat_of_nat ` A"
  by (rule starset_finite)


subsection \<open>Another characterization of infinite set of natural numbers\<close>

lemma finite_nat_set_bounded: "finite N \<Longrightarrow> \<exists>n::nat. \<forall>i \<in> N. i < n"
  apply (erule_tac F = N in finite_induct)
   apply auto
  apply (rule_tac x = "Suc n + x" in exI)
  apply auto
  done

lemma finite_nat_set_bounded_iff: "finite N \<longleftrightarrow> (\<exists>n::nat. \<forall>i \<in> N. i < n)"
  by (blast intro: finite_nat_set_bounded bounded_nat_set_is_finite)

lemma not_finite_nat_set_iff: "\<not> finite N \<longleftrightarrow> (\<forall>n::nat. \<exists>i \<in> N. n \<le> i)"
  by (auto simp add: finite_nat_set_bounded_iff not_less)

lemma bounded_nat_set_is_finite2: "\<forall>i::nat \<in> N. i \<le> n \<Longrightarrow> finite N"
  apply (rule finite_subset)
   apply (rule_tac [2] finite_atMost)
  apply auto
  done

lemma finite_nat_set_bounded2: "finite N \<Longrightarrow> \<exists>n::nat. \<forall>i \<in> N. i \<le> n"
  apply (erule_tac F = N in finite_induct)
   apply auto
  apply (rule_tac x = "n + x" in exI)
  apply auto
  done

lemma finite_nat_set_bounded_iff2: "finite N \<longleftrightarrow> (\<exists>n::nat. \<forall>i \<in> N. i \<le> n)"
  by (blast intro: finite_nat_set_bounded2 bounded_nat_set_is_finite2)

lemma not_finite_nat_set_iff2: "\<not> finite N \<longleftrightarrow> (\<forall>n::nat. \<exists>i \<in> N. n < i)"
  by (auto simp add: finite_nat_set_bounded_iff2 not_le)


subsection \<open>An injective function cannot define an embedded natural number\<close>

lemma lemma_infinite_set_singleton:
  "\<forall>m n. m \<noteq> n \<longrightarrow> f n \<noteq> f m \<Longrightarrow> {n. f n = N} = {} \<or> (\<exists>m. {n. f n = N} = {m})"
  apply auto
  apply (drule_tac x = x in spec, auto)
  apply (subgoal_tac "\<forall>n. f n = f x \<longleftrightarrow> x = n")
   apply auto
  done

lemma inj_fun_not_hypnat_in_SHNat:
  fixes f :: "nat \<Rightarrow> nat"
  assumes inj_f: "inj f"
  shows "starfun f whn \<notin> Nats"
proof
  from inj_f have inj_f': "inj (starfun f)"
    by (transfer inj_on_def Ball_def UNIV_def)
  assume "starfun f whn \<in> Nats"
  then obtain N where N: "starfun f whn = hypnat_of_nat N"
    by (auto simp: Nats_def)
  then have "\<exists>n. starfun f n = hypnat_of_nat N" ..
  then have "\<exists>n. f n = N" by transfer
  then obtain n where "f n = N" ..
  then have "starfun f (hypnat_of_nat n) = hypnat_of_nat N"
    by transfer
  with N have "starfun f whn = starfun f (hypnat_of_nat n)"
    by simp
  with inj_f' have "whn = hypnat_of_nat n"
    by (rule injD)
  then show False
    by (simp add: whn_neq_hypnat_of_nat)
qed

lemma range_subset_mem_starsetNat: "range f \<subseteq> A \<Longrightarrow> starfun f whn \<in> *s* A"
  apply (rule_tac x="whn" in spec)
  apply transfer
  apply auto
  done

text \<open>
  Gleason Proposition 11-5.5. pg 149, pg 155 (ex. 3) and pg. 360.

  Let \<open>E\<close> be a nonvoid ordered set with no maximal elements (note: effectively an
  infinite set if we take \<open>E = N\<close> (Nats)). Then there exists an order-preserving
  injection from \<open>N\<close> to \<open>E\<close>. Of course, (as some doofus will undoubtedly point out!
  :-)) can use notion of least element in proof (i.e. no need for choice) if
  dealing with nats as we have well-ordering property.
\<close>

lemma lemmaPow3: "E \<noteq> {} \<Longrightarrow> \<exists>x. \<exists>X \<in> Pow E - {{}}. x \<in> X"
  by auto

lemma choicefun_mem_set [simp]: "E \<noteq> {} \<Longrightarrow> choicefun E \<in> E"
  apply (unfold choicefun_def)
  apply (rule lemmaPow3 [THEN someI2_ex], auto)
  done

lemma injf_max_mem_set: "E \<noteq>{} \<Longrightarrow> \<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> injf_max n E \<in> E"
  apply (induct n)
   apply force
  apply (simp add: choicefun_def)
  apply (rule lemmaPow3 [THEN someI2_ex], auto)
  done

lemma injf_max_order_preserving: "\<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> injf_max n E < injf_max (Suc n) E"
  apply (simp add: choicefun_def)
  apply (rule lemmaPow3 [THEN someI2_ex])
   apply auto
  done

lemma injf_max_order_preserving2: "\<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> \<forall>n m. m < n \<longrightarrow> injf_max m E < injf_max n E"
  apply (rule allI)
  apply (induct_tac n)
   apply auto
  apply (simp add: choicefun_def)
  apply (rule lemmaPow3 [THEN someI2_ex])
   apply (auto simp add: less_Suc_eq)
  apply (drule_tac x = m in spec)
  apply (drule subsetD)
   apply auto
  done

lemma inj_injf_max: "\<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> inj (\<lambda>n. injf_max n E)"
  apply (rule inj_onI)
  apply (rule ccontr)
  apply auto
  apply (drule injf_max_order_preserving2)
  apply (metis antisym_conv3 order_less_le)
  done

lemma infinite_set_has_order_preserving_inj:
  "E \<noteq> {} \<Longrightarrow> \<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> \<exists>f. range f \<subseteq> E \<and> inj f \<and> (\<forall>m. f m < f (Suc m))"
  for E :: "'a::order set" and f :: "nat \<Rightarrow> 'a"
  apply (rule_tac x = "\<lambda>n. injf_max n E" in exI)
  apply safe
    apply (rule injf_max_mem_set)
     apply (rule_tac [3] inj_injf_max)
     apply (rule_tac [4] injf_max_order_preserving)
     apply auto
  done


text \<open>Only need the existence of an injective function from \<open>N\<close> to \<open>A\<close> for proof.\<close>

lemma hypnat_infinite_has_nonstandard: "\<not> finite A \<Longrightarrow> hypnat_of_nat ` A < ( *s* A)"
  apply auto
  apply (subgoal_tac "A \<noteq> {}")
   prefer 2 apply force
  apply (drule infinite_set_has_order_preserving_inj)
   apply (erule not_finite_nat_set_iff2 [THEN iffD1])
  apply auto
  apply (drule inj_fun_not_hypnat_in_SHNat)
  apply (drule range_subset_mem_starsetNat)
  apply (auto simp add: SHNat_eq)
  done

lemma starsetNat_eq_hypnat_of_nat_image_finite: "*s* A =  hypnat_of_nat ` A \<Longrightarrow> finite A"
  by (metis hypnat_infinite_has_nonstandard less_irrefl)

lemma finite_starsetNat_iff: "*s* A = hypnat_of_nat ` A \<longleftrightarrow> finite A"
  by (blast intro!: starsetNat_eq_hypnat_of_nat_image_finite NatStar_hypnat_of_nat)

lemma hypnat_infinite_has_nonstandard_iff: "\<not> finite A \<longleftrightarrow> hypnat_of_nat ` A < *s* A"
  apply (rule iffI)
   apply (blast intro!: hypnat_infinite_has_nonstandard)
  apply (auto simp add: finite_starsetNat_iff [symmetric])
  done


subsection \<open>Existence of Infinitely Many Primes: a Nonstandard Proof\<close>

lemma lemma_not_dvd_hypnat_one [simp]: "\<not> (\<forall>n \<in> - {0}. hypnat_of_nat n dvd 1)"
  apply auto
  apply (rule_tac x = 2 in bexI)
   apply transfer
   apply auto
  done

lemma lemma_not_dvd_hypnat_one2 [simp]: "\<exists>n \<in> - {0}. \<not> hypnat_of_nat n dvd 1"
  using lemma_not_dvd_hypnat_one by (auto simp del: lemma_not_dvd_hypnat_one)

lemma hypnat_add_one_gt_one: "\<And>N::hypnat. 0 < N \<Longrightarrow> 1 < N + 1"
  by transfer simp

lemma hypnat_of_nat_zero_not_prime [simp]: "hypnat_of_nat 0 \<notin> starprime"
  by transfer simp

lemma hypnat_zero_not_prime [simp]: "0 \<notin> starprime"
  using hypnat_of_nat_zero_not_prime by simp

lemma hypnat_of_nat_one_not_prime [simp]: "hypnat_of_nat 1 \<notin> starprime"
  by transfer simp

lemma hypnat_one_not_prime [simp]: "1 \<notin> starprime"
  using hypnat_of_nat_one_not_prime by simp

lemma hdvd_diff: "\<And>k m n :: hypnat. k dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd (m - n)"
  by transfer (rule dvd_diff_nat)

lemma hdvd_one_eq_one: "\<And>x::hypnat. is_unit x \<Longrightarrow> x = 1"
  by transfer simp

text \<open>Already proved as \<open>primes_infinite\<close>, but now using non-standard naturals.\<close>
theorem not_finite_prime: "\<not> finite {p::nat. prime p}"
  apply (rule hypnat_infinite_has_nonstandard_iff [THEN iffD2])
  using hypnat_dvd_all_hypnat_of_nat
  apply clarify
  apply (drule hypnat_add_one_gt_one)
  apply (drule hyperprime_factor_exists)
  apply clarify
  apply (subgoal_tac "k \<notin> hypnat_of_nat ` {p. prime p}")
   apply (force simp: starprime_def)
  apply (metis Compl_iff add.commute dvd_add_left_iff empty_iff hdvd_one_eq_one hypnat_one_not_prime
      imageE insert_iff mem_Collect_eq not_prime_0)
  done

end
