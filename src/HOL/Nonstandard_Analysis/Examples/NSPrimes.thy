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
proof (induct M)
  case 0
  then show ?case 
    by auto
next
  case (Suc M)
  then obtain N where "N>0" and "\<And>m. 0 < m \<and> m \<le> M \<Longrightarrow> m dvd N"
    by metis
  then show ?case
    by (metis nat_0_less_mult_iff zero_less_Suc dvd_mult dvd_mult2 dvd_refl le_Suc_eq)
qed

lemma dvd_by_all: "\<forall>M::nat. \<exists>N>0. \<forall>m. 0 < m \<and> m \<le> M \<longrightarrow> m dvd N"
  using dvd_by_all2 by blast

lemma hypnat_of_nat_le_zero_iff [simp]: "hypnat_of_nat n \<le> 0 \<longleftrightarrow> n = 0"
  by transfer simp

text \<open>Goldblatt: Exercise 5.11(2) -- p. 57.\<close>
lemma hdvd_by_all [rule_format]: "\<forall>M. \<exists>N. 0 < N \<and> (\<forall>m::hypnat. 0 < m \<and> m \<le> M \<longrightarrow> m dvd N)"
  by transfer (rule dvd_by_all)

text \<open>Goldblatt: Exercise 5.11(2) -- p. 57.\<close>
lemma hypnat_dvd_all_hypnat_of_nat:
  "\<exists>N::hypnat. 0 < N \<and> (\<forall>n \<in> - {0::nat}. hypnat_of_nat n dvd N)"
  by (metis Compl_iff gr0I hdvd_by_all hypnat_of_nat_le_whn singletonI star_of_0_less)


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



subsection \<open>An injective function cannot define an embedded natural number\<close>

lemma lemma_infinite_set_singleton:
  "\<forall>m n. m \<noteq> n \<longrightarrow> f n \<noteq> f m \<Longrightarrow> {n. f n = N} = {} \<or> (\<exists>m. {n. f n = N} = {m})"
  by (metis (mono_tags) is_singletonI' is_singleton_the_elem mem_Collect_eq)

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
  by (metis STAR_subset_closed UNIV_I image_eqI starset_UNIV starset_image)

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
  unfolding choicefun_def
  by (force intro: lemmaPow3 [THEN someI2_ex])

lemma injf_max_mem_set: "E \<noteq>{} \<Longrightarrow> \<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> injf_max n E \<in> E"
proof (induct n)
  case 0
  then show ?case by force
next
  case (Suc n)
  then show ?case
    apply (simp add: choicefun_def)
    apply (rule lemmaPow3 [THEN someI2_ex], auto)
    done
qed

lemma injf_max_order_preserving: "\<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> injf_max n E < injf_max (Suc n) E"
  by (metis (no_types, lifting) choicefun_mem_set empty_iff injf_max.simps(2) mem_Collect_eq)

lemma injf_max_order_preserving2: 
  assumes "m < n" and E: "\<forall>x. \<exists>y \<in> E. x < y"
  shows  "injf_max m E < injf_max n E"
  using \<open>m < n\<close>
proof (induction n arbitrary: m)
  case 0 then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (metis E injf_max_order_preserving less_Suc_eq order_less_trans)
qed


lemma inj_injf_max: "\<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> inj (\<lambda>n. injf_max n E)"
  by (metis injf_max_order_preserving2 linorder_injI order_less_irrefl)

lemma infinite_set_has_order_preserving_inj:
  "E \<noteq> {} \<Longrightarrow> \<forall>x. \<exists>y \<in> E. x < y \<Longrightarrow> \<exists>f. range f \<subseteq> E \<and> inj f \<and> (\<forall>m. f m < f (Suc m))"
  for E :: "'a::order set" and f :: "nat \<Rightarrow> 'a"
  by (metis image_subsetI inj_injf_max injf_max_mem_set injf_max_order_preserving)


text \<open>Only need the existence of an injective function from \<open>N\<close> to \<open>A\<close> for proof.\<close>

lemma hypnat_infinite_has_nonstandard:
  assumes "infinite A"
  shows "hypnat_of_nat ` A < ( *s* A)"
  by (metis assms IntE NatStar_hypreal_of_real_Int STAR_star_of_image_subset psubsetI
      infinite_iff_countable_subset inj_fun_not_hypnat_in_SHNat range_subset_mem_starsetNat)

lemma starsetNat_eq_hypnat_of_nat_image_finite: "*s* A =  hypnat_of_nat ` A \<Longrightarrow> finite A"
  by (metis hypnat_infinite_has_nonstandard less_irrefl)

lemma finite_starsetNat_iff: "*s* A = hypnat_of_nat ` A \<longleftrightarrow> finite A"
  by (blast intro!: starsetNat_eq_hypnat_of_nat_image_finite NatStar_hypnat_of_nat)

lemma hypnat_infinite_has_nonstandard_iff: "infinite A \<longleftrightarrow> hypnat_of_nat ` A < *s* A"
  by (metis finite_starsetNat_iff hypnat_infinite_has_nonstandard nless_le)


subsection \<open>Existence of Infinitely Many Primes: a Nonstandard Proof\<close>

lemma lemma_not_dvd_hypnat_one [simp]: "\<exists>n \<in> - {0}. \<not> hypnat_of_nat n dvd 1"
proof -
  have "\<not> hypnat_of_nat 2 dvd 1"
    by transfer auto
  then show ?thesis
    by (metis ComplI singletonD zero_neq_numeral)
qed

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
theorem not_finite_prime: "infinite {p::nat. prime p}"
proof -
  obtain N k where N: "\<forall>n\<in>- {0}. hypnat_of_nat n dvd N" "k\<in>starprime" "k dvd N + 1"
    by (meson hyperprime_factor_exists hypnat_add_one_gt_one hypnat_dvd_all_hypnat_of_nat)
  then have "k \<noteq> 1"
    using \<open>k \<in> starprime\<close> by force
  then have "k \<notin> hypnat_of_nat ` {p. prime p}"
    using N dvd_add_right_iff hdvd_one_eq_one not_prime_0 by blast
  then show ?thesis
    by (metis \<open>k \<in> starprime\<close> finite_starsetNat_iff starprime_def)
qed

end
