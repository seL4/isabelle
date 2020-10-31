(*  Title:      HOL/Analysis/Arcwise_Connected.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>Arcwise-Connected Sets\<close>

theory Arcwise_Connected
imports Path_Connected Ordered_Euclidean_Space "HOL-Computational_Algebra.Primes"
begin

lemma path_connected_interval [simp]:
  fixes a b::"'a::ordered_euclidean_space"
  shows "path_connected {a..b}"
  using is_interval_cc is_interval_path_connected by blast

lemma segment_to_closest_point:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>closed S; S \<noteq> {}\<rbrakk> \<Longrightarrow> open_segment a (closest_point S a) \<inter> S = {}"
  unfolding disjoint_iff
  by (metis closest_point_le dist_commute dist_in_open_segment not_le)

lemma segment_to_point_exists:
  fixes S :: "'a :: euclidean_space set"
    assumes "closed S" "S \<noteq> {}"
    obtains b where "b \<in> S" "open_segment a b \<inter> S = {}"
  by (metis assms segment_to_closest_point closest_point_exists that)


subsection \<open>The Brouwer reduction theorem\<close>

theorem Brouwer_reduction_theorem_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "closed S" "\<phi> S"
      and \<phi>: "\<And>F. \<lbrakk>\<And>n. closed(F n); \<And>n. \<phi>(F n); \<And>n. F(Suc n) \<subseteq> F n\<rbrakk> \<Longrightarrow> \<phi>(\<Inter>(range F))"
  obtains T where "T \<subseteq> S" "closed T" "\<phi> T" "\<And>U. \<lbrakk>U \<subseteq> S; closed U; \<phi> U\<rbrakk> \<Longrightarrow> \<not> (U \<subset> T)"
proof -
  obtain B :: "nat \<Rightarrow> 'a set"
    where "inj B" "\<And>n. open(B n)" and open_cov: "\<And>S. open S \<Longrightarrow> \<exists>K. S = \<Union>(B ` K)"
      by (metis Setcompr_eq_image that univ_second_countable_sequence)
  define A where "A \<equiv> rec_nat S (\<lambda>n a. if \<exists>U. U \<subseteq> a \<and> closed U \<and> \<phi> U \<and> U \<inter> (B n) = {}
                                        then SOME U. U \<subseteq> a \<and> closed U \<and> \<phi> U \<and> U \<inter> (B n) = {}
                                        else a)"
  have [simp]: "A 0 = S"
    by (simp add: A_def)
  have ASuc: "A(Suc n) = (if \<exists>U. U \<subseteq> A n \<and> closed U \<and> \<phi> U \<and> U \<inter> (B n) = {}
                          then SOME U. U \<subseteq> A n \<and> closed U \<and> \<phi> U \<and> U \<inter> (B n) = {}
                          else A n)" for n
    by (auto simp: A_def)
  have sub: "\<And>n. A(Suc n) \<subseteq> A n"
    by (auto simp: ASuc dest!: someI_ex)
  have subS: "A n \<subseteq> S" for n
    by (induction n) (use sub in auto)
  have clo: "closed (A n) \<and> \<phi> (A n)" for n
    by (induction n) (auto simp: assms ASuc dest!: someI_ex)
  show ?thesis
  proof
    show "\<Inter>(range A) \<subseteq> S"
      using \<open>\<And>n. A n \<subseteq> S\<close> by blast
    show "closed (\<Inter>(A ` UNIV))"
      using clo by blast
    show "\<phi> (\<Inter>(A ` UNIV))"
      by (simp add: clo \<phi> sub)
    show "\<not> U \<subset> \<Inter>(A ` UNIV)" if "U \<subseteq> S" "closed U" "\<phi> U" for U
    proof -
      have "\<exists>y. x \<notin> A y" if "x \<notin> U" and Usub: "U \<subseteq> (\<Inter>x. A x)" for x
      proof -
        obtain e where "e > 0" and e: "ball x e \<subseteq> -U"
          using \<open>closed U\<close> \<open>x \<notin> U\<close> openE [of "-U"] by blast
        moreover obtain K where K: "ball x e = \<Union>(B ` K)"
          using open_cov [of "ball x e"] by auto
        ultimately have "\<Union>(B ` K) \<subseteq> -U"
          by blast
        have "K \<noteq> {}"
          using \<open>0 < e\<close> \<open>ball x e = \<Union>(B ` K)\<close> by auto
        then obtain n where "n \<in> K" "x \<in> B n"
          by (metis K UN_E \<open>0 < e\<close> centre_in_ball)
        then have "U \<inter> B n = {}"
          using K e by auto
        show ?thesis
        proof (cases "\<exists>U\<subseteq>A n. closed U \<and> \<phi> U \<and> U \<inter> B n = {}")
          case True
          then show ?thesis
            apply (rule_tac x="Suc n" in exI)
            apply (simp add: ASuc)
            apply (erule someI2_ex)
            using \<open>x \<in> B n\<close> by blast
        next
          case False
          then show ?thesis
            by (meson Inf_lower Usub \<open>U \<inter> B n = {}\<close> \<open>\<phi> U\<close> \<open>closed U\<close> range_eqI subset_trans)
        qed
      qed
      with that show ?thesis
        by (meson Inter_iff psubsetE rangeI subsetI)
    qed
  qed
qed

corollary Brouwer_reduction_theorem:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "\<phi> S" "S \<noteq> {}"
      and \<phi>: "\<And>F. \<lbrakk>\<And>n. compact(F n); \<And>n. F n \<noteq> {}; \<And>n. \<phi>(F n); \<And>n. F(Suc n) \<subseteq> F n\<rbrakk> \<Longrightarrow> \<phi>(\<Inter>(range F))"
  obtains T where "T \<subseteq> S" "compact T" "T \<noteq> {}" "\<phi> T"
                  "\<And>U. \<lbrakk>U \<subseteq> S; closed U; U \<noteq> {}; \<phi> U\<rbrakk> \<Longrightarrow> \<not> (U \<subset> T)"
proof (rule Brouwer_reduction_theorem_gen [of S "\<lambda>T. T \<noteq> {} \<and> T \<subseteq> S \<and> \<phi> T"])
  fix F
  assume cloF: "\<And>n. closed (F n)"
     and F: "\<And>n. F n \<noteq> {} \<and> F n \<subseteq> S \<and> \<phi> (F n)" and Fsub: "\<And>n. F (Suc n) \<subseteq> F n"
  show "\<Inter>(F ` UNIV) \<noteq> {} \<and> \<Inter>(F ` UNIV) \<subseteq> S \<and> \<phi> (\<Inter>(F ` UNIV))"
  proof (intro conjI)
    show "\<Inter>(F ` UNIV) \<noteq> {}"
      by (metis F Fsub \<open>compact S\<close> cloF closed_Int_compact compact_nest inf.orderE lift_Suc_antimono_le)
    show " \<Inter>(F ` UNIV) \<subseteq> S"
      using F by blast
    show "\<phi> (\<Inter>(F ` UNIV))"
      by (metis F Fsub \<phi> \<open>compact S\<close> cloF closed_Int_compact inf.orderE)
  qed
next
  show "S \<noteq> {} \<and> S \<subseteq> S \<and> \<phi> S"
    by (simp add: assms)
qed (meson assms compact_imp_closed seq_compact_closed_subset seq_compact_eq_compact)+


subsection\<^marker>\<open>tag unimportant\<close>\<open>Arcwise Connections\<close>(*FIX ME this subsection is empty(?) *)

subsection\<open>Density of points with dyadic rational coordinates\<close>

proposition closure_dyadic_rationals:
    "closure (\<Union>k. \<Union>f \<in> Basis \<rightarrow> \<int>.
                   { \<Sum>i :: 'a :: euclidean_space \<in> Basis. (f i / 2^k) *\<^sub>R i }) = UNIV"
proof -
  have "x \<in> closure (\<Union>k. \<Union>f \<in> Basis \<rightarrow> \<int>. {\<Sum>i \<in> Basis. (f i / 2^k) *\<^sub>R i})" for x::'a
  proof (clarsimp simp: closure_approachable)
    fix e::real
    assume "e > 0"
    then obtain k where k: "(1/2)^k < e/DIM('a)"
      by (meson DIM_positive divide_less_eq_1_pos of_nat_0_less_iff one_less_numeral_iff real_arch_pow_inv semiring_norm(76) zero_less_divide_iff zero_less_numeral)
    have "dist (\<Sum>i\<in>Basis. (real_of_int \<lfloor>2^k*(x \<bullet> i)\<rfloor> / 2^k) *\<^sub>R i) x =
          dist (\<Sum>i\<in>Basis. (real_of_int \<lfloor>2^k*(x \<bullet> i)\<rfloor> / 2^k) *\<^sub>R i) (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i)"
      by (simp add: euclidean_representation)
    also have "... = norm ((\<Sum>i\<in>Basis. (real_of_int \<lfloor>2^k*(x \<bullet> i)\<rfloor> / 2^k) *\<^sub>R i - (x \<bullet> i) *\<^sub>R i))"
      by (simp add: dist_norm sum_subtractf)
    also have "... \<le> DIM('a)*((1/2)^k)"
    proof (rule sum_norm_bound, simp add: algebra_simps)
      fix i::'a
      assume "i \<in> Basis"
      then have "norm ((real_of_int \<lfloor>x \<bullet> i*2^k\<rfloor> / 2^k) *\<^sub>R i - (x \<bullet> i) *\<^sub>R i) =
                 \<bar>real_of_int \<lfloor>x \<bullet> i*2^k\<rfloor> / 2^k - x \<bullet> i\<bar>"
        by (simp add: scaleR_left_diff_distrib [symmetric])
      also have "... \<le> (1/2) ^ k"
        by (simp add: divide_simps) linarith
      finally show "norm ((real_of_int \<lfloor>x \<bullet> i*2^k\<rfloor> / 2^k) *\<^sub>R i - (x \<bullet> i) *\<^sub>R i) \<le> (1/2) ^ k" .
    qed
    also have "... < DIM('a)*(e/DIM('a))"
      using DIM_positive k linordered_comm_semiring_strict_class.comm_mult_strict_left_mono of_nat_0_less_iff by blast
    also have "... = e"
      by simp
    finally have "dist (\<Sum>i\<in>Basis. (\<lfloor>2^k*(x \<bullet> i)\<rfloor> / 2^k) *\<^sub>R i) x < e" .
    with Ints_of_int
    show "\<exists>k. \<exists>f \<in> Basis \<rightarrow> \<int>. dist (\<Sum>b\<in>Basis. (f b / 2^k) *\<^sub>R b) x < e"
      by fastforce
  qed
  then show ?thesis by auto
qed

corollary closure_rational_coordinates:
    "closure (\<Union>f \<in> Basis \<rightarrow> \<rat>. { \<Sum>i :: 'a :: euclidean_space \<in> Basis. f i *\<^sub>R i }) = UNIV"
proof -
  have *: "(\<Union>k. \<Union>f \<in> Basis \<rightarrow> \<int>. { \<Sum>i::'a \<in> Basis. (f i / 2^k) *\<^sub>R i })
           \<subseteq> (\<Union>f \<in> Basis \<rightarrow> \<rat>. { \<Sum>i \<in> Basis. f i *\<^sub>R i })"
  proof clarsimp
    fix k and f :: "'a \<Rightarrow> real"
    assume f: "f \<in> Basis \<rightarrow> \<int>"
    show "\<exists>x \<in> Basis \<rightarrow> \<rat>. (\<Sum>i \<in> Basis. (f i / 2^k) *\<^sub>R i) = (\<Sum>i \<in> Basis. x i *\<^sub>R i)"
      apply (rule_tac x="\<lambda>i. f i / 2^k" in bexI)
      using Ints_subset_Rats f by auto
  qed
  show ?thesis
    using closure_dyadic_rationals closure_mono [OF *] by blast
qed

lemma closure_dyadic_rationals_in_convex_set:
   "\<lbrakk>convex S; interior S \<noteq> {}\<rbrakk>
        \<Longrightarrow> closure(S \<inter>
                    (\<Union>k. \<Union>f \<in> Basis \<rightarrow> \<int>.
                   { \<Sum>i :: 'a :: euclidean_space \<in> Basis. (f i / 2^k) *\<^sub>R i })) =
            closure S"
  by (simp add: closure_dyadic_rationals closure_convex_Int_superset)

lemma closure_rationals_in_convex_set:
   "\<lbrakk>convex S; interior S \<noteq> {}\<rbrakk>
    \<Longrightarrow> closure(S \<inter> (\<Union>f \<in> Basis \<rightarrow> \<rat>. { \<Sum>i :: 'a :: euclidean_space \<in> Basis. f i *\<^sub>R i })) =
        closure S"
  by (simp add: closure_rational_coordinates closure_convex_Int_superset)


text\<open> Every path between distinct points contains an arc, and hence
path connection is equivalent to arcwise connection for distinct points.
The proof is based on Whyburn's "Topological Analysis".\<close>

lemma closure_dyadic_rationals_in_convex_set_pos_1:
  fixes S :: "real set"
  assumes "convex S" and intnz: "interior S \<noteq> {}" and pos: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> x"
    shows "closure(S \<inter> (\<Union>k m. {of_nat m / 2^k})) = closure S"
proof -
  have "\<exists>m. f 1/2^k = real m / 2^k" if "(f 1) / 2^k \<in> S" "f 1 \<in> \<int>" for k and f :: "real \<Rightarrow> real"
    using that by (force simp: Ints_def zero_le_divide_iff power_le_zero_eq dest: pos zero_le_imp_eq_int)
  then have "S \<inter> (\<Union>k m. {real m / 2^k}) = S \<inter>
             (\<Union>k. \<Union>f\<in>Basis \<rightarrow> \<int>. {\<Sum>i\<in>Basis. (f i / 2^k) *\<^sub>R i})"
    by force
  then show ?thesis
    using closure_dyadic_rationals_in_convex_set [OF \<open>convex S\<close> intnz] by simp
qed


definition\<^marker>\<open>tag unimportant\<close> dyadics :: "'a::field_char_0 set" where "dyadics \<equiv> \<Union>k m. {of_nat m / 2^k}"

lemma real_in_dyadics [simp]: "real m \<in> dyadics"
  by (simp add: dyadics_def) (metis divide_numeral_1 numeral_One power_0)

lemma nat_neq_4k1: "of_nat m \<noteq> (4 * of_nat k + 1) / (2 * 2^n :: 'a::field_char_0)"
proof
  assume "of_nat m = (4 * of_nat k + 1) / (2 * 2^n :: 'a)"
  then have "of_nat (m * (2 * 2^n)) = (of_nat (Suc (4 * k)) :: 'a)"
    by (simp add: field_split_simps)
  then have "m * (2 * 2^n) = Suc (4 * k)"
    using of_nat_eq_iff by blast
  then have "odd (m * (2 * 2^n))"
    by simp
  then show False
    by simp
qed

lemma nat_neq_4k3: "of_nat m \<noteq> (4 * of_nat k + 3) / (2 * 2^n :: 'a::field_char_0)"
proof
  assume "of_nat m = (4 * of_nat k + 3) / (2 * 2^n :: 'a)"
  then have "of_nat (m * (2 * 2^n)) = (of_nat (4 * k + 3) :: 'a)"
    by (simp add: field_split_simps)
  then have "m * (2 * 2^n) = (4 * k) + 3"
    using of_nat_eq_iff by blast
  then have "odd (m * (2 * 2^n))"
    by simp
  then show False
    by simp
qed

lemma iff_4k:
  assumes "r = real k" "odd k"
    shows "(4 * real m + r) / (2 * 2^n) = (4 * real m' + r) / (2 * 2 ^ n') \<longleftrightarrow> m=m' \<and> n=n'"
proof -
  { assume "(4 * real m + r) / (2 * 2^n) = (4 * real m' + r) / (2 * 2 ^ n')"
    then have "real ((4 * m + k) * (2 * 2 ^ n')) = real ((4 * m' + k) * (2 * 2^n))"
      using assms by (auto simp: field_simps)
    then have "(4 * m + k) * (2 * 2 ^ n') = (4 * m' + k) * (2 * 2^n)"
      using of_nat_eq_iff by blast
    then have "(4 * m + k) * (2 ^ n') = (4 * m' + k) * (2^n)"
      by linarith
    then obtain "4*m + k = 4*m' + k" "n=n'"
      using prime_power_cancel2 [OF two_is_prime_nat] assms
      by (metis even_mult_iff even_numeral odd_add)
    then have "m=m'" "n=n'"
      by auto
  }
  then show ?thesis by blast
qed

lemma neq_4k1_k43: "(4 * real m + 1) / (2 * 2^n) \<noteq> (4 * real m' + 3) / (2 * 2 ^ n')"
proof
  assume "(4 * real m + 1) / (2 * 2^n) = (4 * real m' + 3) / (2 * 2 ^ n')"
  then have "real (Suc (4 * m) * (2 * 2 ^ n')) = real ((4 * m' + 3) * (2 * 2^n))"
    by (auto simp: field_simps)
  then have "Suc (4 * m) * (2 * 2 ^ n') = (4 * m' + 3) * (2 * 2^n)"
    using of_nat_eq_iff by blast
  then have "Suc (4 * m) * (2 ^ n') = (4 * m' + 3) * (2^n)"
    by linarith
  then have "Suc (4 * m) = (4 * m' + 3)"
    by (rule prime_power_cancel2 [OF two_is_prime_nat]) auto
  then have "1 + 2 * m' = 2 * m"
    using \<open>Suc (4 * m) = 4 * m' + 3\<close> by linarith
  then show False
    using even_Suc by presburger
qed

lemma dyadic_413_cases:
  obtains "(of_nat m::'a::field_char_0) / 2^k \<in> Nats"
  | m' k' where "k' < k" "(of_nat m:: 'a) / 2^k = of_nat (4*m' + 1) / 2^Suc k'"
  | m' k' where "k' < k" "(of_nat m:: 'a) / 2^k = of_nat (4*m' + 3) / 2^Suc k'"
proof (cases "m>0")
  case False
  then have "m=0" by simp
  with that show ?thesis by auto
next
  case True
  obtain k' m' where m': "odd m'" and k': "m = m' * 2^k'"
    using prime_power_canonical [OF two_is_prime_nat True] by blast
  then obtain q r where q: "m' = 4*q + r" and r: "r < 4"
    by (metis not_add_less2 split_div zero_neq_numeral)
  show ?thesis
  proof (cases "k \<le> k'")
    case True
    have "(of_nat m:: 'a) / 2^k = of_nat m' * (2 ^ k' / 2^k)"
      using k' by (simp add: field_simps)
    also have "... = (of_nat m'::'a) * 2 ^ (k'-k)"
      using k' True by (simp add: power_diff)
    also have "... \<in> \<nat>"
      by (metis Nats_mult of_nat_in_Nats of_nat_numeral of_nat_power)
    finally show ?thesis by (auto simp: that)
  next
    case False
    then obtain kd where kd: "Suc kd = k - k'"
      using Suc_diff_Suc not_less by blast
    have "(of_nat m:: 'a) / 2^k = of_nat m' * (2 ^ k' / 2^k)"
      using k' by (simp add: field_simps)
    also have "... = (of_nat m'::'a) / 2 ^ (k-k')"
      using k' False by (simp add: power_diff)
    also have "... = ((of_nat r + 4 * of_nat q)::'a) / 2 ^ (k-k')"
      using q by force
    finally have meq: "(of_nat m:: 'a) / 2^k = (of_nat r + 4 * of_nat q) / 2 ^ (k - k')" .
    have "r \<noteq> 0" "r \<noteq> 2"
      using q m' by presburger+
    with r consider "r = 1" | "r = 3"
      by linarith
    then show ?thesis
    proof cases
      assume "r = 1"
      with meq kd that(2) [of kd q] show ?thesis
        by simp
    next
      assume "r = 3"
      with meq kd that(3) [of kd q]  show ?thesis
        by simp
    qed
  qed
qed


lemma dyadics_iff:
   "(dyadics :: 'a::field_char_0 set) =
    Nats \<union> (\<Union>k m. {of_nat (4*m + 1) / 2^Suc k}) \<union> (\<Union>k m. {of_nat (4*m + 3) / 2^Suc k})"
           (is "_ = ?rhs")
proof
  show "dyadics \<subseteq> ?rhs"
    unfolding dyadics_def
    apply clarify
    apply (rule dyadic_413_cases, force+)
    done
next
  have "range of_nat \<subseteq> (\<Union>k m. {(of_nat m::'a) / 2 ^ k})"
    by clarsimp (metis divide_numeral_1 numeral_One power_0)
  moreover have "\<And>k m. \<exists>k' m'. ((1::'a) + 4 * of_nat m) / 2 ^ Suc k = of_nat m' / 2 ^ k'"
    by (metis (no_types) of_nat_Suc of_nat_mult of_nat_numeral)
  moreover have "\<And>k m. \<exists>k' m'. (4 * of_nat m + (3::'a)) / 2 ^ Suc k = of_nat m' / 2 ^ k'"
    by (metis of_nat_add of_nat_mult of_nat_numeral)
  ultimately show "?rhs \<subseteq> dyadics"
    by (auto simp: dyadics_def Nats_def)
qed


function\<^marker>\<open>tag unimportant\<close> (domintros) dyad_rec :: "[nat \<Rightarrow> 'a, 'a\<Rightarrow>'a, 'a\<Rightarrow>'a, real] \<Rightarrow> 'a" where
    "dyad_rec b l r (real m) = b m"
  | "dyad_rec b l r ((4 * real m + 1) / 2 ^ (Suc n)) = l (dyad_rec b l r ((2*m + 1) / 2^n))"
  | "dyad_rec b l r ((4 * real m + 3) / 2 ^ (Suc n)) = r (dyad_rec b l r ((2*m + 1) / 2^n))"
  | "x \<notin> dyadics \<Longrightarrow> dyad_rec b l r x = undefined"
  using iff_4k [of _ 1] iff_4k [of _ 3]
         apply (simp_all add: nat_neq_4k1 nat_neq_4k3 neq_4k1_k43 dyadics_iff Nats_def)
  by (fastforce simp:  field_simps)+

lemma dyadics_levels: "dyadics = (\<Union>K. \<Union>k<K. \<Union> m. {of_nat m / 2^k})"
  unfolding dyadics_def by auto

lemma dyad_rec_level_termination:
  assumes "k < K"
  shows "dyad_rec_dom(b, l, r, real m / 2^k)"
  using assms
proof (induction K arbitrary: k m)
  case 0
  then show ?case by auto
next
  case (Suc K)
  then consider "k = K" | "k < K"
    using less_antisym by blast
  then show ?case
  proof cases
    assume "k = K"
    show ?case
    proof (rule dyadic_413_cases [of m k, where 'a=real])
      show "real m / 2^k \<in> \<nat> \<Longrightarrow> dyad_rec_dom (b, l, r, real m / 2^k)"
        by (force simp: Nats_def nat_neq_4k1 nat_neq_4k3 intro: dyad_rec.domintros)
      show ?case if "k' < k" and eq: "real m / 2^k = real (4 * m' + 1) / 2^Suc k'" for m' k'
      proof -
        have "dyad_rec_dom (b, l, r, (4 * real m' + 1) / 2^Suc k')"
        proof (rule dyad_rec.domintros)
          fix m n
          assume "(4 * real m' + 1) / (2 * 2 ^ k') = (4 * real m + 1) / (2 * 2^n)"
          then have "m' = m" "k' = n" using iff_4k [of _ 1]
            by auto
          have "dyad_rec_dom (b, l, r, real (2 * m + 1) / 2 ^ k')"
            using Suc.IH \<open>k = K\<close> \<open>k' < k\<close> by blast
          then show "dyad_rec_dom (b, l, r, (2 * real m + 1) / 2^n)"
            using \<open>k' = n\<close> by (auto simp: algebra_simps)
        next
          fix m n
          assume "(4 * real m' + 1) / (2 * 2 ^ k') = (4 * real m + 3) / (2 * 2^n)"
          then have "False"
            by (metis neq_4k1_k43)
          then show "dyad_rec_dom (b, l, r, (2 * real m + 1) / 2^n)" ..
        qed
        then show ?case by (simp add: eq add_ac)
      qed
      show ?case if "k' < k" and eq: "real m / 2^k = real (4 * m' + 3) / 2^Suc k'" for m' k'
      proof -
        have "dyad_rec_dom (b, l, r, (4 * real m' + 3) / 2^Suc k')"
        proof (rule dyad_rec.domintros)
          fix m n
          assume "(4 * real m' + 3) / (2 * 2 ^ k') = (4 * real m + 1) / (2 * 2^n)"
          then have "False"
            by (metis neq_4k1_k43)
          then show "dyad_rec_dom (b, l, r, (2 * real m + 1) / 2^n)" ..
        next
          fix m n
          assume "(4 * real m' + 3) / (2 * 2 ^ k') = (4 * real m + 3) / (2 * 2^n)"
          then have "m' = m" "k' = n" using iff_4k [of _ 3]
            by auto
          have "dyad_rec_dom (b, l, r, real (2 * m + 1) / 2 ^ k')"
            using Suc.IH \<open>k = K\<close> \<open>k' < k\<close> by blast
          then show "dyad_rec_dom (b, l, r, (2 * real m + 1) / 2^n)"
            using \<open>k' = n\<close> by (auto simp: algebra_simps)
        qed
        then show ?case by (simp add: eq add_ac)
      qed
    qed
  next
    assume "k < K"
    then show ?case
      using Suc.IH by blast
  qed
qed


lemma dyad_rec_termination: "x \<in> dyadics \<Longrightarrow> dyad_rec_dom(b,l,r,x)"
  by (auto simp: dyadics_levels intro: dyad_rec_level_termination)

lemma dyad_rec_of_nat [simp]: "dyad_rec b l r (real m) = b m"
  by (simp add: dyad_rec.psimps dyad_rec_termination)

lemma dyad_rec_41 [simp]: "dyad_rec b l r ((4 * real m + 1) / 2 ^ (Suc n)) = l (dyad_rec b l r ((2*m + 1) / 2^n))"
proof (rule dyad_rec.psimps)
  show "dyad_rec_dom (b, l, r, (4 * real m + 1) / 2 ^ Suc n)"
    by (metis add.commute dyad_rec_level_termination lessI of_nat_Suc of_nat_mult of_nat_numeral)
qed

lemma dyad_rec_43 [simp]: "dyad_rec b l r ((4 * real m + 3) / 2 ^ (Suc n)) = r (dyad_rec b l r ((2*m + 1) / 2^n))"
proof (rule dyad_rec.psimps)
  show "dyad_rec_dom (b, l, r, (4 * real m + 3) / 2 ^ Suc n)"
    by (metis dyad_rec_level_termination lessI of_nat_add of_nat_mult of_nat_numeral)
qed

lemma dyad_rec_41_times2:
  assumes "n > 0"
    shows "dyad_rec b l r (2 * ((4 * real m + 1) / 2^Suc n)) = l (dyad_rec b l r (2 * (2 * real m + 1) / 2^n))"
proof -
  obtain n' where n': "n = Suc n'"
    using assms not0_implies_Suc by blast
  have "dyad_rec b l r (2 * ((4 * real m + 1) / 2^Suc n)) = dyad_rec b l r ((2 * (4 * real m + 1)) / (2 * 2^n))"
    by auto
  also have "... = dyad_rec b l r ((4 * real m + 1) / 2^n)"
    by (subst mult_divide_mult_cancel_left) auto
  also have "... = l (dyad_rec b l r ((2 * real m + 1) / 2 ^ n'))"
    by (simp add: add.commute [of 1] n' del: power_Suc)
  also have "... = l (dyad_rec b l r ((2 * (2 * real m + 1)) / (2 * 2 ^ n')))"
    by (subst mult_divide_mult_cancel_left) auto
  also have "... = l (dyad_rec b l r (2 * (2 * real m + 1) / 2^n))"
    by (simp add: add.commute n')
  finally show ?thesis .
qed

lemma dyad_rec_43_times2:
  assumes "n > 0"
    shows "dyad_rec b l r (2 * ((4 * real m + 3) / 2^Suc n)) = r (dyad_rec b l r (2 * (2 * real m + 1) / 2^n))"
proof -
  obtain n' where n': "n = Suc n'"
    using assms not0_implies_Suc by blast
  have "dyad_rec b l r (2 * ((4 * real m + 3) / 2^Suc n)) = dyad_rec b l r ((2 * (4 * real m + 3)) / (2 * 2^n))"
    by auto
  also have "... = dyad_rec b l r ((4 * real m + 3) / 2^n)"
    by (subst mult_divide_mult_cancel_left) auto
  also have "... = r (dyad_rec b l r ((2 * real m + 1) / 2 ^ n'))"
    by (simp add: n' del: power_Suc)
  also have "... = r (dyad_rec b l r ((2 * (2 * real m + 1)) / (2 * 2 ^ n')))"
    by (subst mult_divide_mult_cancel_left) auto
  also have "... = r (dyad_rec b l r (2 * (2 * real m + 1) / 2^n))"
    by (simp add: n')
  finally show ?thesis .
qed

definition\<^marker>\<open>tag unimportant\<close> dyad_rec2
    where "dyad_rec2 u v lc rc x =
             dyad_rec (\<lambda>z. (u,v)) (\<lambda>(a,b). (a, lc a b (midpoint a b))) (\<lambda>(a,b). (rc a b (midpoint a b), b)) (2*x)"

abbreviation\<^marker>\<open>tag unimportant\<close> leftrec where "leftrec u v lc rc x \<equiv> fst (dyad_rec2 u v lc rc x)"
abbreviation\<^marker>\<open>tag unimportant\<close> rightrec where "rightrec u v lc rc x \<equiv> snd (dyad_rec2 u v lc rc x)"

lemma leftrec_base: "leftrec u v lc rc (real m / 2) = u"
  by (simp add: dyad_rec2_def)

lemma leftrec_41: "n > 0 \<Longrightarrow> leftrec u v lc rc ((4 * real m + 1) / 2 ^ (Suc n)) = leftrec u v lc rc ((2 * real m + 1) / 2^n)"
  unfolding dyad_rec2_def dyad_rec_41_times2
  by (simp add: case_prod_beta)

lemma leftrec_43: "n > 0 \<Longrightarrow>
             leftrec u v lc rc ((4 * real m + 3) / 2 ^ (Suc n)) =
                 rc (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n))
                 (midpoint (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n)))"
  unfolding dyad_rec2_def dyad_rec_43_times2
  by (simp add: case_prod_beta)

lemma rightrec_base: "rightrec u v lc rc (real m / 2) = v"
  by (simp add: dyad_rec2_def)

lemma rightrec_41: "n > 0 \<Longrightarrow>
             rightrec u v lc rc ((4 * real m + 1) / 2 ^ (Suc n)) =
                 lc (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n))
                 (midpoint (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n)))"
  unfolding dyad_rec2_def dyad_rec_41_times2
  by (simp add: case_prod_beta)

lemma rightrec_43: "n > 0 \<Longrightarrow> rightrec u v lc rc ((4 * real m + 3) / 2 ^ (Suc n)) = rightrec u v lc rc ((2 * real m + 1) / 2^n)"
  unfolding dyad_rec2_def dyad_rec_43_times2
  by (simp add: case_prod_beta)

lemma dyadics_in_open_unit_interval:
   "{0<..<1} \<inter> (\<Union>k m. {real m / 2^k}) = (\<Union>k. \<Union>m \<in> {0<..<2^k}. {real m / 2^k})"
  by (auto simp: field_split_simps)



theorem homeomorphic_monotone_image_interval:
  fixes f :: "real \<Rightarrow> 'a::{real_normed_vector,complete_space}"
  assumes cont_f: "continuous_on {0..1} f"
      and conn: "\<And>y. connected ({0..1} \<inter> f -` {y})"
      and f_1not0: "f 1 \<noteq> f 0"
    shows "(f ` {0..1}) homeomorphic {0..1::real}"
proof -
  have "\<exists>c d. a \<le> c \<and> c \<le> m \<and> m \<le> d \<and> d \<le> b \<and>
              (\<forall>x \<in> {c..d}. f x = f m) \<and>
              (\<forall>x \<in> {a..<c}. (f x \<noteq> f m)) \<and>
              (\<forall>x \<in> {d<..b}. (f x \<noteq> f m)) \<and>
              (\<forall>x \<in> {a..<c}. \<forall>y \<in> {d<..b}. f x \<noteq> f y)"
    if m: "m \<in> {a..b}" and ab01: "{a..b} \<subseteq> {0..1}" for a b m
  proof -
    have comp: "compact (f -` {f m} \<inter> {0..1})"
      by (simp add: compact_eq_bounded_closed bounded_Int closed_vimage_Int cont_f)
    obtain c0 d0 where cd0: "{0..1} \<inter> f -` {f m} = {c0..d0}"
      using connected_compact_interval_1 [of "{0..1} \<inter> f -` {f m}"] conn comp
      by (metis Int_commute)
    with that have "m \<in> cbox c0 d0"
      by auto
    obtain c d where cd: "{a..b} \<inter> f -` {f m} = {c..d}"
      using ab01 cd0
      by (rule_tac c="max a c0" and d="min b d0" in that) auto
    then have cdab: "{c..d} \<subseteq> {a..b}"
      by blast
    show ?thesis
    proof (intro exI conjI ballI)
      show "a \<le> c" "d \<le> b"
        using cdab cd m by auto
      show "c \<le> m" "m \<le> d"
        using cd m by auto
      show "\<And>x. x \<in> {c..d} \<Longrightarrow> f x = f m"
        using cd by blast
      show "f x \<noteq> f m" if "x \<in> {a..<c}" for x
        using that m cd [THEN equalityD1, THEN subsetD] \<open>c \<le> m\<close> by force
      show "f x \<noteq> f m" if "x \<in> {d<..b}" for x
        using that m cd [THEN equalityD1, THEN subsetD, of x] \<open>m \<le> d\<close> by force
      show "f x \<noteq> f y" if "x \<in> {a..<c}" "y \<in> {d<..b}" for x y
      proof (cases "f x = f m \<or> f y = f m")
        case True
        then show ?thesis
          using \<open>\<And>x. x \<in> {a..<c} \<Longrightarrow> f x \<noteq> f m\<close> that by auto
      next
        case False
        have False if "f x = f y"
        proof -
          have "x \<le> m" "m \<le> y"
            using \<open>c \<le> m\<close> \<open>x \<in> {a..<c}\<close>  \<open>m \<le> d\<close> \<open>y \<in> {d<..b}\<close> by auto
          then have "x \<in> ({0..1} \<inter> f -` {f y})" "y \<in> ({0..1} \<inter> f -` {f y})"
            using \<open>x \<in> {a..<c}\<close> \<open>y \<in> {d<..b}\<close> ab01 by (auto simp: that)
          then have "m \<in> ({0..1} \<inter> f -` {f y})"
            by (meson \<open>m \<le> y\<close> \<open>x \<le> m\<close> is_interval_connected_1 conn [of "f y"] is_interval_1)
          with False show False by auto
        qed
        then show ?thesis by auto
      qed
    qed
  qed
  then obtain leftcut rightcut where LR:
    "\<And>a b m. \<lbrakk>m \<in> {a..b}; {a..b} \<subseteq> {0..1}\<rbrakk> \<Longrightarrow>
            (a \<le> leftcut a b m \<and> leftcut a b m \<le> m \<and> m \<le> rightcut a b m \<and> rightcut a b m \<le> b \<and>
            (\<forall>x \<in> {leftcut a b m..rightcut a b m}. f x = f m) \<and>
            (\<forall>x \<in> {a..<leftcut a b m}. f x \<noteq> f m) \<and>
            (\<forall>x \<in> {rightcut a b m<..b}. f x \<noteq> f m) \<and>
            (\<forall>x \<in> {a..<leftcut a b m}. \<forall>y \<in> {rightcut a b m<..b}. f x \<noteq> f y))"
    apply atomize
    apply (clarsimp simp only: imp_conjL [symmetric] choice_iff choice_iff')
    apply (rule that, blast)
    done
  then have left_right: "\<And>a b m. \<lbrakk>m \<in> {a..b}; {a..b} \<subseteq> {0..1}\<rbrakk> \<Longrightarrow> a \<le> leftcut a b m \<and> rightcut a b m \<le> b"
       and  left_right_m: "\<And>a b m. \<lbrakk>m \<in> {a..b}; {a..b} \<subseteq> {0..1}\<rbrakk> \<Longrightarrow> leftcut a b m \<le> m \<and> m \<le> rightcut a b m"
    by auto
  have left_neq: "\<lbrakk>a \<le> x; x < leftcut a b m; a \<le> m; m \<le> b; {a..b} \<subseteq> {0..1}\<rbrakk> \<Longrightarrow> f x \<noteq> f m"
    and right_neq: "\<lbrakk>rightcut a b m < x; x \<le> b; a \<le> m; m \<le> b; {a..b} \<subseteq> {0..1}\<rbrakk> \<Longrightarrow> f x \<noteq> f m"
    and left_right_neq: "\<lbrakk>a \<le> x; x < leftcut a b m; rightcut a b m < y; y \<le> b; a \<le> m; m \<le> b; {a..b} \<subseteq> {0..1}\<rbrakk> \<Longrightarrow> f x \<noteq> f m"
    and feqm: "\<lbrakk>leftcut a b m \<le> x; x \<le> rightcut a b m; a \<le> m; m \<le> b; {a..b} \<subseteq> {0..1}\<rbrakk>
                         \<Longrightarrow> f x = f m" for a b m x y
    by (meson atLeastAtMost_iff greaterThanAtMost_iff atLeastLessThan_iff LR)+
  have f_eqI: "\<And>a b m x y. \<lbrakk>leftcut a b m \<le> x; x \<le> rightcut a b m; leftcut a b m \<le> y; y \<le> rightcut a b m;
                             a \<le> m; m \<le> b; {a..b} \<subseteq> {0..1}\<rbrakk>  \<Longrightarrow> f x = f y"
    by (metis feqm)
  define u where "u \<equiv> rightcut 0 1 0"
  have lc[simp]: "leftcut 0 1 0 = 0" and u01: "0 \<le> u" "u \<le> 1"
    using LR [of 0 0 1] by (auto simp: u_def)
  have f0u: "\<And>x. x \<in> {0..u} \<Longrightarrow> f x = f 0"
    using LR [of 0 0 1] unfolding u_def [symmetric]
    by (metis \<open>leftcut 0 1 0 = 0\<close> atLeastAtMost_iff order_refl zero_le_one)
  have fu1: "\<And>x. x \<in> {u<..1} \<Longrightarrow> f x \<noteq> f 0"
    using LR [of 0 0 1] unfolding u_def [symmetric] by fastforce
  define v where "v \<equiv> leftcut u 1 1"
  have rc[simp]: "rightcut u 1 1 = 1" and v01: "u \<le> v" "v \<le> 1"
    using LR [of 1 u 1] u01  by (auto simp: v_def)
  have fuv: "\<And>x. x \<in> {u..<v} \<Longrightarrow> f x \<noteq> f 1"
    using LR [of 1 u 1] u01 v_def by fastforce
  have f0v: "\<And>x. x \<in> {0..<v} \<Longrightarrow> f x \<noteq> f 1"
    by (metis f_1not0 atLeastAtMost_iff atLeastLessThan_iff f0u fuv linear)
  have fv1: "\<And>x. x \<in> {v..1} \<Longrightarrow> f x = f 1"
    using LR [of 1 u 1] u01 v_def by (metis atLeastAtMost_iff atLeastatMost_subset_iff order_refl rc)
  define a where "a \<equiv> leftrec u v leftcut rightcut"
  define b where "b \<equiv> rightrec u v leftcut rightcut"
  define c where "c \<equiv> \<lambda>x. midpoint (a x) (b x)"
  have a_real [simp]: "a (real j) = u" for j
    using a_def leftrec_base
    by (metis nonzero_mult_div_cancel_right of_nat_mult of_nat_numeral zero_neq_numeral)
  have b_real [simp]: "b (real j) = v" for j
    using b_def rightrec_base
    by (metis nonzero_mult_div_cancel_right of_nat_mult of_nat_numeral zero_neq_numeral)
  have a41: "a ((4 * real m + 1) / 2^Suc n) = a ((2 * real m + 1) / 2^n)" if "n > 0" for m n
    using that a_def leftrec_41 by blast
  have b41: "b ((4 * real m + 1) / 2^Suc n) =
               leftcut (a ((2 * real m + 1) / 2^n))
                       (b ((2 * real m + 1) / 2^n))
                       (c ((2 * real m + 1) / 2^n))" if "n > 0" for m n
    using that a_def b_def c_def rightrec_41 by blast
  have a43: "a ((4 * real m + 3) / 2^Suc n) =
               rightcut (a ((2 * real m + 1) / 2^n))
                        (b ((2 * real m + 1) / 2^n))
                        (c ((2 * real m + 1) / 2^n))" if "n > 0" for m n
    using that a_def b_def c_def leftrec_43 by blast
  have b43: "b ((4 * real m + 3) / 2^Suc n) = b ((2 * real m + 1) / 2^n)" if "n > 0" for m n
    using that b_def rightrec_43 by blast
  have uabv: "u \<le> a (real m / 2 ^ n) \<and> a (real m / 2 ^ n) \<le> b (real m / 2 ^ n) \<and> b (real m / 2 ^ n) \<le> v" for m n
  proof (induction n arbitrary: m)
    case 0
    then show ?case by (simp add: v01)
  next
    case (Suc n p)
    show ?case
    proof (cases "even p")
      case True
      then obtain m where "p = 2*m" by (metis evenE)
      then show ?thesis
        by (simp add: Suc.IH)
    next
      case False
      then obtain m where m: "p = 2*m + 1" by (metis oddE)
      show ?thesis
      proof (cases n)
        case 0
        then show ?thesis
          by (simp add: a_def b_def leftrec_base rightrec_base v01)
      next
        case (Suc n')
        then have "n > 0" by simp
        have a_le_c: "a (real m / 2^n) \<le> c (real m / 2^n)" for m
          unfolding c_def by (metis Suc.IH ge_midpoint_1)
        have c_le_b: "c (real m / 2^n) \<le> b (real m / 2^n)" for m
          unfolding c_def by (metis Suc.IH le_midpoint_1)
        have c_ge_u: "c (real m / 2^n) \<ge> u" for m
          using Suc.IH a_le_c order_trans by blast
        have c_le_v: "c (real m / 2^n) \<le> v" for m
          using Suc.IH c_le_b order_trans by blast
        have a_ge_0: "0 \<le> a (real m / 2^n)" for m
          using Suc.IH order_trans u01(1) by blast
        have b_le_1: "b (real m / 2^n) \<le> 1" for m
          using Suc.IH order_trans v01(2) by blast
        have left_le: "leftcut (a ((real m) / 2^n)) (b ((real m) / 2^n)) (c ((real m) / 2^n)) \<le> c ((real m) / 2^n)" for m
          by (simp add: LR a_ge_0 a_le_c b_le_1 c_le_b)
        have right_ge: "rightcut (a ((real m) / 2^n)) (b ((real m) / 2^n)) (c ((real m) / 2^n)) \<ge> c ((real m) / 2^n)" for m
          by (simp add: LR a_ge_0 a_le_c b_le_1 c_le_b)
        show ?thesis
        proof (cases "even m")
          case True
          then obtain r where r: "m = 2*r" by (metis evenE)
          show ?thesis
            using order_trans [OF left_le c_le_v, of "1+2*r"] Suc.IH [of "m+1"] 
            using a_le_c [of "m+1"] c_le_b [of "m+1"] a_ge_0 [of "m+1"] b_le_1 [of "m+1"] left_right \<open>n > 0\<close>
            by (simp_all add: r m add.commute [of 1]  a41 b41 del: power_Suc)
        next
          case False
          then obtain r where r: "m = 2*r + 1" by (metis oddE)
          show ?thesis
            using order_trans [OF c_ge_u right_ge, of "1+2*r"] Suc.IH [of "m"]
            using a_le_c [of "m"] c_le_b [of "m"] a_ge_0 [of "m"] b_le_1 [of "m"] left_right \<open>n > 0\<close>
            apply (simp_all add: r m add.commute [of 3] a43 b43 del: power_Suc)
            by (simp add: add.commute)
        qed
      qed
    qed
  qed
  have a_ge_0 [simp]: "0 \<le> a(m / 2^n)" and b_le_1 [simp]: "b(m / 2^n) \<le> 1" for m::nat and n
    using uabv order_trans u01 v01 by blast+
  then have b_ge_0 [simp]: "0 \<le> b(m / 2^n)" and a_le_1 [simp]: "a(m / 2^n) \<le> 1" for m::nat and n
    using uabv order_trans by blast+
  have alec [simp]: "a(m / 2^n) \<le> c(m / 2^n)" and cleb [simp]: "c(m / 2^n) \<le> b(m / 2^n)" for m::nat and n
    by (auto simp: c_def ge_midpoint_1 le_midpoint_1 uabv)
  have c_ge_0 [simp]: "0 \<le> c(m / 2^n)" and c_le_1 [simp]: "c(m / 2^n) \<le> 1" for m::nat and n
    using a_ge_0 alec b_le_1 cleb order_trans by blast+
  have "\<lbrakk>d = m-n; odd j; \<bar>real i / 2^m - real j / 2^n\<bar> < 1/2 ^ n\<rbrakk>
        \<Longrightarrow> (a(j / 2^n)) \<le> (c(i / 2^m)) \<and> (c(i / 2^m)) \<le> (b(j / 2^n))" for d i j m n
  proof (induction d arbitrary: j n rule: less_induct)
    case (less d j n)
    show ?case
    proof (cases "m \<le> n")
      case True
      have "\<bar>2^n\<bar> * \<bar>real i / 2^m - real j / 2^n\<bar> = 0"
      proof (rule Ints_nonzero_abs_less1)
        have "(real i * 2^n - real j * 2^m) / 2^m = (real i * 2^n) / 2^m - (real j * 2^m) / 2^m"
          using diff_divide_distrib by blast
        also have "... = (real i * 2 ^ (n-m)) - (real j)"
          using True by (auto simp: power_diff field_simps)
        also have "... \<in> \<int>"
          by simp
        finally have "(real i * 2^n - real j * 2^m) / 2^m \<in> \<int>" .
        with True Ints_abs show "\<bar>2^n\<bar> * \<bar>real i / 2^m - real j / 2^n\<bar> \<in> \<int>"
          by (fastforce simp: field_split_simps)
        show "\<bar>\<bar>2^n\<bar> * \<bar>real i / 2^m - real j / 2^n\<bar>\<bar> < 1"
          using less.prems by (auto simp: field_split_simps)
      qed
      then have "real i / 2^m = real j / 2^n"
        by auto
      then show ?thesis
        by auto
    next
      case False
      then have "n < m" by auto
      obtain k where k: "j = Suc (2*k)"
        using \<open>odd j\<close> oddE by fastforce
      show ?thesis
      proof (cases "n > 0")
        case False
        then have "a (real j / 2^n) = u"
          by simp
        also have "... \<le> c (real i / 2^m)"
          using alec uabv by (blast intro: order_trans)
        finally have ac: "a (real j / 2^n) \<le> c (real i / 2^m)" .
        have "c (real i / 2^m) \<le> v"
          using cleb uabv by (blast intro: order_trans)
        also have "... = b (real j / 2^n)"
          using False by simp
        finally show ?thesis
          by (auto simp: ac)
      next
        case True show ?thesis
        proof (cases "i / 2^m" "j / 2^n" rule: linorder_cases)
          case less
          moreover have "real (4 * k + 1) / 2 ^ Suc n + 1 / (2 ^ Suc n) = real j / 2 ^ n"
            using k by (force simp: field_split_simps)
          moreover have "\<bar>real i / 2 ^ m - j / 2 ^ n\<bar> < 2 / (2 ^ Suc n)"
            using less.prems by simp
          ultimately have closer: "\<bar>real i / 2 ^ m - real (4 * k + 1) / 2 ^ Suc n\<bar> < 1 / (2 ^ Suc n)"
            using less.prems by linarith
          have "a (real (4 * k + 1) / 2 ^ Suc n) \<le> c (i / 2 ^ m) \<and>
                   c (real i / 2 ^ m) \<le> b (real (4 * k + 1) / 2 ^ Suc n)"
          proof (rule less.IH [OF _ refl])
            show "m - Suc n < d"
              using \<open>n < m\<close> diff_less_mono2 less.prems(1) lessI by presburger
            show "\<bar>real i / 2 ^ m - real (4 * k + 1) / 2 ^ Suc n\<bar> < 1 / 2 ^ Suc n"
              using closer \<open>n < m\<close> \<open>d = m - n\<close> by (auto simp: field_split_simps \<open>n < m\<close> diff_less_mono2)
          qed auto
          then show ?thesis
            using LR [of "c((2*k + 1) / 2^n)" "a((2*k + 1) / 2^n)" "b((2*k + 1) / 2^n)"]
            using alec [of "2*k+1"] cleb [of "2*k+1"] a_ge_0 [of "2*k+1"] b_le_1 [of "2*k+1"]
            using k a41 b41 \<open>0 < n\<close>
            by (simp add: add.commute)
        next
          case equal then show ?thesis by simp
        next
          case greater
          moreover have "real (4 * k + 3) / 2 ^ Suc n - 1 / (2 ^ Suc n) = real j / 2 ^ n"
            using k by (force simp: field_split_simps)
          moreover have "\<bar>real i / 2 ^ m - real j / 2 ^ n\<bar> < 2 * 1 / (2 ^ Suc n)"
            using less.prems by simp
          ultimately have closer: "\<bar>real i / 2 ^ m - real (4 * k + 3) / 2 ^ Suc n\<bar> < 1 / (2 ^ Suc n)"
            using less.prems by linarith
          have "a (real (4 * k + 3) / 2 ^ Suc n) \<le> c (real i / 2 ^ m) \<and>
                   c (real i / 2 ^ m) \<le> b (real (4 * k + 3) / 2 ^ Suc n)"
          proof (rule less.IH [OF _ refl])
            show "m - Suc n < d"
              using \<open>n < m\<close> diff_less_mono2 less.prems(1) by blast
            show "\<bar>real i / 2 ^ m - real (4 * k + 3) / 2 ^ Suc n\<bar> < 1 / 2 ^ Suc n"
              using closer \<open>n < m\<close> \<open>d = m - n\<close> by (auto simp: field_split_simps  \<open>n < m\<close> diff_less_mono2)
          qed auto
          then show ?thesis
            using LR [of "c((2*k + 1) / 2^n)" "a((2*k + 1) / 2^n)" "b((2*k + 1) / 2^n)"]
            using alec [of "2*k+1"] cleb [of "2*k+1"] a_ge_0 [of "2*k+1"] b_le_1 [of "2*k+1"]
            using k a43 b43 \<open>0 < n\<close>
            by (simp add: add.commute)
        qed
      qed
    qed
  qed
  then have aj_le_ci: "a (real j / 2 ^ n) \<le> c (real i / 2 ^ m)"
    and ci_le_bj: "c (real i / 2 ^ m) \<le> b (real j / 2 ^ n)" if "odd j" "\<bar>real i / 2^m - real j / 2^n\<bar> < 1/2 ^ n" for i j m n
    using that by blast+
  have close_ab: "odd m \<Longrightarrow> \<bar>a (real m / 2 ^ n) - b (real m / 2 ^ n)\<bar> \<le> 2 / 2^n" for m n
  proof (induction n arbitrary: m)
    case 0
    with u01 v01 show ?case by auto
  next
    case (Suc n m)
    with oddE obtain k where k: "m = Suc (2*k)" by fastforce
    show ?case
    proof (cases "n > 0")
      case False
      with u01 v01 show ?thesis
        by (simp add: a_def b_def leftrec_base rightrec_base)
    next
      case True
      show ?thesis
      proof (cases "even k")
        case True
        then obtain j where j: "k = 2*j" by (metis evenE)
        have "\<bar>a ((2 * real j + 1) / 2 ^ n) - (b ((2 * real j + 1) / 2 ^ n))\<bar> \<le> 2/2 ^ n"
        proof -
          have "odd (Suc k)"
            using True by auto
          then show ?thesis
            by (metis (no_types) Groups.add_ac(2) Suc.IH j of_nat_Suc of_nat_mult of_nat_numeral)
        qed
        moreover have "a ((2 * real j + 1) / 2 ^ n) \<le>
                       leftcut (a ((2 * real j + 1) / 2 ^ n)) (b ((2 * real j + 1) / 2 ^ n)) (c ((2 * real j + 1) / 2 ^ n))"
          using alec [of "2*j+1"] cleb [of "2*j+1"] a_ge_0 [of "2*j+1"]  b_le_1 [of "2*j+1"]
          by (auto simp: add.commute left_right)
        moreover have "leftcut (a ((2 * real j + 1) / 2 ^ n)) (b ((2 * real j + 1) / 2 ^ n)) (c ((2 * real j + 1) / 2 ^ n)) \<le>
                         c ((2 * real j + 1) / 2 ^ n)"
          using alec [of "2*j+1"] cleb [of "2*j+1"] a_ge_0 [of "2*j+1"]  b_le_1 [of "2*j+1"]
          by (auto simp: add.commute left_right_m)
        ultimately have "\<bar>a ((2 * real j + 1) / 2 ^ n) -
                          leftcut (a ((2 * real j + 1) / 2 ^ n)) (b ((2 * real j + 1) / 2 ^ n)) (c ((2 * real j + 1) / 2 ^ n))\<bar>
                   \<le> 2/2 ^ Suc n"
          by (simp add: c_def midpoint_def)
        with j k \<open>n > 0\<close> show ?thesis
          by (simp add: add.commute [of 1] a41 b41 del: power_Suc)
      next
        case False
        then obtain j where j: "k = 2*j + 1" by (metis oddE)
        have "\<bar>a ((2 * real j + 1) / 2 ^ n) - (b ((2 * real j + 1) / 2 ^ n))\<bar> \<le> 2/2 ^ n"
          using Suc.IH [OF False] j by (auto simp: algebra_simps)
        moreover have "c ((2 * real j + 1) / 2 ^ n) \<le>
                       rightcut (a ((2 * real j + 1) / 2 ^ n)) (b ((2 * real j + 1) / 2 ^ n)) (c ((2 * real j + 1) / 2 ^ n))"
          using alec [of "2*j+1"] cleb [of "2*j+1"] a_ge_0 [of "2*j+1"]  b_le_1 [of "2*j+1"]
          by (auto simp: add.commute left_right_m)
        moreover have "rightcut (a ((2 * real j + 1) / 2 ^ n)) (b ((2 * real j + 1) / 2 ^ n)) (c ((2 * real j + 1) / 2 ^ n)) \<le>
                         b ((2 * real j + 1) / 2 ^ n)"
          using alec [of "2*j+1"] cleb [of "2*j+1"] a_ge_0 [of "2*j+1"]  b_le_1 [of "2*j+1"]
          by (auto simp: add.commute left_right)
        ultimately have "\<bar>rightcut (a ((2 * real j + 1) / 2 ^ n)) (b ((2 * real j + 1) / 2 ^ n)) (c ((2 * real j + 1) / 2 ^ n)) -
                          b ((2 * real j + 1) / 2 ^ n)\<bar>  \<le>  2/2 ^ Suc n"
          by (simp add: c_def midpoint_def)
        with j k \<open>n > 0\<close> show ?thesis
          by (simp add: add.commute [of 3] a43 b43 del: power_Suc)
      qed
    qed
  qed
  have m1_to_3: "4 * real k - 1 = real (4 * (k-1)) + 3" if "0 < k" for k
    using that by auto
  have fb_eq_fa: "\<lbrakk>0 < j; 2*j < 2 ^ n\<rbrakk> \<Longrightarrow> f(b((2 * real j - 1) / 2^n)) = f(a((2 * real j + 1) / 2^n))" for n j
  proof (induction n arbitrary: j)
    case 0
    then show ?case by auto
  next
    case (Suc n j) show ?case
    proof (cases "n > 0")
      case False
      with Suc.prems show ?thesis by auto
    next
      case True
      show ?thesis proof (cases "even j")
        case True
        then obtain k where k: "j = 2*k" by (metis evenE)
        with \<open>0 < j\<close> have "k > 0" "2 * k < 2 ^ n"
          using Suc.prems(2) k by auto
        with k \<open>0 < n\<close> Suc.IH [of k] show ?thesis
          by (simp add: m1_to_3 a41 b43 del: power_Suc) (auto simp: of_nat_diff)
      next
        case False
        then obtain k where k: "j = 2*k + 1" by (metis oddE)
        have "f (leftcut (a ((2 * k + 1) / 2^n)) (b ((2 * k + 1) / 2^n)) (c ((2 * k + 1) / 2^n)))
              = f (c ((2 * k + 1) / 2^n))"
          "f (c ((2 * k + 1) / 2^n))
              = f (rightcut (a ((2 * k + 1) / 2^n)) (b ((2 * k + 1) / 2^n)) (c ((2 * k + 1) / 2^n)))"
          using alec [of "2*k+1" n] cleb [of "2*k+1" n] a_ge_0 [of "2*k+1" n]  b_le_1 [of "2*k+1" n] k
          using left_right_m [of "c((2*k + 1) / 2^n)" "a((2*k + 1) / 2^n)" "b((2*k + 1) / 2^n)"]
          by (auto simp: add.commute  feqm [OF order_refl]  feqm [OF _ order_refl, symmetric])
        then
        show ?thesis
          by (simp add: k add.commute [of 1] add.commute [of 3] a43 b41\<open>0 < n\<close> del: power_Suc)
      qed
    qed
  qed
  have f_eq_fc: "\<lbrakk>0 < j; j < 2 ^ n\<rbrakk>
                 \<Longrightarrow> f(b((2*j - 1) / 2 ^ (Suc n))) = f(c(j / 2^n)) \<and>
                     f(a((2*j + 1) / 2 ^ (Suc n))) = f(c(j / 2^n))" for n and j::nat
  proof (induction n arbitrary: j)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    show ?case
    proof (cases "even j")
      case True
      then obtain k where k: "j = 2*k" by (metis evenE)
      then have less2n: "k < 2 ^ n"
        using Suc.prems(2) by auto
      have "0 < k" using \<open>0 < j\<close> k by linarith
      then have m1_to_3: "real (4 * k - Suc 0) = real (4 * (k-1)) + 3"
        by auto
      then show ?thesis
        using Suc.IH [of k] k \<open>0 < k\<close>
        by (simp add: less2n add.commute [of 1] m1_to_3 a41 b43 del: power_Suc) (auto simp: of_nat_diff)
    next
      case False
      then obtain k where k: "j = 2*k + 1" by (metis oddE)
      with Suc.prems have "k < 2^n" by auto
      show ?thesis
        using alec [of "2*k+1" "Suc n"] cleb [of "2*k+1" "Suc n"] a_ge_0 [of "2*k+1" "Suc n"]  b_le_1 [of "2*k+1" "Suc n"] k
        using left_right_m [of "c((2*k + 1) / 2 ^ Suc n)" "a((2*k + 1) / 2 ^ Suc n)" "b((2*k + 1) / 2 ^ Suc n)"]
        apply (simp add: add.commute [of 1] add.commute [of 3] m1_to_3 b41 a43 del: power_Suc)
        apply (force intro: feqm)
        done
    qed
  qed
  define D01 where "D01 \<equiv> {0<..<1} \<inter> (\<Union>k m. {real m / 2^k})"
  have cloD01 [simp]: "closure D01 = {0..1}"
    unfolding D01_def
    by (subst closure_dyadic_rationals_in_convex_set_pos_1) auto
  have "uniformly_continuous_on D01 (f \<circ> c)"
  proof (clarsimp simp: uniformly_continuous_on_def)
    fix e::real
    assume "0 < e"
    have ucontf: "uniformly_continuous_on {0..1} f"
      by (simp add: compact_uniformly_continuous [OF cont_f])
    then obtain d where "0 < d" and d: "\<And>x x'. \<lbrakk>x \<in> {0..1}; x' \<in> {0..1}; norm (x' - x) < d\<rbrakk> \<Longrightarrow> norm (f x' - f x) < e/2"
      unfolding uniformly_continuous_on_def dist_norm
      by (metis \<open>0 < e\<close> less_divide_eq_numeral1(1) mult_zero_left)
    obtain n where n: "1/2^n < min d 1"
      by (metis \<open>0 < d\<close> divide_less_eq_1 less_numeral_extra(1) min_def one_less_numeral_iff power_one_over real_arch_pow_inv semiring_norm(76) zero_less_numeral)
    with gr0I have "n > 0"
      by (force simp: field_split_simps)
    show "\<exists>d>0. \<forall>x\<in>D01. \<forall>x'\<in>D01. dist x' x < d \<longrightarrow> dist (f (c x')) (f (c x)) < e"
    proof (intro exI ballI impI conjI)
      show "(0::real) < 1/2^n" by auto
    next
      have dist_fc_close: "dist (f(c(real i / 2^m))) (f(c(real j / 2^n))) < e/2"
        if i: "0 < i" "i < 2 ^ m" and j: "0 < j" "j < 2 ^ n" and clo: "abs(i / 2^m - j / 2^n) < 1/2 ^ n" for i j m
      proof -
        have abs3: "\<bar>x - a\<bar> < e \<Longrightarrow> x = a \<or> \<bar>x - (a - e/2)\<bar> < e/2 \<or> \<bar>x - (a + e/2)\<bar> < e/2" for x a e::real
          by linarith
        consider "i / 2 ^ m = j / 2 ^ n"
          | "\<bar>i / 2 ^ m - (2 * j - 1) / 2 ^ Suc n\<bar> < 1/2 ^ Suc n"
          | "\<bar>i / 2 ^ m - (2 * j + 1) / 2 ^ Suc n\<bar> < 1/2 ^ Suc n"
          using abs3 [OF clo] j by (auto simp: field_simps of_nat_diff)
        then show ?thesis
        proof cases
          case 1 with \<open>0 < e\<close> show ?thesis by auto
        next
          case 2
          have *: "abs(a - b) \<le> 1/2 ^ n \<and> 1/2 ^ n < d \<and> a \<le> c \<and> c \<le> b \<Longrightarrow> b - c < d" for a b c
            by auto
          have "norm (c (real i / 2 ^ m) - b (real (2 * j - 1) / 2 ^ Suc n)) < d"
            using 2 j n close_ab [of "2*j-1" "Suc n"]
            using b_ge_0 [of "2*j-1" "Suc n"] b_le_1 [of "2*j-1" "Suc n"]
            using aj_le_ci [of "2*j-1" i m "Suc n"]
            using ci_le_bj [of "2*j-1" i m "Suc n"]
            apply (simp add: divide_simps of_nat_diff del: power_Suc)
            apply (auto simp: divide_simps intro!: *)
            done
          moreover have "f(c(j / 2^n)) = f(b ((2*j - 1) / 2 ^ (Suc n)))"
            using f_eq_fc [OF j] by metis
          ultimately show ?thesis
            by (metis dist_norm atLeastAtMost_iff b_ge_0 b_le_1 c_ge_0 c_le_1 d)
        next
          case 3
          have *: "abs(a - b) \<le> 1/2 ^ n \<and> 1/2 ^ n < d \<and> a \<le> c \<and> c \<le> b \<Longrightarrow> c - a < d" for a b c
            by auto
          have "norm (c (real i / 2 ^ m) - a (real (2 * j + 1) / 2 ^ Suc n)) < d"
            using 3 j n close_ab [of "2*j+1" "Suc n"]
            using b_ge_0 [of "2*j+1" "Suc n"] b_le_1 [of "2*j+1" "Suc n"]
            using aj_le_ci [of "2*j+1" i m "Suc n"]
            using ci_le_bj [of "2*j+1" i m "Suc n"]
            apply (simp add: divide_simps of_nat_diff del: power_Suc)
            apply (auto simp: divide_simps intro!: *)
            done
          moreover have "f(c(j / 2^n)) = f(a ((2*j + 1) / 2 ^ (Suc n)))"
            using f_eq_fc [OF j] by metis
          ultimately show ?thesis
            by (metis dist_norm a_ge_0 atLeastAtMost_iff a_ge_0 a_le_1 c_ge_0 c_le_1 d)
        qed
      qed
      show "dist (f (c x')) (f (c x)) < e"
        if "x \<in> D01" "x' \<in> D01" "dist x' x < 1/2^n" for x x'
        using that unfolding D01_def dyadics_in_open_unit_interval
      proof clarsimp
        fix i k::nat and m p
        assume i: "0 < i" "i < 2 ^ m" and k: "0<k" "k < 2 ^ p"
        assume clo: "dist (real k / 2 ^ p) (real i / 2 ^ m) < 1/2 ^ n"
        obtain j::nat where "0 < j" "j < 2 ^ n"
          and clo_ij: "abs(i / 2^m - j / 2^n) < 1/2 ^ n"
          and clo_kj: "abs(k / 2^p - j / 2^n) < 1/2 ^ n"
        proof -
          have "max (2^n * i / 2^m) (2^n * k / 2^p) \<ge> 0"
            by (auto simp: le_max_iff_disj)
          then obtain j where "floor (max (2^n*i / 2^m) (2^n*k / 2^p)) = int j"
            using zero_le_floor zero_le_imp_eq_int by blast
          then have j_le: "real j \<le> max (2^n * i / 2^m) (2^n * k / 2^p)"
            and less_j1: "max (2^n * i / 2^m) (2^n * k / 2^p) < real j + 1"
            using floor_correct [of "max (2^n * i / 2^m) (2^n * k / 2^p)"] by linarith+
          show thesis
          proof (cases "j = 0")
            case True
            show thesis
            proof
              show "(1::nat) < 2 ^ n"
                by (metis Suc_1 \<open>0 < n\<close> lessI one_less_power)
              show "\<bar>real i / 2 ^ m - real 1/2 ^ n\<bar> < 1/2 ^ n"
                using i less_j1 by (simp add: dist_norm field_simps True)
              show "\<bar>real k / 2 ^ p - real 1/2 ^ n\<bar> < 1/2 ^ n"
                using k less_j1 by (simp add: dist_norm field_simps True)
            qed simp
          next
            case False
            have 1: "real j * 2 ^ m < real i * 2 ^ n"
              if j: "real j * 2 ^ p \<le> real k * 2 ^ n" and k: "real k * 2 ^ m < real i * 2 ^ p"
              for i k m p
            proof -
              have "real j * 2 ^ p * 2 ^ m \<le> real k * 2 ^ n * 2 ^ m"
                using j by simp
              moreover have "real k * 2 ^ m * 2 ^ n < real i * 2 ^ p * 2 ^ n"
                using k by simp
              ultimately have "real j * 2 ^ p * 2 ^ m < real i * 2 ^ p * 2 ^ n"
                by (simp only: mult_ac)
              then show ?thesis
                by simp
            qed
            have 2: "real j * 2 ^ m < 2 ^ m + real i * 2 ^ n"
              if j: "real j * 2 ^ p \<le> real k * 2 ^ n" and k: "real k * (2 ^ m * 2 ^ n) < 2 ^ m * 2 ^ p + real i * (2 ^ n * 2 ^ p)"
              for i k m p
            proof -
              have "real j * 2 ^ p * 2 ^ m \<le> real k * (2 ^ m * 2 ^ n)"
                using j by simp
              also have "... < 2 ^ m * 2 ^ p + real i * (2 ^ n * 2 ^ p)"
                by (rule k)
              finally have "(real j * 2 ^ m) * 2 ^ p < (2 ^ m + real i * 2 ^ n) * 2 ^ p"
                by (simp add: algebra_simps)
              then show ?thesis
                by simp
            qed
            have 3: "real j * 2 ^ p < 2 ^ p + real k * 2 ^ n"
              if j: "real j * 2 ^ m \<le> real i * 2 ^ n" and i: "real i * 2 ^ p \<le> real k * 2 ^ m"
            proof -
              have "real j * 2 ^ m * 2 ^ p \<le> real i * 2 ^ n * 2 ^ p"
                using j by simp
              moreover have "real i * 2 ^ p * 2 ^ n \<le> real k * 2 ^ m * 2 ^ n"
                using i by simp
              ultimately have "real j * 2 ^ m * 2 ^ p \<le> real k * 2 ^ m * 2 ^ n"
                by (simp only: mult_ac)
              then have "real j * 2 ^ p \<le> real k * 2 ^ n"
                by simp
              also have "... < 2 ^ p + real k * 2 ^ n"
                by auto
              finally show ?thesis by simp
            qed
            show ?thesis
            proof
              have "2 ^ n * real i / 2 ^ m < 2 ^ n" "2 ^ n * real k / 2 ^ p < 2 ^ n"
                using i k by (auto simp: field_simps)
              then have "max (2^n * i / 2^m) (2^n * k / 2^p) < 2^n"
                by simp
              with j_le have "real j < 2 ^ n" by linarith 
              then show "j < 2 ^ n"
                by auto
              have "\<bar>real i * 2 ^ n - real j * 2 ^ m\<bar> < 2 ^ m"
                using clo less_j1 j_le
                 by (auto simp: le_max_iff_disj field_split_simps dist_norm abs_if split: if_split_asm dest: 1 2)
              then show "\<bar>real i / 2 ^ m - real j / 2 ^ n\<bar> < 1/2 ^ n"
                by (auto simp: field_split_simps)
              have "\<bar>real k * 2 ^ n - real j * 2 ^ p\<bar> < 2 ^ p"
                using clo less_j1 j_le
                by (auto simp: le_max_iff_disj field_split_simps dist_norm abs_if split: if_split_asm dest: 3 2)
              then show "\<bar>real k / 2 ^ p - real j / 2 ^ n\<bar> < 1/2 ^ n"
                by (auto simp: le_max_iff_disj field_split_simps dist_norm)
            qed (use False in simp)
          qed
        qed
        show "dist (f (c (real k / 2 ^ p))) (f (c (real i / 2 ^ m))) < e"
        proof (rule dist_triangle_half_l)
          show "dist (f (c (real k / 2 ^ p))) (f(c(j / 2^n))) < e/2"
            using \<open>0 < j\<close> \<open>j < 2 ^ n\<close> k clo_kj 
            by (intro dist_fc_close) auto
          show "dist (f (c (real i / 2 ^ m))) (f (c (real j / 2 ^ n))) < e/2"
            using \<open>0 < j\<close> \<open>j < 2 ^ n\<close> i clo_ij 
            by (intro dist_fc_close) auto
        qed
      qed
    qed
  qed
  then obtain h where ucont_h: "uniformly_continuous_on {0..1} h"
    and fc_eq: "\<And>x. x \<in> D01 \<Longrightarrow> (f \<circ> c) x = h x"
  proof (rule uniformly_continuous_on_extension_on_closure [of D01 "f \<circ> c"])
  qed (use closure_subset [of D01] in \<open>auto intro!: that\<close>)
  then have cont_h: "continuous_on {0..1} h"
    using uniformly_continuous_imp_continuous by blast
  have h_eq: "h (real k / 2 ^ m) = f (c (real k / 2 ^ m))" if "0 < k" "k < 2^m" for k m
    using fc_eq that by (force simp: D01_def)
  have "h ` {0..1} = f ` {0..1}"
  proof
    have "h ` (closure D01) \<subseteq> f ` {0..1}"
    proof (rule image_closure_subset)
      show "continuous_on (closure D01) h"
        using cont_h by simp
      show "closed (f ` {0..1})"
        using compact_continuous_image [OF cont_f] compact_imp_closed by blast
      show "h ` D01 \<subseteq> f ` {0..1}"
        by (force simp: dyadics_in_open_unit_interval D01_def h_eq)
    qed
    with cloD01 show "h ` {0..1} \<subseteq> f ` {0..1}" by simp
    have a12 [simp]: "a (1/2) = u"
      by (metis a_def leftrec_base numeral_One of_nat_numeral)
    have b12 [simp]: "b (1/2) = v"
      by (metis b_def rightrec_base numeral_One of_nat_numeral)
    have "f ` {0..1} \<subseteq> closure(h ` D01)"
    proof (clarsimp simp: closure_approachable dyadics_in_open_unit_interval D01_def)
      fix x e::real
      assume "0 \<le> x" "x \<le> 1" "0 < e"
      have ucont_f: "uniformly_continuous_on {0..1} f"
        using compact_uniformly_continuous cont_f by blast
      then obtain \<delta> where "\<delta> > 0"
        and \<delta>: "\<And>x x'. \<lbrakk>x \<in> {0..1}; x' \<in> {0..1}; dist x' x < \<delta>\<rbrakk> \<Longrightarrow> norm (f x' - f x) < e"
        using \<open>0 < e\<close> by (auto simp: uniformly_continuous_on_def dist_norm)
      have *: "\<exists>m::nat. \<exists>y. odd m \<and> 0 < m \<and> m < 2 ^ n \<and> y \<in> {a(m / 2^n) .. b(m / 2^n)} \<and> f y = f x"
        if "n \<noteq> 0" for n
        using that
      proof (induction n)
        case 0 then show ?case by auto
      next
        case (Suc n)
        show ?case
        proof (cases "n=0")
          case True
          consider "x \<in> {0..u}" | "x \<in> {u..v}" | "x \<in> {v..1}"
            using \<open>0 \<le> x\<close> \<open>x \<le> 1\<close> by force
          then have "\<exists>y\<ge>a (real 1/2). y \<le> b (real 1/2) \<and> f y = f x"
          proof cases
            case 1
            then show ?thesis
              using uabv [of 1 1] f0u [of u] f0u [of x] by force
          next
            case 2
            then show ?thesis
              by (rule_tac x=x in exI) auto
          next
            case 3
            then show ?thesis
              using uabv [of 1 1] fv1 [of v] fv1 [of x] by force
          qed
          with \<open>n=0\<close> show ?thesis
            by (rule_tac x=1 in exI) auto
        next
          case False
          with Suc obtain m y
            where "odd m" "0 < m" and mless: "m < 2 ^ n"
              and y: "y \<in> {a (real m / 2 ^ n)..b (real m / 2 ^ n)}" and feq: "f y = f x"
            by metis
          then obtain j where j: "m = 2*j + 1" by (metis oddE)
          have j4: "4 * j + 1 < 2 ^ Suc n"
            using mless j by (simp add: algebra_simps)

          consider "y \<in> {a((2*j + 1) / 2^n) .. b((4*j + 1) / 2 ^ (Suc n))}"
            | "y \<in> {b((4*j + 1) / 2 ^ (Suc n)) .. a((4*j + 3) / 2 ^ (Suc n))}"
            | "y \<in> {a((4*j + 3) / 2 ^ (Suc n)) .. b((2*j + 1) / 2^n)}"
            using y j by force
          then show ?thesis
          proof cases
            case 1
            show ?thesis
            proof (intro exI conjI)
              show "y \<in> {a (real (4 * j + 1) / 2 ^ Suc n)..b (real (4 * j + 1) / 2 ^ Suc n)}"
                using mless j \<open>n \<noteq> 0\<close> 1 by (simp add: a41 b41 add.commute [of 1] del: power_Suc)
            qed (use feq j4 in auto)
          next
            case 2
            show ?thesis
            proof (intro exI conjI)
              show "b (real (4 * j + 1) / 2 ^ Suc n) \<in> {a (real (4 * j + 1) / 2 ^ Suc n)..b (real (4 * j + 1) / 2 ^ Suc n)}"
                using \<open>n \<noteq> 0\<close> alec [of "2*j+1" n] cleb [of "2*j+1" n] a_ge_0 [of "2*j+1" n] b_le_1 [of "2*j+1" n]
                using left_right [of "c((2*j + 1) / 2^n)" "a((2*j + 1) / 2^n)" "b((2*j + 1) / 2^n)"]
                by (simp add: a41 b41 add.commute [of 1] del: power_Suc)
              show "f (b (real (4 * j + 1) / 2 ^ Suc n)) = f x"
                using \<open>n \<noteq> 0\<close> 2 
                using alec [of "2*j+1" n] cleb [of "2*j+1" n] a_ge_0 [of "2*j+1" n]  b_le_1 [of "2*j+1" n]
                by (force simp add: b41 a43 add.commute [of 1] feq [symmetric] simp del: power_Suc intro: f_eqI)
            qed (use j4 in auto)
          next
            case 3
            show ?thesis
            proof (intro exI conjI)
              show "4 * j + 3 < 2 ^ Suc n"
                using mless j by simp
              show "f y = f x"
                by fact
              show "y \<in> {a (real (4 * j + 3) / 2 ^ Suc n) .. b (real (4 * j + 3) / 2 ^ Suc n)}"
                using 3 False b43 [of n j] by (simp add: add.commute)
            qed (use 3 in auto)
          qed
        qed
      qed
      obtain n where n: "1/2^n < min (\<delta> / 2) 1"
        by (metis \<open>0 < \<delta>\<close> divide_less_eq_1 less_numeral_extra(1) min_less_iff_conj one_less_numeral_iff power_one_over real_arch_pow_inv semiring_norm(76) zero_less_divide_iff zero_less_numeral)
      with gr0I have "n \<noteq> 0"
        by fastforce
      with * obtain m::nat and y
        where "odd m" "0 < m" and mless: "m < 2 ^ n"
          and y: "a(m / 2^n) \<le> y \<and> y \<le> b(m / 2^n)" and feq: "f x = f y"
        by (metis atLeastAtMost_iff)
      then have "0 \<le> y" "y \<le> 1"
        by (meson a_ge_0 b_le_1 order.trans)+
      moreover have "y < \<delta> + c (real m / 2 ^ n)" "c (real m / 2 ^ n) < \<delta> + y"
        using y alec [of m n] cleb [of m n] n field_sum_of_halves close_ab [OF \<open>odd m\<close>, of n]
        by linarith+
      moreover note \<open>0 < m\<close> mless \<open>0 \<le> x\<close> \<open>x \<le> 1\<close>
      ultimately have "dist (h (real m / 2 ^ n)) (f x) < e"
        by (auto simp: dist_norm h_eq feq \<delta>)
      then show "\<exists>k. \<exists>m\<in>{0<..<2 ^ k}. dist (h (real m / 2 ^ k)) (f x) < e"
        using \<open>0 < m\<close> greaterThanLessThan_iff mless by blast
    qed
    also have "... \<subseteq> h ` {0..1}"
    proof (rule closure_minimal)
      show "h ` D01 \<subseteq> h ` {0..1}"
        using cloD01 closure_subset by blast
      show "closed (h ` {0..1})"
        using compact_continuous_image [OF cont_h] compact_imp_closed by auto
    qed
    finally show "f ` {0..1} \<subseteq> h ` {0..1}" .
  qed
  moreover have "inj_on h {0..1}"
  proof -
    have "u < v"
      by (metis atLeastAtMost_iff f0u f_1not0 fv1 order.not_eq_order_implies_strict u01(1) u01(2) v01(1))
    have f_not_fu: "\<And>x. \<lbrakk>u < x; x \<le> v\<rbrakk> \<Longrightarrow> f x \<noteq> f u"
      by (metis atLeastAtMost_iff f0u fu1 greaterThanAtMost_iff order_refl order_trans u01(1) v01(2))
    have f_not_fv: "\<And>x. \<lbrakk>u \<le> x; x < v\<rbrakk> \<Longrightarrow> f x \<noteq> f v"
      by (metis atLeastAtMost_iff order_refl order_trans v01(2) atLeastLessThan_iff fuv fv1)
    have a_less_b:
         "a(j / 2^n) < b(j / 2^n) \<and>
          (\<forall>x. a(j / 2^n) < x \<longrightarrow> x \<le> b(j / 2^n) \<longrightarrow> f x \<noteq> f(a(j / 2^n))) \<and>
          (\<forall>x. a(j / 2^n) \<le> x \<longrightarrow> x < b(j / 2^n) \<longrightarrow> f x \<noteq> f(b(j / 2^n)))" for n and j::nat
    proof (induction n arbitrary: j)
      case 0 then show ?case
        by (simp add: \<open>u < v\<close> f_not_fu f_not_fv)
    next
      case (Suc n j) show ?case
      proof (cases "n > 0")
        case False then show ?thesis
          by (auto simp: a_def b_def leftrec_base rightrec_base \<open>u < v\<close> f_not_fu f_not_fv)
      next
        case True show ?thesis
        proof (cases "even j")
          case True
          with \<open>0 < n\<close> Suc.IH show ?thesis
            by (auto elim!: evenE)
        next
          case False
          then obtain k where k: "j = 2*k + 1" by (metis oddE)
          then show ?thesis
          proof (cases "even k")
            case True
            then obtain m where m: "k = 2*m" by (metis evenE)
            have fleft: "f (leftcut (a ((2*m + 1) / 2^n)) (b ((2*m + 1) / 2^n)) (c ((2*m + 1) / 2^n))) =
                         f (c((2*m + 1) / 2^n))"
              using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n]  b_le_1 [of "2*m+1" n]
              using left_right_m [of "c((2*m + 1) / 2^n)" "a((2*m + 1) / 2^n)" "b((2*m + 1) / 2^n)"]
              by (auto intro: f_eqI)
            show ?thesis
            proof (intro conjI impI notI allI)
              have False if "b (real j / 2 ^ Suc n) \<le> a (real j / 2 ^ Suc n)"
              proof -
                have "f (c ((1 + real m * 2) / 2 ^ n)) = f (a ((1 + real m * 2) / 2 ^ n))"
                  using k m \<open>0 < n\<close> fleft that a41 [of n m] b41 [of n m]
                  using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n]  b_le_1 [of "2*m+1" n]
                  using left_right [of "c((2*m + 1) / 2^n)" "a((2*m + 1) / 2^n)" "b((2*m + 1) / 2^n)"]
                  by (auto simp: algebra_simps)
                moreover have "a (real (1 + m * 2) / 2 ^ n) < c (real (1 + m * 2) / 2 ^ n)"
                  using Suc.IH [of "1 + m * 2"] by (simp add: c_def midpoint_def)
                moreover have "c (real (1 + m * 2) / 2 ^ n) \<le> b (real (1 + m * 2) / 2 ^ n)"
                  using cleb by blast
                ultimately show ?thesis
                  using Suc.IH [of "1 + m * 2"] by force
              qed
              then show "a (real j / 2 ^ Suc n) < b (real j / 2 ^ Suc n)" by force
            next
              fix x
              assume "a (real j / 2 ^ Suc n) < x" "x \<le> b (real j / 2 ^ Suc n)" "f x = f (a (real j / 2 ^ Suc n))"
              then show False
                using Suc.IH [of "1 + m * 2", THEN conjunct2, THEN conjunct1]
                using k m \<open>0 < n\<close> a41 [of n m] b41 [of n m]
                using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n] b_le_1 [of "2*m+1" n]
                using left_right_m [of "c((2*m + 1) / 2^n)" "a((2*m + 1) / 2^n)" "b((2*m + 1) / 2^n)"]
                by (auto simp: algebra_simps)
            next
              fix x
              assume "a (real j / 2 ^ Suc n) \<le> x" "x < b (real j / 2 ^ Suc n)" "f x = f (b (real j / 2 ^ Suc n))"
              then show False
                using k m \<open>0 < n\<close> a41 [of n m] b41 [of n m] fleft left_neq
                using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n] b_le_1 [of "2*m+1" n]
                by (auto simp: algebra_simps)
            qed
          next
            case False
            with oddE obtain m where m: "k = Suc (2*m)" by fastforce
            have fright: "f (rightcut (a ((2*m + 1) / 2^n)) (b ((2*m + 1) / 2^n)) (c ((2*m + 1) / 2^n))) = f (c((2*m + 1) / 2^n))"
              using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n]  b_le_1 [of "2*m+1" n]
              using left_right_m [of "c((2*m + 1) / 2^n)" "a((2*m + 1) / 2^n)" "b((2*m + 1) / 2^n)"]
              by (auto intro: f_eqI [OF _ order_refl])
            show ?thesis
            proof (intro conjI impI notI allI)
              have False if "b (real j / 2 ^ Suc n) \<le> a (real j / 2 ^ Suc n)"
              proof -
                have "f (c ((1 + real m * 2) / 2 ^ n)) = f (b ((1 + real m * 2) / 2 ^ n))"
                  using k m \<open>0 < n\<close> fright that a43 [of n m] b43 [of n m]
                  using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n]  b_le_1 [of "2*m+1" n]
                  using left_right [of "c((2*m + 1) / 2^n)" "a((2*m + 1) / 2^n)" "b((2*m + 1) / 2^n)"]
                  by (auto simp: algebra_simps)
                moreover have "a (real (1 + m * 2) / 2 ^ n) \<le> c (real (1 + m * 2) / 2 ^ n)"
                  using alec by blast
                moreover have "c (real (1 + m * 2) / 2 ^ n) < b (real (1 + m * 2) / 2 ^ n)"
                  using Suc.IH [of "1 + m * 2"] by (simp add: c_def midpoint_def)
                ultimately show ?thesis
                  using Suc.IH [of "1 + m * 2"] by force
              qed
              then show "a (real j / 2 ^ Suc n) < b (real j / 2 ^ Suc n)" by force
            next
              fix x
              assume "a (real j / 2 ^ Suc n) < x" "x \<le> b (real j / 2 ^ Suc n)" "f x = f (a (real j / 2 ^ Suc n))"
              then show False
                using k m \<open>0 < n\<close> a43 [of n m] b43 [of n m] fright right_neq
                using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n] b_le_1 [of "2*m+1" n]
                by (auto simp: algebra_simps)
            next
              fix x
              assume "a (real j / 2 ^ Suc n) \<le> x" "x < b (real j / 2 ^ Suc n)" "f x = f (b (real j / 2 ^ Suc n))"
              then show False
                using Suc.IH [of "1 + m * 2", THEN conjunct2, THEN conjunct2]
                using k m \<open>0 < n\<close> a43 [of n m] b43 [of n m]
                using alec [of "2*m+1" n] cleb [of "2*m+1" n] a_ge_0 [of "2*m+1" n] b_le_1 [of "2*m+1" n]
                using left_right_m [of "c((2*m + 1) / 2^n)" "a((2*m + 1) / 2^n)" "b((2*m + 1) / 2^n)"]
                by (auto simp: algebra_simps fright simp del: power_Suc)
            qed
          qed
        qed
      qed
    qed
    have c_gt_0 [simp]: "0 < c(m / 2^n)" and c_less_1 [simp]: "c(m / 2^n) < 1" for m::nat and n
      using a_less_b [of m n] apply (simp_all add: c_def midpoint_def)
      using a_ge_0 [of m n] b_le_1 [of m n] by linarith+
    have approx: "\<exists>j n. odd j \<and> n \<noteq> 0 \<and>
                        real i / 2^m \<le> real j / 2^n \<and>
                        real j / 2^n \<le> real k / 2^p \<and>
                        \<bar>real i / 2 ^ m - real j / 2 ^ n\<bar> < 1/2^n \<and>
                        \<bar>real k / 2 ^ p - real j / 2 ^ n\<bar> < 1/2^n"
      if "0 < i" "i < 2 ^ m" "0 < k" "k < 2 ^ p" "i / 2^m < k / 2^p" "m + p = N" for N m p i k
      using that
    proof (induction N arbitrary: m p i k rule: less_induct)
      case (less N)
      then consider "i / 2^m \<le> 1/2" "1/2 \<le> k / 2^p" | "k / 2^p < 1/2" | "k / 2^p \<ge> 1/2" "1/2 < i / 2^m"
        by linarith
      then show ?case
      proof cases
        case 1
        with less.prems show ?thesis
          by (rule_tac x=1 in exI)+ (fastforce simp: field_split_simps)
      next
        case 2 show ?thesis
        proof (cases m)
          case 0 with less.prems show ?thesis
            by auto
        next
          case (Suc m') show ?thesis
          proof (cases p)
            case 0 with less.prems show ?thesis by auto
          next
            case (Suc p')
            have \<section>: False if "real i * 2 ^ p' < real k * 2 ^ m'" "k < 2 ^ p'" "2 ^ m' \<le> i"
            proof -
              have "real k * 2 ^ m' < 2 ^ p' * 2 ^ m'"
                using that by simp
              then have "real i * 2 ^ p' < 2 ^ p' * 2 ^ m'"
                using that by linarith
              with that show ?thesis by simp
            qed
            moreover have *: "real i / 2 ^ m' < real k / 2^p'"  "k < 2 ^ p'"
              using less.prems \<open>m = Suc m'\<close> 2 Suc by (force simp: field_split_simps)+
            moreover have "i < 2 ^ m' "
              using \<section> * by (clarsimp simp: divide_simps linorder_not_le) (meson linorder_not_le)
            ultimately show ?thesis
              using less.IH [of "m'+p'" i m' k p'] less.prems \<open>m = Suc m'\<close> 2 Suc
              by (force simp: field_split_simps)
          qed
        qed
      next
        case 3 show ?thesis
        proof (cases m)
          case 0 with less.prems show ?thesis
            by auto
        next
          case (Suc m') show ?thesis
          proof (cases p)
            case 0 with less.prems show ?thesis by auto
          next
            case (Suc p')
            have "real (i - 2 ^ m') / 2 ^ m' < real (k - 2 ^ p') / 2 ^ p'"
              using less.prems \<open>m = Suc m'\<close> Suc 3  by (auto simp: field_simps of_nat_diff)
            moreover have "k - 2 ^ p' < 2 ^ p'" "i - 2 ^ m' < 2 ^ m'"
              using less.prems Suc \<open>m = Suc m'\<close> by auto
            moreover 
            have "2 ^ p' \<le> k" "2 ^ p' \<noteq> k"
              using less.prems \<open>m = Suc m'\<close> Suc 3 by auto
            then have "2 ^ p' < k"
              by linarith
            ultimately show ?thesis
              using less.IH [of "m'+p'" "i - 2^m'" m' "k - 2 ^ p'" p'] less.prems \<open>m = Suc m'\<close> Suc 3
              apply (clarsimp simp: field_simps of_nat_diff)
              apply (rule_tac x="2 ^ n + j" in exI, simp)
              apply (rule_tac x="Suc n" in exI)
              apply (auto simp: field_simps)
              done
          qed
        qed
      qed
    qed
    have clec: "c(real i / 2^m) \<le> c(real j / 2^n)"
      if i: "0 < i" "i < 2 ^ m" and j: "0 < j" "j < 2 ^ n" and ij: "i / 2^m < j / 2^n" for m i n j
    proof -
      obtain j' n' where "odd j'" "n' \<noteq> 0"
        and i_le_j: "real i / 2 ^ m \<le> real j' / 2 ^ n'"
        and j_le_j: "real j' / 2 ^ n' \<le> real j / 2 ^ n"
        and clo_ij: "\<bar>real i / 2 ^ m - real j' / 2 ^ n'\<bar> < 1/2 ^ n'"
        and clo_jj: "\<bar>real j / 2 ^ n - real j' / 2 ^ n'\<bar> < 1/2 ^ n'"
        using approx [of i m j n "m+n"] that i j ij by auto
      with oddE obtain q where q: "j' = Suc (2*q)" by fastforce
      have "c (real i / 2 ^ m) \<le> c((2*q + 1) / 2^n')"
      proof (cases "i / 2^m = (2*q + 1) / 2^n'")
        case True then show ?thesis by simp
      next
        case False
        with i_le_j clo_ij q have "\<bar>real i / 2 ^ m - real (4 * q + 1) / 2 ^ Suc n'\<bar> < 1 / 2 ^ Suc n'"
          by (auto simp: field_split_simps)
        then have "c(i / 2^m) \<le> b(real(4 * q + 1) / 2 ^ (Suc n'))"
          by (meson ci_le_bj even_mult_iff even_numeral even_plus_one_iff)
        then show ?thesis
          using alec [of "2*q+1" n'] cleb [of "2*q+1" n'] a_ge_0 [of "2*q+1" n'] b_le_1 [of "2*q+1" n'] b41 [of n' q] \<open>n' \<noteq> 0\<close>
          using left_right_m [of "c((2*q + 1) / 2^n')" "a((2*q + 1) / 2^n')" "b((2*q + 1) / 2^n')"]
          by (auto simp: algebra_simps)
      qed
      also have "... \<le> c(real j / 2^n)"
      proof (cases "j / 2^n = (2*q + 1) / 2^n'")
        case True
        then show ?thesis by simp
      next
        case False
        with j_le_j q have less: "(2*q + 1) / 2^n' < j / 2^n"
          by auto
        have *: "\<lbrakk>q < i; abs(i - q) < s*2; r = q + s\<rbrakk> \<Longrightarrow> abs(i - r) < s" for i q s r::real
          by auto
        have "\<bar>real j / 2 ^ n - real (4 * q + 3) / 2 ^ Suc n'\<bar> < 1 / 2 ^ Suc n'"
          by (rule * [OF less]) (use j_le_j clo_jj q  in \<open>auto simp: field_split_simps\<close>)
        then have "a(real(4*q + 3) / 2 ^ (Suc n')) \<le> c(j / 2^n)"
          by (metis Suc3_eq_add_3 add.commute aj_le_ci even_Suc even_mult_iff even_numeral)
        then show ?thesis
          using alec [of "2*q+1" n'] cleb [of "2*q+1" n'] a_ge_0 [of "2*q+1" n'] b_le_1 [of "2*q+1" n'] a43 [of n' q] \<open>n' \<noteq> 0\<close>
          using left_right_m [of "c((2*q + 1) / 2^n')" "a((2*q + 1) / 2^n')" "b((2*q + 1) / 2^n')"]
          by (auto simp: algebra_simps)
      qed
      finally show ?thesis .
    qed
    have "x = y" if "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" "h x = h y" for x y
      using that
    proof (induction x y rule: linorder_class.linorder_less_wlog)
      case (less x1 x2)
      obtain m n where m: "0 < m" "m < 2 ^ n"
        and x12: "x1 < m / 2^n" "m / 2^n < x2"
        and neq: "h x1 \<noteq> h (real m / 2^n)"
      proof -
        have "(x1 + x2) / 2 \<in> closure D01"
          using cloD01 less.hyps less.prems by auto
        with less obtain y where "y \<in> D01" and dist_y: "dist y ((x1 + x2) / 2) < (x2 - x1) / 64"
          unfolding closure_approachable
          by (metis diff_gt_0_iff_gt less_divide_eq_numeral1(1) mult_zero_left)
        obtain m n where m: "0 < m" "m < 2 ^ n"
                     and clo: "\<bar>real m / 2 ^ n - (x1 + x2) / 2\<bar> < (x2 - x1) / 64"
                     and n: "1/2^n < (x2 - x1) / 128"
        proof -
          have "min 1 ((x2 - x1) / 128) > 0" "1/2 < (1::real)"
            using less by auto
          then obtain N where N: "1/2^N < min 1 ((x2 - x1) / 128)"
            by (metis power_one_over real_arch_pow_inv)
          then have "N > 0"
            using less_divide_eq_1 by force
          obtain p q where p: "p < 2 ^ q" "p \<noteq> 0" and yeq: "y = real p / 2 ^ q"
            using \<open>y \<in> D01\<close> by (auto simp: zero_less_divide_iff D01_def)
          show ?thesis
          proof
            show "0 < 2^N * p"
              using p by auto
            show "2 ^ N * p < 2 ^ (N+q)"
              by (simp add: p power_add)
            have "\<bar>real (2 ^ N * p) / 2 ^ (N + q) - (x1 + x2) / 2\<bar> = \<bar>real p / 2 ^ q - (x1 + x2) / 2\<bar>"
              by (simp add: power_add)
            also have "... = \<bar>y - (x1 + x2) / 2\<bar>"
              by (simp add: yeq)
            also have "... < (x2 - x1) / 64"
              using dist_y by (simp add: dist_norm)
            finally show "\<bar>real (2 ^ N * p) / 2 ^ (N + q) - (x1 + x2) / 2\<bar> < (x2 - x1) / 64" .
            have "(1::real) / 2 ^ (N + q) \<le> 1/2^N"
              by (simp add: field_simps)
            also have "... < (x2 - x1) / 128"
              using N by force
            finally show "1/2 ^ (N + q) < (x2 - x1) / 128" .
          qed
        qed
        obtain m' n' m'' n'' where "0 < m'" "m' < 2 ^ n'" "x1 < m' / 2^n'" "m' / 2^n' < x2"
          and "0 < m''" "m'' < 2 ^ n''" "x1 < m'' / 2^n''" "m'' / 2^n'' < x2"
          and neq: "h (real m'' / 2^n'') \<noteq> h (real m' / 2^n')"
        proof
          show "0 < Suc (2*m)"
            by simp
          show m21: "Suc (2*m) < 2 ^ Suc n"
            using m by auto
          show "x1 < real (Suc (2 * m)) / 2 ^ Suc n"
            using clo by (simp add: field_simps abs_if split: if_split_asm)
          show "real (Suc (2 * m)) / 2 ^ Suc n < x2"
            using n clo by (simp add: field_simps abs_if split: if_split_asm)
          show "0 < 4*m + 3"
            by simp
          have "m+1 \<le> 2 ^ n"
            using m by simp
          then have "4 * (m+1) \<le> 4 * (2 ^ n)"
            by simp
          then show m43: "4*m + 3 < 2 ^ (n+2)"
            by (simp add: algebra_simps)
          show "x1 < real (4 * m + 3) / 2 ^ (n + 2)"
            using clo by (simp add: field_simps abs_if split: if_split_asm)
          show "real (4 * m + 3) / 2 ^ (n + 2) < x2"
            using n clo by (simp add: field_simps abs_if split: if_split_asm)
          have c_fold: "midpoint (a ((2 * real m + 1) / 2 ^ Suc n)) (b ((2 * real m + 1) / 2 ^ Suc n)) = c ((2 * real m + 1) / 2 ^ Suc n)"
            by (simp add: c_def)
          define R where "R \<equiv> rightcut (a ((2 * real m + 1) / 2 ^ Suc n)) (b ((2 * real m + 1) / 2 ^ Suc n))  (c ((2 * real m + 1) / 2 ^ Suc n))"
          have "R < b ((2 * real m + 1) / 2 ^ Suc n)"
            unfolding R_def  using a_less_b [of "4*m + 3" "n+2"] a43 [of "Suc n" m] b43 [of "Suc n" m]
            by simp
          then have Rless: "R < midpoint R (b ((2 * real m + 1) / 2 ^ Suc n))"
            by (simp add: midpoint_def)
          have midR_le: "midpoint R (b ((2 * real m + 1) / 2 ^ Suc n)) \<le> b ((2 * real m + 1) / (2 * 2 ^ n))"
            using \<open>R < b ((2 * real m + 1) / 2 ^ Suc n)\<close>
            by (simp add: midpoint_def)
          have "(real (Suc (2 * m)) / 2 ^ Suc n) \<in> D01"  "real (4 * m + 3) / 2 ^ (n + 2) \<in> D01"
            by (simp_all add: D01_def m21 m43 del: power_Suc of_nat_Suc of_nat_add add_2_eq_Suc') blast+
          then show "h (real (4 * m + 3) / 2 ^ (n + 2)) \<noteq> h (real (Suc (2 * m)) / 2 ^ Suc n)"
            using a_less_b [of "4*m + 3" "n+2", THEN conjunct1]
            using a43 [of "Suc n" m] b43 [of "Suc n" m]
            using alec [of "2*m+1" "Suc n"] cleb [of "2*m+1" "Suc n"] a_ge_0 [of "2*m+1" "Suc n"]  b_le_1 [of "2*m+1" "Suc n"]
            apply (simp add: fc_eq [symmetric] c_def del: power_Suc)
            apply (simp only: add.commute [of 1] c_fold R_def [symmetric])
            apply (rule right_neq)
            using Rless apply (simp add: R_def)
               apply (rule midR_le, auto)
            done
        qed
        then show ?thesis by (metis that)
      qed
      have m_div: "0 < m / 2^n" "m / 2^n < 1"
        using m  by (auto simp: field_split_simps)
      have closure0m: "{0..m / 2^n} = closure ({0<..< m / 2^n} \<inter> (\<Union>k m. {real m / 2 ^ k}))"
        by (subst closure_dyadic_rationals_in_convex_set_pos_1, simp_all add: not_le m)
      have "2^n > m"
        by (simp add: m(2) not_le)
      then have closurem1: "{m / 2^n .. 1} = closure ({m / 2^n <..< 1} \<inter> (\<Union>k m. {real m / 2 ^ k}))"
        using closure_dyadic_rationals_in_convex_set_pos_1 m_div(1) by fastforce
      have cont_h': "continuous_on (closure ({u<..<v} \<inter> (\<Union>k m. {real m / 2 ^ k}))) h"
        if "0 \<le> u" "v \<le> 1" for u v
        using that by (intro continuous_on_subset [OF cont_h] closure_minimal [OF subsetI]) auto
      have closed_f': "closed (f ` {u..v})" if "0 \<le> u" "v \<le> 1" for u v
        by (metis compact_continuous_image cont_f compact_interval atLeastatMost_subset_iff
            compact_imp_closed continuous_on_subset that)
      have less_2I: "\<And>k i. real i / 2 ^ k < 1 \<Longrightarrow> i < 2 ^ k"
        by simp
      have "h ` ({0<..<m / 2 ^ n} \<inter> (\<Union>q p. {real p / 2 ^ q})) \<subseteq> f ` {0..c (m / 2 ^ n)}"
      proof clarsimp
        fix p q
        assume p: "0 < real p / 2 ^ q" "real p / 2 ^ q < real m / 2 ^ n"
        then have [simp]: "0 < p"
          by (simp add: field_split_simps)
        have [simp]: "p < 2 ^ q"
          by (blast intro: p less_2I m_div less_trans)
        have "f (c (real p / 2 ^ q)) \<in> f ` {0..c (real m / 2 ^ n)}"
          by (auto simp: clec p m)
        then show "h (real p / 2 ^ q) \<in> f ` {0..c (real m / 2 ^ n)}"
          by (simp add: h_eq)
      qed
      with m_div have "h ` {0 .. m / 2^n} \<subseteq> f ` {0 .. c(m / 2^n)}"
        apply (subst closure0m)
        by (rule image_closure_subset [OF cont_h' closed_f']) auto
      then have hx1: "h x1 \<in> f ` {0 .. c(m / 2^n)}"
        using x12 less.prems(1) by auto
      then obtain t1 where t1: "h x1 = f t1" "0 \<le> t1" "t1 \<le> c (m / 2 ^ n)"
        by auto
      have "h ` ({m / 2 ^ n<..<1} \<inter> (\<Union>q p. {real p / 2 ^ q})) \<subseteq> f ` {c (m / 2 ^ n)..1}"
      proof clarsimp
        fix p q
        assume p: "real m / 2 ^ n < real p / 2 ^ q" and [simp]: "p < 2 ^ q"
        then have [simp]: "0 < p"
          using gr_zeroI m_div by fastforce
        have "f (c (real p / 2 ^ q)) \<in> f ` {c (m / 2 ^ n)..1}"
          by (auto simp: clec p m)
        then show "h (real p / 2 ^ q) \<in> f ` {c (real m / 2 ^ n)..1}"
          by (simp add: h_eq)
      qed
      with m have "h ` {m / 2^n .. 1} \<subseteq> f ` {c(m / 2^n) .. 1}"
        apply (subst closurem1)
        by (rule image_closure_subset [OF cont_h' closed_f']) auto
      then have hx2: "h x2 \<in> f ` {c(m / 2^n)..1}"
        using x12 less.prems by auto
      then obtain t2 where t2: "h x2 = f t2" "c (m / 2 ^ n) \<le> t2" "t2 \<le> 1"
        by auto
      with t1 less neq have False
        using conn [of "h x2", unfolded is_interval_connected_1 [symmetric] is_interval_1, rule_format, of t1 t2 "c(m / 2^n)"]
        by (simp add: h_eq m)
      then show ?case by blast
    qed auto
    then show ?thesis
      by (auto simp: inj_on_def)
  qed
  ultimately have "{0..1::real} homeomorphic f ` {0..1}"
    using homeomorphic_compact [OF _ cont_h] by blast
  then show ?thesis
    using homeomorphic_sym by blast
qed


theorem path_contains_arc:
  fixes p :: "real \<Rightarrow> 'a::{complete_space,real_normed_vector}"
  assumes "path p" and a: "pathstart p = a" and b: "pathfinish p = b" and "a \<noteq> b"
  obtains q where "arc q" "path_image q \<subseteq> path_image p" "pathstart q = a" "pathfinish q = b"
proof -
  have ucont_p: "uniformly_continuous_on {0..1} p"
    using \<open>path p\<close> unfolding path_def
    by (metis compact_Icc compact_uniformly_continuous)
  define \<phi> where "\<phi> \<equiv> \<lambda>S. S \<subseteq> {0..1} \<and> 0 \<in> S \<and> 1 \<in> S \<and>
                           (\<forall>x \<in> S. \<forall>y \<in> S. open_segment x y \<inter> S = {} \<longrightarrow> p x = p y)"
  obtain T where "closed T" "\<phi> T" and T: "\<And>U. \<lbrakk>closed U; \<phi> U\<rbrakk> \<Longrightarrow> \<not> (U \<subset> T)"
  proof (rule Brouwer_reduction_theorem_gen [of "{0..1}" \<phi>])
    have *: "{x<..<y} \<inter> {0..1} = {x<..<y}" if "0 \<le> x" "y \<le> 1" "x \<le> y" for x y::real
      using that by auto
    show "\<phi> {0..1}"
      by (auto simp: \<phi>_def open_segment_eq_real_ivl *)
    show "\<phi> (\<Inter>(F ` UNIV))"
      if "\<And>n. closed (F n)" and \<phi>: "\<And>n. \<phi> (F n)" and Fsub: "\<And>n. F (Suc n) \<subseteq> F n" for F
    proof -
      have F01: "\<And>n. F n \<subseteq> {0..1} \<and> 0 \<in> F n \<and> 1 \<in> F n"
        and peq: "\<And>n x y. \<lbrakk>x \<in> F n; y \<in> F n; open_segment x y \<inter> F n = {}\<rbrakk> \<Longrightarrow> p x = p y"
        by (metis \<phi> \<phi>_def)+
      have pqF: False if "\<forall>u. x \<in> F u" "\<forall>x. y \<in> F x" "open_segment x y \<inter> (\<Inter>x. F x) = {}" and neg: "p x \<noteq> p y"
        for x y
        using that
      proof (induction x y rule: linorder_class.linorder_less_wlog)
        case (less x y)
        have xy: "x \<in> {0..1}" "y \<in> {0..1}"
          by (metis less.prems subsetCE F01)+
        have "norm(p x - p y) / 2 > 0"
          using less by auto
        then obtain e where "e > 0"
          and e: "\<And>u v. \<lbrakk>u \<in> {0..1}; v \<in> {0..1}; dist v u < e\<rbrakk> \<Longrightarrow> dist (p v) (p u) < norm(p x - p y) / 2"
          by (metis uniformly_continuous_onE [OF ucont_p])
        have minxy: "min e (y - x)  < (y - x) * (3 / 2)"
          by (subst min_less_iff_disj) (simp add: less)
        define w where "w \<equiv> x + (min e (y - x) / 3)" 
        define z where "z \<equiv>y - (min e (y - x) / 3)"
        have "w < z" and w: "w \<in> {x<..<y}" and z: "z \<in> {x<..<y}"
          and wxe: "norm(w - x) < e" and zye: "norm(z - y) < e"
          using minxy \<open>0 < e\<close> less unfolding w_def z_def by auto
        have Fclo: "\<And>T. T \<in> range F \<Longrightarrow> closed T"
          by (metis \<open>\<And>n. closed (F n)\<close> image_iff)
        have eq: "{w..z} \<inter> \<Inter>(F ` UNIV) = {}"
          using less w z by (simp add: open_segment_eq_real_ivl disjoint_iff)
        then obtain K where "finite K" and K: "{w..z} \<inter> (\<Inter> (F ` K)) = {}"
          by (metis finite_subset_image compact_imp_fip [OF compact_interval Fclo])
        then have "K \<noteq> {}"
          using \<open>w < z\<close> \<open>{w..z} \<inter> \<Inter>(F ` K) = {}\<close> by auto
        define n where "n \<equiv> Max K"
        have "n \<in> K" unfolding n_def by (metis \<open>K \<noteq> {}\<close> \<open>finite K\<close> Max_in)
        have "F n \<subseteq> \<Inter> (F ` K)"
          unfolding n_def by (metis Fsub Max_ge \<open>K \<noteq> {}\<close> \<open>finite K\<close> cINF_greatest lift_Suc_antimono_le)
        with K have wzF_null: "{w..z} \<inter> F n = {}"
          by (metis disjoint_iff_not_equal subset_eq)
        obtain u where u: "u \<in> F n" "u \<in> {x..w}" "({u..w} - {u}) \<inter> F n = {}"
        proof (cases "w \<in> F n")
          case True
          then show ?thesis
            by (metis wzF_null \<open>w < z\<close> atLeastAtMost_iff disjoint_iff_not_equal less_eq_real_def)
        next
          case False
          obtain u where "u \<in> F n" "u \<in> {x..w}" "{u<..<w} \<inter> F n = {}"
          proof (rule segment_to_point_exists [of "F n \<inter> {x..w}" w])
            show "closed (F n \<inter> {x..w})"
              by (metis \<open>\<And>n. closed (F n)\<close> closed_Int closed_real_atLeastAtMost)
            show "F n \<inter> {x..w} \<noteq> {}"
              by (metis atLeastAtMost_iff disjoint_iff_not_equal greaterThanLessThan_iff less.prems(1) less_eq_real_def w)
          qed (auto simp: open_segment_eq_real_ivl intro!: that)
          with False show thesis
            by (auto simp add: disjoint_iff less_eq_real_def intro!: that)
        qed
        obtain v where v: "v \<in> F n" "v \<in> {z..y}" "({z..v} - {v}) \<inter> F n = {}"
        proof (cases "z \<in> F n")
          case True
          have "z \<in> {w..z}"
            using \<open>w < z\<close> by auto
          then show ?thesis
            by (metis wzF_null Int_iff True empty_iff)
        next
          case False
          show ?thesis
          proof (rule segment_to_point_exists [of "F n \<inter> {z..y}" z])
            show "closed (F n \<inter> {z..y})"
              by (metis \<open>\<And>n. closed (F n)\<close> closed_Int closed_atLeastAtMost)
            show "F n \<inter> {z..y} \<noteq> {}"
              by (metis atLeastAtMost_iff disjoint_iff_not_equal greaterThanLessThan_iff less.prems(2) less_eq_real_def z)
            show "\<And>b. \<lbrakk>b \<in> F n \<inter> {z..y}; open_segment z b \<inter> (F n \<inter> {z..y}) = {}\<rbrakk> \<Longrightarrow> thesis"
            proof
              show "\<And>b. \<lbrakk>b \<in> F n \<inter> {z..y}; open_segment z b \<inter> (F n \<inter> {z..y}) = {}\<rbrakk> \<Longrightarrow> ({z..b} - {b}) \<inter> F n = {}"
                using False by (auto simp: open_segment_eq_real_ivl less_eq_real_def)
            qed auto
          qed
        qed
        obtain u v where "u \<in> {0..1}" "v \<in> {0..1}" "norm(u - x) < e" "norm(v - y) < e" "p u = p v"
        proof
          show "u \<in> {0..1}" "v \<in> {0..1}"
            by (metis F01 \<open>u \<in> F n\<close> \<open>v \<in> F n\<close> subsetD)+
          show "norm(u - x) < e" "norm (v - y) < e"
            using \<open>u \<in> {x..w}\<close> \<open>v \<in> {z..y}\<close> atLeastAtMost_iff real_norm_def wxe zye by auto
          show "p u = p v"
          proof (rule peq)
            show "u \<in> F n" "v \<in> F n"
              by (auto simp: u v)
            have "False" if "\<xi> \<in> F n" "u < \<xi>" "\<xi> < v" for \<xi>
            proof -
              have "\<xi> \<notin> {z..v}"
                by (metis DiffI disjoint_iff_not_equal less_irrefl singletonD that(1,3) v(3))
              moreover have "\<xi> \<notin> {w..z} \<inter> F n"
                by (metis equals0D wzF_null)
              ultimately have "\<xi> \<in> {u..w}"
                using that by auto
              then show ?thesis
                by (metis DiffI disjoint_iff_not_equal less_eq_real_def not_le singletonD that(1,2) u(3))
            qed
            moreover
            have "\<lbrakk>\<xi> \<in> F n; v < \<xi>; \<xi> < u\<rbrakk> \<Longrightarrow> False" for \<xi>
              using \<open>u \<in> {x..w}\<close> \<open>v \<in> {z..y}\<close> \<open>w < z\<close> by simp
            ultimately
            show "open_segment u v \<inter> F n = {}"
              by (force simp: open_segment_eq_real_ivl)
          qed
        qed
        then show ?case
          using e [of x u] e [of y v] xy
          by (metis dist_norm dist_triangle_half_r order_less_irrefl)
      qed (auto simp: open_segment_commute)
      show ?thesis
        unfolding \<phi>_def by (metis (no_types, hide_lams) INT_I Inf_lower2 rangeI that(3) F01 subsetCE pqF)
    qed
    show "closed {0..1::real}" by auto
  qed (meson \<phi>_def)
  then have "T \<subseteq> {0..1}" "0 \<in> T" "1 \<in> T"
    and peq: "\<And>x y. \<lbrakk>x \<in> T; y \<in> T; open_segment x y \<inter> T = {}\<rbrakk> \<Longrightarrow> p x = p y"
    unfolding \<phi>_def by metis+
  then have "T \<noteq> {}" by auto
  define h where "h \<equiv> \<lambda>x. p(SOME y. y \<in> T \<and> open_segment x y \<inter> T = {})"
  have "p y = p z" if "y \<in> T" "z \<in> T" and xyT: "open_segment x y \<inter> T = {}" and xzT: "open_segment x z \<inter> T = {}"
    for x y z
  proof (cases "x \<in> T")
    case True
    with that show ?thesis by (metis \<open>\<phi> T\<close> \<phi>_def)
  next
    case False
    have "insert x (open_segment x y \<union> open_segment x z) \<inter> T = {}"
      by (metis False Int_Un_distrib2 Int_insert_left Un_empty_right xyT xzT)
    moreover have "open_segment y z \<inter> T \<subseteq> insert x (open_segment x y \<union> open_segment x z) \<inter> T"
      by (auto simp: open_segment_eq_real_ivl)
    ultimately have "open_segment y z \<inter> T = {}"
      by blast
    with that peq show ?thesis by metis
  qed
  then have h_eq_p_gen: "h x = p y" if "y \<in> T" "open_segment x y \<inter> T = {}" for x y
    using that unfolding h_def
    by (metis (mono_tags, lifting) some_eq_ex)
  then have h_eq_p: "\<And>x. x \<in> T \<Longrightarrow> h x = p x"
    by simp
  have disjoint: "\<And>x. \<exists>y. y \<in> T \<and> open_segment x y \<inter> T = {}"
    by (meson \<open>T \<noteq> {}\<close> \<open>closed T\<close> segment_to_point_exists)
  have heq: "h x = h x'" if "open_segment x x' \<inter> T = {}" for x x'
  proof (cases "x \<in> T \<or> x' \<in> T")
    case True
    then show ?thesis
      by (metis h_eq_p h_eq_p_gen open_segment_commute that)
  next
    case False
    obtain y y' where "y \<in> T" "open_segment x y \<inter> T = {}" "h x = p y"
      "y' \<in> T" "open_segment x' y' \<inter> T = {}" "h x' = p y'"
      by (meson disjoint h_eq_p_gen)
    moreover have "open_segment y y' \<subseteq> (insert x (insert x' (open_segment x y \<union> open_segment x' y' \<union> open_segment x x')))"
      by (auto simp: open_segment_eq_real_ivl)
    ultimately show ?thesis
      using False that by (fastforce simp add: h_eq_p intro!: peq)
  qed
  have "h ` {0..1} homeomorphic {0..1::real}"
  proof (rule homeomorphic_monotone_image_interval)
    show "continuous_on {0..1} h"
    proof (clarsimp simp add: continuous_on_iff)
      fix u \<epsilon>::real
      assume "0 < \<epsilon>" "0 \<le> u" "u \<le> 1"
      then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>v. v \<in> {0..1} \<Longrightarrow> dist v u < \<delta> \<longrightarrow> dist (p v) (p u) < \<epsilon> / 2"
        using ucont_p [unfolded uniformly_continuous_on_def]
        by (metis atLeastAtMost_iff half_gt_zero_iff)
      then have "dist (h v) (h u) < \<epsilon>" if "v \<in> {0..1}" "dist v u < \<delta>" for v
      proof (cases "open_segment u v \<inter> T = {}")
        case True
        then show ?thesis
          using \<open>0 < \<epsilon>\<close> heq by auto
      next
        case False
        have uvT: "closed (closed_segment u v \<inter> T)" "closed_segment u v \<inter> T \<noteq> {}"
          using False open_closed_segment by (auto simp: \<open>closed T\<close> closed_Int)
        obtain w where "w \<in> T" and w: "w \<in> closed_segment u v" "open_segment u w \<inter> T = {}"
        proof (rule segment_to_point_exists [OF uvT])
          fix b
          assume "b \<in> closed_segment u v \<inter> T" "open_segment u b \<inter> (closed_segment u v \<inter> T) = {}"
          then show thesis
            by (metis IntD1 IntD2 ends_in_segment(1) inf.orderE inf_assoc subset_oc_segment that)
        qed
        then have puw: "dist (p u) (p w) < \<epsilon> / 2"
          by (metis (no_types) \<open>T \<subseteq> {0..1}\<close> \<open>dist v u < \<delta>\<close> \<delta> dist_commute dist_in_closed_segment le_less_trans subsetCE)
        obtain z where "z \<in> T" and z: "z \<in> closed_segment u v" "open_segment v z \<inter> T = {}"
        proof (rule segment_to_point_exists [OF uvT])
          fix b
          assume "b \<in> closed_segment u v \<inter> T" "open_segment v b \<inter> (closed_segment u v \<inter> T) = {}"
          then show thesis
            by (metis IntD1 IntD2 ends_in_segment(2) inf.orderE inf_assoc subset_oc_segment that)
        qed
        then have "dist (p u) (p z) < \<epsilon> / 2"
          by (metis \<open>T \<subseteq> {0..1}\<close> \<open>dist v u < \<delta>\<close> \<delta> dist_commute dist_in_closed_segment le_less_trans subsetCE)
        then show ?thesis
          using puw by (metis (no_types) \<open>w \<in> T\<close> \<open>z \<in> T\<close> dist_commute dist_triangle_half_l h_eq_p_gen w(2) z(2))
      qed
      with \<open>0 < \<delta>\<close> show "\<exists>\<delta>>0. \<forall>v\<in>{0..1}. dist v u < \<delta> \<longrightarrow> dist (h v) (h u) < \<epsilon>" by blast
    qed
    show "connected ({0..1} \<inter> h -` {z})" for z
    proof (clarsimp simp add: connected_iff_connected_component)
      fix u v
      assume huv_eq: "h v = h u" and uv: "0 \<le> u" "u \<le> 1" "0 \<le> v" "v \<le> 1"
      have "\<exists>T. connected T \<and> T \<subseteq> {0..1} \<and> T \<subseteq> h -` {h u} \<and> u \<in> T \<and> v \<in> T"
      proof (intro exI conjI)
        show "connected (closed_segment u v)"
          by simp
        show "closed_segment u v \<subseteq> {0..1}"
          by (simp add: uv closed_segment_eq_real_ivl)
        have pxy: "p x = p y"
          if "T \<subseteq> {0..1}" "0 \<in> T" "1 \<in> T" "x \<in> T" "y \<in> T"
          and disjT: "open_segment x y \<inter> (T - open_segment u v) = {}"
          and xynot: "x \<notin> open_segment u v" "y \<notin> open_segment u v"
          for x y
        proof (cases "open_segment x y \<inter> open_segment u v = {}")
          case True
          then show ?thesis
            by (metis Diff_Int_distrib Diff_empty peq disjT \<open>x \<in> T\<close> \<open>y \<in> T\<close>)
        next
          case False
          then have "open_segment x u \<union> open_segment y v \<subseteq> open_segment x y - open_segment u v \<or>
                     open_segment y u \<union> open_segment x v \<subseteq> open_segment x y - open_segment u v" (is "?xuyv \<or> ?yuxv")
            using xynot by (fastforce simp add: open_segment_eq_real_ivl not_le not_less split: if_split_asm)
          then show "p x = p y"
          proof
            assume "?xuyv"
            then have "open_segment x u \<inter> T = {}" "open_segment y v \<inter> T = {}"
              using disjT by auto
            then have "h x = h y"
              using heq huv_eq by auto
            then show ?thesis
              using h_eq_p \<open>x \<in> T\<close> \<open>y \<in> T\<close> by auto
          next
            assume "?yuxv"
            then have "open_segment y u \<inter> T = {}" "open_segment x v \<inter> T = {}"
              using disjT by auto
            then have "h x = h y"
              using heq [of y u]  heq [of x v] huv_eq by auto
            then show ?thesis
              using h_eq_p \<open>x \<in> T\<close> \<open>y \<in> T\<close> by auto
          qed
        qed
        have "\<not> T - open_segment u v \<subset> T"
        proof (rule T)
          show "closed (T - open_segment u v)"
            by (simp add: closed_Diff [OF \<open>closed T\<close>] open_segment_eq_real_ivl)
          have "0 \<notin> open_segment u v" "1 \<notin> open_segment u v"
            using open_segment_eq_real_ivl uv by auto
          then show "\<phi> (T - open_segment u v)"
            using \<open>T \<subseteq> {0..1}\<close> \<open>0 \<in> T\<close> \<open>1 \<in> T\<close>
            by (auto simp: \<phi>_def) (meson peq pxy)
        qed
        then have "open_segment u v \<inter> T = {}"
          by blast
        then show "closed_segment u v \<subseteq> h -` {h u}"
          by (force intro: heq simp: open_segment_eq_real_ivl closed_segment_eq_real_ivl split: if_split_asm)+
      qed auto
      then show "connected_component ({0..1} \<inter> h -` {h u}) u v"
        by (simp add: connected_component_def)
    qed
    show "h 1 \<noteq> h 0"
      by (metis \<open>\<phi> T\<close> \<phi>_def a \<open>a \<noteq> b\<close> b h_eq_p pathfinish_def pathstart_def)
  qed
  then obtain f and g :: "real \<Rightarrow> 'a"
    where gfeq: "(\<forall>x\<in>h ` {0..1}. (g(f x) = x))" and fhim: "f ` h ` {0..1} = {0..1}" and contf: "continuous_on (h ` {0..1}) f"
      and fgeq: "(\<forall>y\<in>{0..1}. (f(g y) = y))" and pag: "path_image g = h ` {0..1}" and contg: "continuous_on {0..1} g"
    by (auto simp: homeomorphic_def homeomorphism_def path_image_def)
  then have "arc g"
    by (metis arc_def path_def inj_on_def)
  obtain u v where "u \<in> {0..1}" "a = g u" "v \<in> {0..1}" "b = g v"
    by (metis (mono_tags, hide_lams) \<open>\<phi> T\<close> \<phi>_def a b fhim gfeq h_eq_p imageI path_image_def pathfinish_def pathfinish_in_path_image pathstart_def pathstart_in_path_image)
  then have "a \<in> path_image g" "b \<in> path_image g"
    using path_image_def by blast+
  have ph: "path_image h \<subseteq> path_image p"
    by (metis image_mono image_subset_iff path_image_def disjoint h_eq_p_gen \<open>T \<subseteq> {0..1}\<close>)
  show ?thesis
  proof
    show "pathstart (subpath u v g) = a" "pathfinish (subpath u v g) = b"
      by (simp_all add: \<open>a = g u\<close> \<open>b = g v\<close>)
    show "path_image (subpath u v g) \<subseteq> path_image p"
      by (metis \<open>u \<in> {0..1}\<close> \<open>v \<in> {0..1}\<close> order_trans pag path_image_def path_image_subpath_subset ph)
    show "arc (subpath u v g)"
      using \<open>arc g\<close> \<open>a = g u\<close> \<open>b = g v\<close> \<open>u \<in> {0..1}\<close> \<open>v \<in> {0..1}\<close> arc_subpath_arc \<open>a \<noteq> b\<close> by blast
  qed
qed


corollary path_connected_arcwise:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  shows "path_connected S \<longleftrightarrow>
         (\<forall>x \<in> S. \<forall>y \<in> S. x \<noteq> y \<longrightarrow> (\<exists>g. arc g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y))"
        (is "?lhs = ?rhs")
proof (intro iffI impI ballI)
  fix x y
  assume "path_connected S" "x \<in> S" "y \<in> S" "x \<noteq> y"
  then obtain p where p: "path p" "path_image p \<subseteq> S" "pathstart p = x" "pathfinish p = y"
    by (force simp: path_connected_def)
  then show "\<exists>g. arc g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y"
    by (metis \<open>x \<noteq> y\<close> order_trans path_contains_arc)
next
  assume R [rule_format]: ?rhs
  show ?lhs
    unfolding path_connected_def
  proof (intro ballI)
    fix x y
    assume "x \<in> S" "y \<in> S"
    show "\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y"
    proof (cases "x = y")
      case True with \<open>x \<in> S\<close> path_component_def path_component_refl show ?thesis
        by blast
    next
      case False with R [OF \<open>x \<in> S\<close> \<open>y \<in> S\<close>] show ?thesis
        by (auto intro: arc_imp_path)
    qed
  qed
qed


corollary arc_connected_trans:
  fixes g :: "real \<Rightarrow> 'a::{complete_space,real_normed_vector}"
  assumes "arc g" "arc h" "pathfinish g = pathstart h" "pathstart g \<noteq> pathfinish h"
  obtains i where "arc i" "path_image i \<subseteq> path_image g \<union> path_image h"
                  "pathstart i = pathstart g" "pathfinish i = pathfinish h"
  by (metis (no_types, hide_lams) arc_imp_path assms path_contains_arc path_image_join path_join pathfinish_join pathstart_join)




subsection\<open>Accessibility of frontier points\<close>

lemma dense_accessible_frontier_points:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes "open S" and opeSV: "openin (top_of_set (frontier S)) V" and "V \<noteq> {}"
  obtains g where "arc g" "g ` {0..<1} \<subseteq> S" "pathstart g \<in> S" "pathfinish g \<in> V"
proof -
  obtain z where "z \<in> V"
    using \<open>V \<noteq> {}\<close> by auto
  then obtain r where "r > 0" and r: "ball z r \<inter> frontier S \<subseteq> V"
    by (metis openin_contains_ball opeSV)
  then have "z \<in> frontier S"
    using \<open>z \<in> V\<close> opeSV openin_contains_ball by blast
  then have "z \<in> closure S" "z \<notin> S"
    by (simp_all add: frontier_def assms interior_open)
  with \<open>r > 0\<close> have "infinite (S \<inter> ball z r)"
    by (auto simp: closure_def islimpt_eq_infinite_ball)
  then obtain y where "y \<in> S" and y: "y \<in> ball z r"
    using infinite_imp_nonempty by force
  then have "y \<notin> frontier S"
    by (meson \<open>open S\<close> disjoint_iff_not_equal frontier_disjoint_eq)
  have "y \<noteq> z"
    using \<open>y \<in> S\<close> \<open>z \<notin> S\<close> by blast
  have "path_connected(ball z r)"
    by (simp add: convex_imp_path_connected)
  with y \<open>r > 0\<close>  obtain g where "arc g" and pig: "path_image g \<subseteq> ball z r"
                                 and g: "pathstart g = y" "pathfinish g = z"
    using \<open>y \<noteq> z\<close> by (force simp: path_connected_arcwise)
  have "continuous_on {0..1} g"
    using \<open>arc g\<close> arc_imp_path path_def by blast
  then have "compact (g -` frontier S \<inter> {0..1})"
    by (simp add: bounded_Int closed_Diff closed_vimage_Int compact_eq_bounded_closed)
  moreover have "g -` frontier S \<inter> {0..1} \<noteq> {}"
  proof -
    have "\<exists>r. r \<in> g -` frontier S \<and> r \<in> {0..1}"
      by (metis \<open>z \<in> frontier S\<close> g(2) imageE path_image_def pathfinish_in_path_image vimageI2)
    then show ?thesis
      by blast
  qed
  ultimately obtain t where gt: "g t \<in> frontier S" and "0 \<le> t" "t \<le> 1"
                and t: "\<And>u. \<lbrakk>g u \<in> frontier S; 0 \<le> u; u \<le> 1\<rbrakk> \<Longrightarrow> t \<le> u"
    by (force simp: dest!: compact_attains_inf)
  moreover have "t \<noteq> 0"
    by (metis \<open>y \<notin> frontier S\<close> g(1) gt pathstart_def)
  ultimately have  t01: "0 < t" "t \<le> 1"
    by auto
  have "V \<subseteq> frontier S"
    using opeSV openin_contains_ball by blast
  show ?thesis
  proof
    show "arc (subpath 0 t g)"
      by (simp add: \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>arc g\<close> \<open>t \<noteq> 0\<close> arc_subpath_arc)
    have "g 0 \<in> S"
      by (metis \<open>y \<in> S\<close> g(1) pathstart_def)
    then show "pathstart (subpath 0 t g) \<in> S"
      by auto
    have "g t \<in> V"
      by (metis IntI atLeastAtMost_iff gt image_eqI path_image_def pig r subsetCE \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>)
    then show "pathfinish (subpath 0 t g) \<in> V"
      by auto
    then have "inj_on (subpath 0 t g) {0..1}"
      using t01 \<open>arc (subpath 0 t g)\<close> arc_imp_inj_on by blast
    then have "subpath 0 t g ` {0..<1} \<subseteq> subpath 0 t g ` {0..1} - {subpath 0 t g 1}"
      by (force simp: dest: inj_onD)
    moreover have False if "subpath 0 t g ` ({0..<1}) - S \<noteq> {}"
    proof -
      have contg: "continuous_on {0..1} g"
        using \<open>arc g\<close> by (auto simp: arc_def path_def)
      have "subpath 0 t g ` {0..<1} \<inter> frontier S \<noteq> {}"
      proof (rule connected_Int_frontier [OF _ _ that])
        show "connected (subpath 0 t g ` {0..<1})"
        proof (rule connected_continuous_image)
          show "continuous_on {0..<1} (subpath 0 t g)"
            by (meson \<open>arc (subpath 0 t g)\<close> arc_def atLeastLessThan_subseteq_atLeastAtMost_iff continuous_on_subset order_refl path_def)
        qed auto
        show "subpath 0 t g ` {0..<1} \<inter> S \<noteq> {}"
          using \<open>y \<in> S\<close> g(1) by (force simp: subpath_def image_def pathstart_def)
      qed
      then obtain x where "x \<in> subpath 0 t g ` {0..<1}" "x \<in> frontier S"
        by blast
      with t01 \<open>0 \<le> t\<close> mult_le_one t show False
        by (fastforce simp: subpath_def)
    qed
    then have "subpath 0 t g ` {0..1} - {subpath 0 t g 1} \<subseteq> S"
      using subsetD by fastforce
    ultimately  show "subpath 0 t g ` {0..<1} \<subseteq> S"
      by auto
  qed
qed


lemma dense_accessible_frontier_points_connected:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes "open S" "connected S" "x \<in> S" "V \<noteq> {}"
      and ope: "openin (top_of_set (frontier S)) V"
  obtains g where "arc g" "g ` {0..<1} \<subseteq> S" "pathstart g = x" "pathfinish g \<in> V"
proof -
  have "V \<subseteq> frontier S"
    using ope openin_imp_subset by blast
  with \<open>open S\<close> \<open>x \<in> S\<close> have "x \<notin> V"
    using interior_open by (auto simp: frontier_def)
  obtain g where "arc g" and g: "g ` {0..<1} \<subseteq> S" "pathstart g \<in> S" "pathfinish g \<in> V"
    by (metis dense_accessible_frontier_points [OF \<open>open S\<close> ope \<open>V \<noteq> {}\<close>])
  then have "path_connected S"
    by (simp add: assms connected_open_path_connected)
  with \<open>pathstart g \<in> S\<close> \<open>x \<in> S\<close> have "path_component S x (pathstart g)"
    by (simp add: path_connected_component)
  then obtain f where "path f" and f: "path_image f \<subseteq> S" "pathstart f = x" "pathfinish f = pathstart g"
    by (auto simp: path_component_def)
  then have "path (f +++ g)"
    by (simp add: \<open>arc g\<close> arc_imp_path)
  then obtain h where "arc h"
                  and h: "path_image h \<subseteq> path_image (f +++ g)" "pathstart h = x" "pathfinish h = pathfinish g"
    using path_contains_arc [of "f +++ g" x "pathfinish g"] \<open>x \<notin> V\<close> \<open>pathfinish g \<in> V\<close> f
    by (metis pathfinish_join pathstart_join)
  have "path_image h \<subseteq> path_image f \<union> path_image g"
    using h(1) path_image_join_subset by auto
  then have "h ` {0..1} - {h 1} \<subseteq> S"
    using f g h
    apply (simp add: path_image_def pathfinish_def subset_iff image_def Bex_def)
    by (metis le_less)
  then have "h ` {0..<1} \<subseteq> S"
    using \<open>arc h\<close> by (force simp: arc_def dest: inj_onD)
  then show thesis
    using \<open>arc h\<close> g(3) h that by presburger
qed

lemma dense_access_fp_aux:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes S: "open S" "connected S"
      and opeSU: "openin (top_of_set (frontier S)) U"
      and opeSV: "openin (top_of_set (frontier S)) V"
      and "V \<noteq> {}" "\<not> U \<subseteq> V"
  obtains g where "arc g" "pathstart g \<in> U" "pathfinish g \<in> V" "g ` {0<..<1} \<subseteq> S"
proof -
  have "S \<noteq> {}"
    using opeSV \<open>V \<noteq> {}\<close> by (metis frontier_empty openin_subtopology_empty)
  then obtain x where "x \<in> S" by auto
  obtain g where "arc g" and g: "g ` {0..<1} \<subseteq> S" "pathstart g = x" "pathfinish g \<in> V"
    using dense_accessible_frontier_points_connected [OF S \<open>x \<in> S\<close> \<open>V \<noteq> {}\<close> opeSV] by blast
  obtain h where "arc h" and h: "h ` {0..<1} \<subseteq> S" "pathstart h = x" "pathfinish h \<in> U - {pathfinish g}"
  proof (rule dense_accessible_frontier_points_connected [OF S \<open>x \<in> S\<close>])
    show "U - {pathfinish g} \<noteq> {}"
      using \<open>pathfinish g \<in> V\<close> \<open>\<not> U \<subseteq> V\<close> by blast
    show "openin (top_of_set (frontier S)) (U - {pathfinish g})"
      by (simp add: opeSU openin_delete)
  qed auto
  obtain \<gamma> where "arc \<gamma>"
             and \<gamma>: "path_image \<gamma> \<subseteq> path_image (reversepath h +++ g)"
                    "pathstart \<gamma> = pathfinish h" "pathfinish \<gamma> = pathfinish g"
  proof (rule path_contains_arc [of "(reversepath h +++ g)" "pathfinish h" "pathfinish g"])
    show "path (reversepath h +++ g)"
      by (simp add: \<open>arc g\<close> \<open>arc h\<close> \<open>pathstart g = x\<close> \<open>pathstart h = x\<close> arc_imp_path)
    show "pathstart (reversepath h +++ g) = pathfinish h"
         "pathfinish (reversepath h +++ g) = pathfinish g"
      by auto
    show "pathfinish h \<noteq> pathfinish g"
      using \<open>pathfinish h \<in> U - {pathfinish g}\<close> by auto
  qed auto
  show ?thesis
  proof
    show "arc \<gamma>" "pathstart \<gamma> \<in> U" "pathfinish \<gamma> \<in> V"
      using \<gamma> \<open>arc \<gamma>\<close> \<open>pathfinish h \<in> U - {pathfinish g}\<close>  \<open>pathfinish g \<in> V\<close> by auto
    have "path_image \<gamma> \<subseteq> path_image h \<union> path_image g"
      by (metis \<gamma>(1) g(2) h(2) path_image_join path_image_reversepath pathfinish_reversepath)
    then have "\<gamma> ` {0..1} - {\<gamma> 0, \<gamma> 1} \<subseteq> S"
      using \<gamma> g h 
      apply (simp add: path_image_def pathstart_def pathfinish_def subset_iff image_def Bex_def)
      by (metis linorder_neqE_linordered_idom not_less)
    then show "\<gamma> ` {0<..<1} \<subseteq> S"
      using \<open>arc h\<close> \<open>arc \<gamma>\<close>
      by (metis arc_imp_simple_path path_image_def pathfinish_def pathstart_def simple_path_endless)
  qed
qed

lemma dense_accessible_frontier_point_pairs:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes S: "open S" "connected S"
      and opeSU: "openin (top_of_set (frontier S)) U"
      and opeSV: "openin (top_of_set (frontier S)) V"
      and "U \<noteq> {}" "V \<noteq> {}" "U \<noteq> V"
    obtains g where "arc g" "pathstart g \<in> U" "pathfinish g \<in> V" "g ` {0<..<1} \<subseteq> S"
proof -
  consider "\<not> U \<subseteq> V" | "\<not> V \<subseteq> U"
    using \<open>U \<noteq> V\<close> by blast
  then show ?thesis
  proof cases
    case 1 then show ?thesis
      using assms dense_access_fp_aux [OF S opeSU opeSV] that by blast
  next
    case 2
    obtain g where "arc g" and g: "pathstart g \<in> V" "pathfinish g \<in> U" "g ` {0<..<1} \<subseteq> S"
      using assms dense_access_fp_aux [OF S opeSV opeSU] "2" by blast
    show ?thesis
    proof
      show "arc (reversepath g)"
        by (simp add: \<open>arc g\<close> arc_reversepath)
      show "pathstart (reversepath g) \<in> U" "pathfinish (reversepath g) \<in> V"
        using g by auto
      show "reversepath g ` {0<..<1} \<subseteq> S"
        using g by (auto simp: reversepath_def)
    qed
  qed
qed

end
