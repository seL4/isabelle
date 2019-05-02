(*  Title:      HOL/Nonstandard_Analysis/HyperNat.thy
    Author:     Jacques D. Fleuriot
    Copyright:  1998  University of Cambridge

Converted to Isar and polished by lcp
*)

section \<open>Hypernatural numbers\<close>

theory HyperNat
  imports StarDef
begin

type_synonym hypnat = "nat star"

abbreviation hypnat_of_nat :: "nat \<Rightarrow> nat star"
  where "hypnat_of_nat \<equiv> star_of"

definition hSuc :: "hypnat \<Rightarrow> hypnat"
  where hSuc_def [transfer_unfold]: "hSuc = *f* Suc"


subsection \<open>Properties Transferred from Naturals\<close>

lemma hSuc_not_zero [iff]: "\<And>m. hSuc m \<noteq> 0"
  by transfer (rule Suc_not_Zero)

lemma zero_not_hSuc [iff]: "\<And>m. 0 \<noteq> hSuc m"
  by transfer (rule Zero_not_Suc)

lemma hSuc_hSuc_eq [iff]: "\<And>m n. hSuc m = hSuc n \<longleftrightarrow> m = n"
  by transfer (rule nat.inject)

lemma zero_less_hSuc [iff]: "\<And>n. 0 < hSuc n"
  by transfer (rule zero_less_Suc)

lemma hypnat_minus_zero [simp]: "\<And>z::hypnat. z - z = 0"
  by transfer (rule diff_self_eq_0)

lemma hypnat_diff_0_eq_0 [simp]: "\<And>n::hypnat. 0 - n = 0"
  by transfer (rule diff_0_eq_0)

lemma hypnat_add_is_0 [iff]: "\<And>m n::hypnat. m + n = 0 \<longleftrightarrow> m = 0 \<and> n = 0"
  by transfer (rule add_is_0)

lemma hypnat_diff_diff_left: "\<And>i j k::hypnat. i - j - k = i - (j + k)"
  by transfer (rule diff_diff_left)

lemma hypnat_diff_commute: "\<And>i j k::hypnat. i - j - k = i - k - j"
  by transfer (rule diff_commute)

lemma hypnat_diff_add_inverse [simp]: "\<And>m n::hypnat. n + m - n = m"
  by transfer (rule diff_add_inverse)

lemma hypnat_diff_add_inverse2 [simp]:  "\<And>m n::hypnat. m + n - n = m"
  by transfer (rule diff_add_inverse2)

lemma hypnat_diff_cancel [simp]: "\<And>k m n::hypnat. (k + m) - (k + n) = m - n"
  by transfer (rule diff_cancel)

lemma hypnat_diff_cancel2 [simp]: "\<And>k m n::hypnat. (m + k) - (n + k) = m - n"
  by transfer (rule diff_cancel2)

lemma hypnat_diff_add_0 [simp]: "\<And>m n::hypnat. n - (n + m) = 0"
  by transfer (rule diff_add_0)

lemma hypnat_diff_mult_distrib: "\<And>k m n::hypnat. (m - n) * k = (m * k) - (n * k)"
  by transfer (rule diff_mult_distrib)

lemma hypnat_diff_mult_distrib2: "\<And>k m n::hypnat. k * (m - n) = (k * m) - (k * n)"
  by transfer (rule diff_mult_distrib2)

lemma hypnat_le_zero_cancel [iff]: "\<And>n::hypnat. n \<le> 0 \<longleftrightarrow> n = 0"
  by transfer (rule le_0_eq)

lemma hypnat_mult_is_0 [simp]: "\<And>m n::hypnat. m * n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  by transfer (rule mult_is_0)

lemma hypnat_diff_is_0_eq [simp]: "\<And>m n::hypnat. m - n = 0 \<longleftrightarrow> m \<le> n"
  by transfer (rule diff_is_0_eq)

lemma hypnat_not_less0 [iff]: "\<And>n::hypnat. \<not> n < 0"
  by transfer (rule not_less0)

lemma hypnat_less_one [iff]: "\<And>n::hypnat. n < 1 \<longleftrightarrow> n = 0"
  by transfer (rule less_one)

lemma hypnat_add_diff_inverse: "\<And>m n::hypnat. \<not> m < n \<Longrightarrow> n + (m - n) = m"
  by transfer (rule add_diff_inverse)

lemma hypnat_le_add_diff_inverse [simp]: "\<And>m n::hypnat. n \<le> m \<Longrightarrow> n + (m - n) = m"
  by transfer (rule le_add_diff_inverse)

lemma hypnat_le_add_diff_inverse2 [simp]: "\<And>m n::hypnat. n \<le> m \<Longrightarrow> (m - n) + n = m"
  by transfer (rule le_add_diff_inverse2)

declare hypnat_le_add_diff_inverse2 [OF order_less_imp_le]

lemma hypnat_le0 [iff]: "\<And>n::hypnat. 0 \<le> n"
  by transfer (rule le0)

lemma hypnat_le_add1 [simp]: "\<And>x n::hypnat. x \<le> x + n"
  by transfer (rule le_add1)

lemma hypnat_add_self_le [simp]: "\<And>x n::hypnat. x \<le> n + x"
  by transfer (rule le_add2)

lemma hypnat_add_one_self_less [simp]: "x < x + 1" for x :: hypnat
  by (fact less_add_one)

lemma hypnat_neq0_conv [iff]: "\<And>n::hypnat. n \<noteq> 0 \<longleftrightarrow> 0 < n"
  by transfer (rule neq0_conv)

lemma hypnat_gt_zero_iff: "0 < n \<longleftrightarrow> 1 \<le> n" for n :: hypnat
  by (auto simp add: linorder_not_less [symmetric])

lemma hypnat_gt_zero_iff2: "0 < n \<longleftrightarrow> (\<exists>m. n = m + 1)" for n :: hypnat
  by (auto intro!: add_nonneg_pos exI[of _ "n - 1"] simp: hypnat_gt_zero_iff)

lemma hypnat_add_self_not_less: "\<not> x + y < x" for x y :: hypnat
  by (simp add: linorder_not_le [symmetric] add.commute [of x])

lemma hypnat_diff_split: "P (a - b) \<longleftrightarrow> (a < b \<longrightarrow> P 0) \<and> (\<forall>d. a = b + d \<longrightarrow> P d)"
  for a b :: hypnat
  \<comment> \<open>elimination of \<open>-\<close> on \<open>hypnat\<close>\<close>
proof (cases "a < b" rule: case_split)
  case True
  then show ?thesis
    by (auto simp add: hypnat_add_self_not_less order_less_imp_le hypnat_diff_is_0_eq [THEN iffD2])
next
  case False
  then show ?thesis
    by (auto simp add: linorder_not_less dest: order_le_less_trans)
qed


subsection \<open>Properties of the set of embedded natural numbers\<close>

lemma of_nat_eq_star_of [simp]: "of_nat = star_of"
proof
  show "of_nat n = star_of n" for n
    by transfer simp
qed

lemma Nats_eq_Standard: "(Nats :: nat star set) = Standard"
  by (auto simp: Nats_def Standard_def)

lemma hypnat_of_nat_mem_Nats [simp]: "hypnat_of_nat n \<in> Nats"
  by (simp add: Nats_eq_Standard)

lemma hypnat_of_nat_one [simp]: "hypnat_of_nat (Suc 0) = 1"
  by transfer simp

lemma hypnat_of_nat_Suc [simp]: "hypnat_of_nat (Suc n) = hypnat_of_nat n + 1"
  by transfer simp

lemma of_nat_eq_add: 
  fixes d::hypnat
  shows "of_nat m = of_nat n + d \<Longrightarrow> d \<in> range of_nat"
proof (induct n arbitrary: d)
  case (Suc n)
  then show ?case
    by (metis Nats_def Nats_eq_Standard Standard_simps(4) hypnat_diff_add_inverse of_nat_in_Nats)
qed auto

lemma Nats_diff [simp]: "a \<in> Nats \<Longrightarrow> b \<in> Nats \<Longrightarrow> a - b \<in> Nats" for a b :: hypnat
  by (simp add: Nats_eq_Standard)


subsection \<open>Infinite Hypernatural Numbers -- \<^term>\<open>HNatInfinite\<close>\<close>

text \<open>The set of infinite hypernatural numbers.\<close>
definition HNatInfinite :: "hypnat set"
  where "HNatInfinite = {n. n \<notin> Nats}"

lemma Nats_not_HNatInfinite_iff: "x \<in> Nats \<longleftrightarrow> x \<notin> HNatInfinite"
  by (simp add: HNatInfinite_def)

lemma HNatInfinite_not_Nats_iff: "x \<in> HNatInfinite \<longleftrightarrow> x \<notin> Nats"
  by (simp add: HNatInfinite_def)

lemma star_of_neq_HNatInfinite: "N \<in> HNatInfinite \<Longrightarrow> star_of n \<noteq> N"
  by (auto simp add: HNatInfinite_def Nats_eq_Standard)

lemma star_of_Suc_lessI: "\<And>N. star_of n < N \<Longrightarrow> star_of (Suc n) \<noteq> N \<Longrightarrow> star_of (Suc n) < N"
  by transfer (rule Suc_lessI)

lemma star_of_less_HNatInfinite:
  assumes N: "N \<in> HNatInfinite"
  shows "star_of n < N"
proof (induct n)
  case 0
  from N have "star_of 0 \<noteq> N"
    by (rule star_of_neq_HNatInfinite)
  then show ?case by simp
next
  case (Suc n)
  from N have "star_of (Suc n) \<noteq> N"
    by (rule star_of_neq_HNatInfinite)
  with Suc show ?case
    by (rule star_of_Suc_lessI)
qed

lemma star_of_le_HNatInfinite: "N \<in> HNatInfinite \<Longrightarrow> star_of n \<le> N"
  by (rule star_of_less_HNatInfinite [THEN order_less_imp_le])


subsubsection \<open>Closure Rules\<close>

lemma Nats_less_HNatInfinite: "x \<in> Nats \<Longrightarrow> y \<in> HNatInfinite \<Longrightarrow> x < y"
  by (auto simp add: Nats_def star_of_less_HNatInfinite)

lemma Nats_le_HNatInfinite: "x \<in> Nats \<Longrightarrow> y \<in> HNatInfinite \<Longrightarrow> x \<le> y"
  by (rule Nats_less_HNatInfinite [THEN order_less_imp_le])

lemma zero_less_HNatInfinite: "x \<in> HNatInfinite \<Longrightarrow> 0 < x"
  by (simp add: Nats_less_HNatInfinite)

lemma one_less_HNatInfinite: "x \<in> HNatInfinite \<Longrightarrow> 1 < x"
  by (simp add: Nats_less_HNatInfinite)

lemma one_le_HNatInfinite: "x \<in> HNatInfinite \<Longrightarrow> 1 \<le> x"
  by (simp add: Nats_le_HNatInfinite)

lemma zero_not_mem_HNatInfinite [simp]: "0 \<notin> HNatInfinite"
  by (simp add: HNatInfinite_def)

lemma Nats_downward_closed: "x \<in> Nats \<Longrightarrow> y \<le> x \<Longrightarrow> y \<in> Nats" for x y :: hypnat
  using HNatInfinite_not_Nats_iff Nats_le_HNatInfinite by fastforce

lemma HNatInfinite_upward_closed: "x \<in> HNatInfinite \<Longrightarrow> x \<le> y \<Longrightarrow> y \<in> HNatInfinite"
  using HNatInfinite_not_Nats_iff Nats_downward_closed by blast

lemma HNatInfinite_add: "x \<in> HNatInfinite \<Longrightarrow> x + y \<in> HNatInfinite"
  using HNatInfinite_upward_closed hypnat_le_add1 by blast

lemma HNatInfinite_diff: "\<lbrakk>x \<in> HNatInfinite; y \<in> Nats\<rbrakk> \<Longrightarrow> x - y \<in> HNatInfinite"
  by (metis HNatInfinite_not_Nats_iff Nats_add Nats_le_HNatInfinite le_add_diff_inverse)

lemma HNatInfinite_is_Suc: "x \<in> HNatInfinite \<Longrightarrow> \<exists>y. x = y + 1" for x :: hypnat
  using hypnat_gt_zero_iff2 zero_less_HNatInfinite by blast


subsection \<open>Existence of an infinite hypernatural number\<close>

text \<open>\<open>\<omega>\<close> is in fact an infinite hypernatural number = \<open>[<1, 2, 3, \<dots>>]\<close>\<close>
definition whn :: hypnat
  where hypnat_omega_def: "whn = star_n (\<lambda>n::nat. n)"

lemma hypnat_of_nat_neq_whn: "hypnat_of_nat n \<noteq> whn"
  by (simp add: FreeUltrafilterNat.singleton' hypnat_omega_def star_of_def star_n_eq_iff)

lemma whn_neq_hypnat_of_nat: "whn \<noteq> hypnat_of_nat n"
  by (simp add: FreeUltrafilterNat.singleton hypnat_omega_def star_of_def star_n_eq_iff)

lemma whn_not_Nats [simp]: "whn \<notin> Nats"
  by (simp add: Nats_def image_def whn_neq_hypnat_of_nat)

lemma HNatInfinite_whn [simp]: "whn \<in> HNatInfinite"
  by (simp add: HNatInfinite_def)

lemma lemma_unbounded_set [simp]: "eventually (\<lambda>n::nat. m < n) \<U>"
  by (rule filter_leD[OF FreeUltrafilterNat.le_cofinite])
     (auto simp add: cofinite_eq_sequentially eventually_at_top_dense)

lemma hypnat_of_nat_eq: "hypnat_of_nat m  = star_n (\<lambda>n::nat. m)"
  by (simp add: star_of_def)

lemma SHNat_eq: "Nats = {n. \<exists>N. n = hypnat_of_nat N}"
  by (simp add: Nats_def image_def)

lemma Nats_less_whn: "n \<in> Nats \<Longrightarrow> n < whn"
  by (simp add: Nats_less_HNatInfinite)

lemma Nats_le_whn: "n \<in> Nats \<Longrightarrow> n \<le> whn"
  by (simp add: Nats_le_HNatInfinite)

lemma hypnat_of_nat_less_whn [simp]: "hypnat_of_nat n < whn"
  by (simp add: Nats_less_whn)

lemma hypnat_of_nat_le_whn [simp]: "hypnat_of_nat n \<le> whn"
  by (simp add: Nats_le_whn)

lemma hypnat_zero_less_hypnat_omega [simp]: "0 < whn"
  by (simp add: Nats_less_whn)

lemma hypnat_one_less_hypnat_omega [simp]: "1 < whn"
  by (simp add: Nats_less_whn)


subsubsection \<open>Alternative characterization of the set of infinite hypernaturals\<close>

text \<open>\<^term>\<open>HNatInfinite = {N. \<forall>n \<in> Nats. n < N}\<close>\<close>

text\<open>unused, but possibly interesting\<close>
lemma HNatInfinite_FreeUltrafilterNat_eventually:
  assumes "\<And>k::nat. eventually (\<lambda>n. f n \<noteq> k) \<U>"
  shows "eventually (\<lambda>n. m < f n) \<U>"
proof (induct m)
  case 0
  then show ?case
    using assms eventually_mono by fastforce
next
  case (Suc m)
  then show ?case
    using assms [of "Suc m"] eventually_elim2 by fastforce
qed

lemma HNatInfinite_iff: "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"
  using HNatInfinite_def Nats_less_HNatInfinite by auto


subsubsection \<open>Alternative Characterization of \<^term>\<open>HNatInfinite\<close> using Free Ultrafilter\<close>

lemma HNatInfinite_FreeUltrafilterNat:
  "star_n X \<in> HNatInfinite \<Longrightarrow> \<forall>u. eventually (\<lambda>n. u < X n) \<U>"
  by (metis (full_types) starP2_star_of starP_star_n star_less_def star_of_less_HNatInfinite)

lemma FreeUltrafilterNat_HNatInfinite:
  "\<forall>u. eventually (\<lambda>n. u < X n) \<U> \<Longrightarrow> star_n X \<in> HNatInfinite"
  by (auto simp add: star_less_def starP2_star_n HNatInfinite_iff SHNat_eq hypnat_of_nat_eq)

lemma HNatInfinite_FreeUltrafilterNat_iff:
  "(star_n X \<in> HNatInfinite) = (\<forall>u. eventually (\<lambda>n. u < X n) \<U>)"
  by (rule iffI [OF HNatInfinite_FreeUltrafilterNat FreeUltrafilterNat_HNatInfinite])


subsection \<open>Embedding of the Hypernaturals into other types\<close>

definition of_hypnat :: "hypnat \<Rightarrow> 'a::semiring_1_cancel star"
  where of_hypnat_def [transfer_unfold]: "of_hypnat = *f* of_nat"

lemma of_hypnat_0 [simp]: "of_hypnat 0 = 0"
  by transfer (rule of_nat_0)

lemma of_hypnat_1 [simp]: "of_hypnat 1 = 1"
  by transfer (rule of_nat_1)

lemma of_hypnat_hSuc: "\<And>m. of_hypnat (hSuc m) = 1 + of_hypnat m"
  by transfer (rule of_nat_Suc)

lemma of_hypnat_add [simp]: "\<And>m n. of_hypnat (m + n) = of_hypnat m + of_hypnat n"
  by transfer (rule of_nat_add)

lemma of_hypnat_mult [simp]: "\<And>m n. of_hypnat (m * n) = of_hypnat m * of_hypnat n"
  by transfer (rule of_nat_mult)

lemma of_hypnat_less_iff [simp]:
  "\<And>m n. of_hypnat m < (of_hypnat n::'a::linordered_semidom star) \<longleftrightarrow> m < n"
  by transfer (rule of_nat_less_iff)

lemma of_hypnat_0_less_iff [simp]:
  "\<And>n. 0 < (of_hypnat n::'a::linordered_semidom star) \<longleftrightarrow> 0 < n"
  by transfer (rule of_nat_0_less_iff)

lemma of_hypnat_less_0_iff [simp]: "\<And>m. \<not> (of_hypnat m::'a::linordered_semidom star) < 0"
  by transfer (rule of_nat_less_0_iff)

lemma of_hypnat_le_iff [simp]:
  "\<And>m n. of_hypnat m \<le> (of_hypnat n::'a::linordered_semidom star) \<longleftrightarrow> m \<le> n"
  by transfer (rule of_nat_le_iff)

lemma of_hypnat_0_le_iff [simp]: "\<And>n. 0 \<le> (of_hypnat n::'a::linordered_semidom star)"
  by transfer (rule of_nat_0_le_iff)

lemma of_hypnat_le_0_iff [simp]: "\<And>m. (of_hypnat m::'a::linordered_semidom star) \<le> 0 \<longleftrightarrow> m = 0"
  by transfer (rule of_nat_le_0_iff)

lemma of_hypnat_eq_iff [simp]:
  "\<And>m n. of_hypnat m = (of_hypnat n::'a::linordered_semidom star) \<longleftrightarrow> m = n"
  by transfer (rule of_nat_eq_iff)

lemma of_hypnat_eq_0_iff [simp]: "\<And>m. (of_hypnat m::'a::linordered_semidom star) = 0 \<longleftrightarrow> m = 0"
  by transfer (rule of_nat_eq_0_iff)

lemma HNatInfinite_of_hypnat_gt_zero:
  "N \<in> HNatInfinite \<Longrightarrow> (0::'a::linordered_semidom star) < of_hypnat N"
  by (rule ccontr) (simp add: linorder_not_less)

end
