theory Normal_Series
  imports Group_Theory
begin

section \<open>Finite normal series\<close>

text \<open>
  The canonical one-step series has the trivial subgroup at index zero and the
  full carrier thereafter.  Values beyond its declared length are immaterial.
\<close>
definition one_step_normal_series_term ::
    "'a set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set"
  where
    "one_step_normal_series_term G unit i = (if i = 0 then {unit} else G)"

text \<open>
  A finite normal series is a finite chain of subgroups beginning at the
  trivial subgroup and ending at the ambient group, with each term normal in
  the next one.  The chain is indexed by the natural numbers from @{term 0}
  through @{term n}; repeated terms are permitted, so strictness can be added
  separately when defining composition series.

  The definition is deliberately stated with carrier sets and the existing
  @{locale normal_subgroup} locale.  In particular, it does not introduce a
  second representation of quotient groups or subgroup chains.
\<close>

locale normal_series =
  G: Group G "(\<cdot>)" \<one>
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  fixes H :: "nat \<Rightarrow> 'a set" and n :: nat
  assumes bottom: "H 0 = {\<one>}"
    and top: "H n = G"
    and term_subgroup: "\<And>i. i \<le> n \<Longrightarrow> Subgroup (H i) G (\<cdot>) \<one>"
    and normal_step:
      "\<And>i. i < n \<Longrightarrow> normal_subgroup (H i) (H (Suc i)) (\<cdot>) \<one>"
begin

text \<open>
  The factor at index @{term i} is packaged as the carrier, operation, and unit
  of the quotient of @{term "H (Suc i)"} by @{term "H i"}.  The definition is
  total in the index; the series assumptions provide the group interpretation
  whenever @{term "i < n"}.
\<close>

definition series_factor ::
    "nat \<Rightarrow> ('a set set \<times> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a set) \<times> 'a set)"
  where
    "series_factor i =
      (normal_subgroup.Factor_Group (H i) (H (Suc i)) (\<cdot>) \<one>,
       Monoid_congruence.quotient_composition
         (H (Suc i)) (\<cdot>)
         (normal_subgroup.Congruence (H i) (H (Suc i)) (\<cdot>) \<one>),
       Equivalence.Class (H (Suc i))
         (normal_subgroup.Congruence (H i) (H (Suc i)) (\<cdot>) \<one>) \<one>)"

text \<open>The finite factor sequence is ordered by increasing index.\<close>

definition series_factors ::
    "('a set set \<times> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a set) \<times> 'a set) list"
  where
    "series_factors = List.map series_factor [0..<n]"

lemma length_series_factors:
  "length series_factors = n"
  unfolding series_factors_def by simp

lemma series_factors_prefix:
  assumes k: "k \<le> n"
  shows "take k series_factors = List.map series_factor [0..<k]"
  using k unfolding series_factors_def by (simp add: take_map)

lemma series_factors_nth:
  assumes i: "i < n"
  shows "series_factors ! i = series_factor i"
  using i unfolding series_factors_def by simp

lemma series_factor_group:
  assumes i: "i < n"
  shows "Group (fst (series_factor i))
      (fst (snd (series_factor i))) (snd (snd (series_factor i)))"
proof -
  interpret step: normal_subgroup "H i" "H (Suc i)" "(\<cdot>)" \<one>
    by (rule normal_step[OF i])
  show ?thesis
    unfolding series_factor_def
    using step.quotient.Group_axioms by simp
qed

text \<open>The adjacent terms form a subgroup and are ordered by inclusion.\<close>

lemma normal_step_subgroup:
  assumes i: "i < n"
  shows "Subgroup (H i) (H (Suc i)) (\<cdot>) \<one>"
proof -
  interpret step: normal_subgroup "H i" "H (Suc i)" "(\<cdot>)" \<one>
    by (rule normal_step[OF i])
  show ?thesis by (rule step.Subgroup_axioms)
qed

lemma normal_step_subset:
  assumes i: "i < n"
  shows "H i \<subseteq> H (Suc i)"
proof -
  interpret step: normal_subgroup "H i" "H (Suc i)" "(\<cdot>)" \<one>
    by (rule normal_step[OF i])
  show ?thesis by (rule step.subset)
qed

lemma series_term_subset:
  assumes i: "i \<le> n"
  shows "H i \<subseteq> G"
proof -
  interpret T: Subgroup "H i" G "(\<cdot>)" \<one>
    by (rule term_subgroup[OF i])
  show ?thesis by (rule T.subset)
qed

text \<open>Inclusion propagates through the entire finite chain.\<close>

lemma normal_series_mono:
  fixes i j :: nat
  assumes ij: "i \<le> j" and jn: "j \<le> n"
  shows "H i \<subseteq> H j"
  using ij
proof (induction rule: inc_induct)
  case base
  show "H j \<subseteq> H j" by simp
next
  case (step k)
  have k_lt_n: "k < n"
  proof (rule less_le_trans)
    show "k < j" by (rule step(2))
    show "j \<le> n" by fact
  qed
  have step_k: "H k \<subseteq> H (Suc k)"
    by (rule normal_step_subset[OF k_lt_n])
  have ih: "H (Suc k) \<subseteq> H j"
    by (rule step(3))
  show ?case by (rule subset_trans[OF step_k ih])
qed

lemma series_bottom_subset:
  assumes i: "i \<le> n"
  shows "H 0 \<subseteq> H i"
  by (rule normal_series_mono[OF zero_le i])

text \<open>Every term in a prefix is a subgroup of the prefix's top term.\<close>

lemma series_prefix_subgroup:
  assumes k: "k \<le> n" and i: "i \<le> k"
  shows "Subgroup (H i) (H k) (\<cdot>) \<one>"
proof -
  have i_n: "i \<le> n" by (rule le_trans[OF i k])
  have i_subset_k: "H i \<subseteq> H k" by (rule normal_series_mono[OF i k])
  show ?thesis
  proof (rule subgroup_restrict)
    show "Subgroup (H i) G (\<cdot>) \<one>" by (rule term_subgroup[OF i_n])
    show "Subgroup (H k) G (\<cdot>) \<one>" by (rule term_subgroup[OF k])
    show "H i \<subseteq> H k" by fact
  qed
qed

text \<open>The terms up to any index form a normal series for that term.\<close>

lemma prefix_normal_series:
  assumes k: "k \<le> n"
  shows "normal_series (H k) (\<cdot>) \<one> H k"
proof -
  have Hk_subgroup: "Subgroup (H k) G (\<cdot>) \<one>"
    by (rule term_subgroup[OF k])
  have Hk_group: "Group (H k) (\<cdot>) \<one>"
    by (rule subgroup_imp_Group[OF Hk_subgroup])
  show ?thesis
  proof (intro normal_series.intro)
    show "Group (H k) (\<cdot>) \<one>" by fact
  next
    show "normal_series_axioms (H k) (\<cdot>) \<one> H k"
    proof (intro normal_series_axioms.intro)
      show "H 0 = {\<one>}" by (rule bottom)
    next
      show "H k = H k" by simp
    next
      show "\<And>i. i \<le> k \<Longrightarrow> Subgroup (H i) (H k) (\<cdot>) \<one>"
      proof -
        fix i
        assume i: "i \<le> k"
        show "Subgroup (H i) (H k) (\<cdot>) \<one>"
          by (rule series_prefix_subgroup[OF k i])
      qed
    next
      show "\<And>i. i < k \<Longrightarrow> normal_subgroup (H i) (H (Suc i)) (\<cdot>) \<one>"
      proof -
        fix i
        assume i: "i < k"
        have i_n: "i < n" by (rule less_le_trans[OF i k])
        show "normal_subgroup (H i) (H (Suc i)) (\<cdot>) \<one>"
          by (rule normal_step[OF i_n])
      qed
    qed
  qed
qed

lemma zero_length_implies_trivial:
  assumes "n = 0"
  shows "G = {\<one>}"
proof -
  have "G = H 0"
    using top assms by simp
  also have "... = {\<one>}"
    by (rule bottom)
  finally show "G = {\<one>}" .
qed

end

context Group begin

text \<open>
  Every group has the canonical one-step normal series from its trivial
  subgroup to its full carrier.  For the trivial group the two terms coincide,
  as repetitions are permitted in a normal series.
\<close>
lemma one_step_normal_series:
  "normal_series G (\<cdot>) \<one> (one_step_normal_series_term G \<one>) 1"
proof (intro normal_series.intro)
  show "Group G (\<cdot>) \<one>" by (rule Group_axioms)
  show "normal_series_axioms G (\<cdot>) \<one>
      (one_step_normal_series_term G \<one>) 1"
  proof (rule normal_series_axioms.intro)
    show "one_step_normal_series_term G \<one> 0 = {\<one>}"
      by (simp add: one_step_normal_series_term_def)
    show "one_step_normal_series_term G \<one> 1 = G"
      by (simp add: one_step_normal_series_term_def)
    show "\<And>i. i \<le> 1 \<Longrightarrow>
        Subgroup (one_step_normal_series_term G \<one> i) G (\<cdot>) \<one>"
      by (auto simp: one_step_normal_series_term_def le_Suc_eq
            trivial_subgroup group_self_subgroup)
    show "\<And>i. i < 1 \<Longrightarrow>
        normal_subgroup (one_step_normal_series_term G \<one> i)
          (one_step_normal_series_term G \<one> (Suc i)) (\<cdot>) \<one>"
      using trivial_normal_subgroup
      by (simp add: one_step_normal_series_term_def)
  qed
qed

end

end
