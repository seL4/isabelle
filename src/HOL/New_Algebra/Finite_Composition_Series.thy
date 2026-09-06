theory Finite_Composition_Series
  imports Maximal_Normal_Subgroup
begin

section \<open>Composition series of finite groups\<close>

text \<open>
  A composition series for a normal subgroup can be extended by one simple
  factor.  The old terms retain their indices and the new ambient group is
  placed at the successor of the old length.  Keeping this construction
  separate makes the finite-cardinality induction below reusable.
\<close>
definition extend_composition_series ::
    "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set"
  where
    "extend_composition_series H n G i = (if i \<le> n then H i else G)"

lemma extend_composition_series_old [simp]:
  "i \<le> n \<Longrightarrow> extend_composition_series H n G i = H i"
  by (simp add: extend_composition_series_def)

lemma extend_composition_series_top [simp]:
  "extend_composition_series H n G (Suc n) = G"
  by (simp add: extend_composition_series_def)

theorem composition_series_extend_simple_factor:
  assumes series: "composition_series K composition unit H n"
    and factor: "simple_factor_group K G composition unit"
  shows "composition_series G composition unit
    (extend_composition_series H n G) (Suc n)"
proof -
  interpret series: composition_series K composition unit H n
    by (rule series)
  interpret factor: simple_factor_group K G composition unit
    by (rule factor)
  show ?thesis
  proof (intro composition_series.intro)
    show "normal_series G composition unit
        (extend_composition_series H n G) (Suc n)"
    proof (intro normal_series.intro)
      show "Group G composition unit" by (rule factor.N.Group_axioms)
    next
      show "normal_series_axioms G composition unit
          (extend_composition_series H n G) (Suc n)"
      proof (intro normal_series_axioms.intro)
        show "extend_composition_series H n G 0 = {unit}"
          using series.bottom by simp
      next
        show "extend_composition_series H n G (Suc n) = G" by simp
      next
        fix i
        assume i: "i \<le> Suc n"
        show "Subgroup (extend_composition_series H n G i) G composition unit"
        proof (cases "i \<le> n")
          case True
          have old: "Subgroup (H i) K composition unit"
            by (rule series.term_subgroup[OF True])
          show ?thesis
            using subgroup_transitive[OF old factor.N.Subgroup_axioms] True
            by simp
        next
          case False
          then have "i = Suc n" using i by arith
          then show ?thesis
            by (simp add: factor.N.group_self_subgroup)
        qed
      next
        fix i
        assume i: "i < Suc n"
        show "normal_subgroup (extend_composition_series H n G i)
            (extend_composition_series H n G (Suc i)) composition unit"
        proof (cases "i < n")
          case True
          then show ?thesis
            using series.normal_step[OF True] by simp
        next
          case False
          then have "i = n" using i by arith
          then show ?thesis
            using series.top factor.N.normal_subgroup_axioms by simp
        qed
      qed
    qed
  next
    show "composition_series_axioms composition unit
        (extend_composition_series H n G) (Suc n)"
    proof (intro composition_series_axioms.intro)
      fix i
      assume i: "i < Suc n"
      show "simple_factor_group (extend_composition_series H n G i)
          (extend_composition_series H n G (Suc i)) composition unit"
      proof (cases "i < n")
        case True
        then show ?thesis
          using series.factor_simple[OF True] by simp
        next
          case False
          then have "i = n" using i by arith
          then show ?thesis using series.top factor by simp
      qed
    qed
  qed
qed


subsection \<open>Existence\<close>

text \<open>
  Every finite group has a composition series.  For a nontrivial group, choose
  a maximal normal subgroup.  Its quotient is simple, while its proper carrier
  has smaller cardinality, so the induction hypothesis supplies the prefix.
\<close>
theorem finite_group_has_composition_series_ex:
  assumes G: "Group G composition unit" and finite_G: "finite G"
  shows "\<exists>H n. composition_series G composition unit H n"
  using G finite_G
proof (induction "card G" arbitrary: G composition unit rule: less_induct)
  case less
  interpret G: Group G composition unit by (rule less.prems(1))
  show ?case
  proof (cases "G = {unit}")
    case True
    have "composition_series G composition unit (\<lambda>_. G) 0"
    proof (intro composition_series.intro normal_series.intro)
      show "Group G composition unit" by (rule G.Group_axioms)
    next
      show "normal_series_axioms G composition unit (\<lambda>_. G) 0"
        using True G.group_self_subgroup
        by unfold_locales auto
    next
      show "composition_series_axioms composition unit (\<lambda>_. G) 0"
      proof (rule composition_series_axioms.intro)
        fix i :: nat
        assume "i < 0"
        then show "simple_factor_group ((\<lambda>_. G) i)
            ((\<lambda>_. G) (Suc i)) composition unit"
          by simp
      qed
    qed
    then show ?thesis by blast
  next
    case False
    obtain M where maximal: "maximal_normal_subgroup M G composition unit"
      using finite_nontrivial_group_has_maximal_normal_subgroup[OF
          G.Group_axioms less.prems(2) False] .
    interpret maximal: maximal_normal_subgroup M G composition unit
      by (rule maximal)
    have finite_M: "finite M"
      by (rule finite_subset[OF maximal.N.subset less.prems(2)])
    have card_M_less: "card M < card G"
      by (rule psubset_card_mono[OF less.prems(2) maximal.strict])
    have M_group: "Group M composition unit"
      by (rule subgroup_imp_Group[OF maximal.N.Subgroup_axioms])
    obtain H n where prefix: "composition_series M composition unit H n"
      using less.hyps[OF card_M_less M_group finite_M] by blast
    have factor: "simple_factor_group M G composition unit"
      by (rule iffD1[OF maximal_normal_subgroup_iff_simple_factor_group maximal])
    have "composition_series G composition unit
        (extend_composition_series H n G) (Suc n)"
      by (rule composition_series_extend_simple_factor[OF prefix factor])
    then show ?thesis by blast
  qed
qed

corollary finite_group_has_composition_series:
  assumes G: "Group G composition unit" and finite_G: "finite G"
  obtains H n where "composition_series G composition unit H n"
  using finite_group_has_composition_series_ex[OF G finite_G] that by blast

end
