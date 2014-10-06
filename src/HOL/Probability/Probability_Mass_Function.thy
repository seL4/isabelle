theory Probability_Mass_Function
  imports Probability_Measure
begin

lemma sets_Pair: "{x} \<in> sets M1 \<Longrightarrow> {y} \<in> sets M2 \<Longrightarrow> {(x, y)} \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  using pair_measureI[of "{x}" M1 "{y}" M2] by simp

lemma finite_subset_card:
  assumes X: "infinite X" shows "\<exists>A\<subseteq>X. finite A \<and> card A = n"
proof (induct n)
  case (Suc n) then guess A .. note A = this
  with X obtain x where "x \<in> X" "x \<notin> A"
    by (metis subset_antisym subset_eq)
  with A show ?case  
    by (intro exI[of _ "insert x A"]) auto
qed (simp cong: conj_cong)

lemma (in prob_space) countable_support:
  "countable {x. measure M {x} \<noteq> 0}"
proof -
  let ?m = "\<lambda>x. measure M {x}"
  have *: "{x. ?m x \<noteq> 0} = (\<Union>n. {x. inverse (real (Suc n)) < ?m x})"
    by (auto intro!: measure_nonneg reals_Archimedean order_le_neq_trans)
  have **: "\<And>n. finite {x. inverse (Suc n) < ?m x}"
  proof (rule ccontr)
    fix n assume "infinite {x. inverse (Suc n) < ?m x}" (is "infinite ?X")
    then obtain X where "finite X" "card X = Suc (Suc n)" "X \<subseteq> ?X"
      by (metis finite_subset_card)
    from this(3) have *: "\<And>x. x \<in> X \<Longrightarrow> 1 / Suc n \<le> ?m x" 
      by (auto simp: inverse_eq_divide)
    { fix x assume "x \<in> X"
      from *[OF this] have "?m x \<noteq> 0" by auto
      then have "{x} \<in> sets M" by (auto dest: measure_notin_sets) }
    note singleton_sets = this
    have "1 < (\<Sum>x\<in>X. 1 / Suc n)"
      by (simp add: `card X = Suc (Suc n)` real_eq_of_nat[symmetric] real_of_nat_Suc)
    also have "\<dots> \<le> (\<Sum>x\<in>X. ?m x)"
      by (rule setsum_mono) fact
    also have "\<dots> = measure M (\<Union>x\<in>X. {x})"
      using singleton_sets `finite X`
      by (intro finite_measure_finite_Union[symmetric]) (auto simp: disjoint_family_on_def)
    finally show False
      using prob_le_1[of "\<Union>x\<in>X. {x}"] by arith
  qed
  show ?thesis
    unfolding * by (intro countable_UN countableI_type countable_finite[OF **])
qed

lemma measure_count_space: "measure (count_space A) X = (if X \<subseteq> A then card X else 0)"
  unfolding measure_def
  by (cases "finite X") (simp_all add: emeasure_notin_sets)

typedef 'a pmf = "{M :: 'a measure. prob_space M \<and> sets M = UNIV \<and> (AE x in M. measure M {x} \<noteq> 0)}"
  morphisms measure_pmf Abs_pmf
  apply (intro exI[of _ "uniform_measure (count_space UNIV) {undefined}"])
  apply (auto intro!: prob_space_uniform_measure simp: measure_count_space)
  apply (subst uniform_measure_def)
  apply (simp add: AE_density AE_count_space split: split_indicator)
  done

declare [[coercion measure_pmf]]

lemma prob_space_measure_pmf: "prob_space (measure_pmf p)"
  using pmf.measure_pmf[of p] by auto

interpretation measure_pmf!: prob_space "measure_pmf M" for M
  by (rule prob_space_measure_pmf)

locale pmf_as_measure
begin

setup_lifting type_definition_pmf

end

context
begin

interpretation pmf_as_measure .

lift_definition pmf :: "'a pmf \<Rightarrow> 'a \<Rightarrow> real" is "\<lambda>M x. measure M {x}" .

lift_definition set_pmf :: "'a pmf \<Rightarrow> 'a set" is "\<lambda>M. {x. measure M {x} \<noteq> 0}" .

lift_definition map_pmf :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pmf \<Rightarrow> 'b pmf" is
  "\<lambda>f M. distr M (count_space UNIV) f"
proof safe
  fix M and f :: "'a \<Rightarrow> 'b"
  let ?D = "distr M (count_space UNIV) f"
  assume "prob_space M" and [simp]: "sets M = UNIV" and ae: "AE x in M. measure M {x} \<noteq> 0"
  interpret prob_space M by fact
  from ae have "AE x in M. measure M (f -` {f x}) \<noteq> 0"
  proof eventually_elim
    fix x
    have "measure M {x} \<le> measure M (f -` {f x})"
      by (intro finite_measure_mono) auto
    then show "measure M {x} \<noteq> 0 \<Longrightarrow> measure M (f -` {f x}) \<noteq> 0"
      using measure_nonneg[of M "{x}"] by auto
  qed
  then show "AE x in ?D. measure ?D {x} \<noteq> 0"
    by (simp add: AE_distr_iff measure_distr measurable_def)
qed (auto simp: measurable_def prob_space.prob_space_distr)

declare [[coercion set_pmf]]

lemma countable_set_pmf: "countable (set_pmf p)"
  by transfer (metis prob_space.countable_support)

lemma sets_measure_pmf[simp]: "sets (measure_pmf p) = UNIV"
  by transfer metis

lemma space_measure_pmf[simp]: "space (measure_pmf p) = UNIV"
  using sets_eq_imp_space_eq[of "measure_pmf p" "count_space UNIV"] by simp

lemma measurable_pmf_measure1[simp]: "measurable (M :: 'a pmf) N = UNIV \<rightarrow> space N"
  by (auto simp: measurable_def)

lemma measurable_pmf_measure2[simp]: "measurable N (M :: 'a pmf) = measurable N (count_space UNIV)"
  by (intro measurable_cong_sets) simp_all

lemma pmf_positive: "x \<in> set_pmf p \<Longrightarrow> 0 < pmf p x"
  by transfer (simp add: less_le measure_nonneg)

lemma pmf_nonneg: "0 \<le> pmf p x"
  by transfer (simp add: measure_nonneg)

lemma emeasure_pmf_single:
  fixes M :: "'a pmf"
  shows "emeasure M {x} = pmf M x"
  by transfer (simp add: finite_measure.emeasure_eq_measure[OF prob_space.finite_measure])

lemma AE_measure_pmf: "AE x in (M::'a pmf). x \<in> M"
  by transfer simp

lemma emeasure_pmf_single_eq_zero_iff:
  fixes M :: "'a pmf"
  shows "emeasure M {y} = 0 \<longleftrightarrow> y \<notin> M"
  by transfer (simp add: finite_measure.emeasure_eq_measure[OF prob_space.finite_measure])

lemma AE_measure_pmf_iff: "(AE x in measure_pmf M. P x) \<longleftrightarrow> (\<forall>y\<in>M. P y)"
proof -
  { fix y assume y: "y \<in> M" and P: "AE x in M. P x" "\<not> P y"
    with P have "AE x in M. x \<noteq> y"
      by auto
    with y have False
      by (simp add: emeasure_pmf_single_eq_zero_iff AE_iff_measurable[OF _ refl]) }
  then show ?thesis
    using AE_measure_pmf[of M] by auto
qed

lemma measure_pmf_eq_density: "measure_pmf p = density (count_space UNIV) (pmf p)"
proof (transfer, elim conjE)
  fix M :: "'a measure" assume [simp]: "sets M = UNIV" and ae: "AE x in M. measure M {x} \<noteq> 0"
  assume "prob_space M" then interpret prob_space M .
  show "M = density (count_space UNIV) (\<lambda>x. ereal (measure M {x}))"
  proof (rule measure_eqI)
    fix A :: "'a set"
    have "(\<integral>\<^sup>+ x. ereal (measure M {x}) * indicator A x \<partial>count_space UNIV) = 
      (\<integral>\<^sup>+ x. emeasure M {x} * indicator (A \<inter> {x. measure M {x} \<noteq> 0}) x \<partial>count_space UNIV)"
      by (auto intro!: nn_integral_cong simp: emeasure_eq_measure split: split_indicator)
    also have "\<dots> = (\<integral>\<^sup>+ x. emeasure M {x} \<partial>count_space (A \<inter> {x. measure M {x} \<noteq> 0}))"
      by (subst nn_integral_restrict_space[symmetric]) (auto simp: restrict_count_space)
    also have "\<dots> = emeasure M (\<Union>x\<in>(A \<inter> {x. measure M {x} \<noteq> 0}). {x})"
      by (intro emeasure_UN_countable[symmetric] countable_Int2 countable_support)
         (auto simp: disjoint_family_on_def)
    also have "\<dots> = emeasure M A"
      using ae by (intro emeasure_eq_AE) auto
    finally show " emeasure M A = emeasure (density (count_space UNIV) (\<lambda>x. ereal (measure M {x}))) A"
      using emeasure_space_1 by (simp add: emeasure_density)
  qed simp
qed

lemma set_pmf_not_empty: "set_pmf M \<noteq> {}"
  using AE_measure_pmf[of M] by (intro notI) simp

lemma set_pmf_iff: "x \<in> set_pmf M \<longleftrightarrow> pmf M x \<noteq> 0"
  by transfer simp

lemma emeasure_pmf: "emeasure (M::'a pmf) M = 1"
proof -
  have "emeasure (M::'a pmf) M = emeasure (M::'a pmf) (space M)"
    by (intro emeasure_eq_AE) (simp_all add: AE_measure_pmf)
  then show ?thesis
    using measure_pmf.emeasure_space_1 by simp
qed

lemma map_pmf_id[simp]: "map_pmf id = id"
  by (rule, transfer) (auto simp: emeasure_distr measurable_def intro!: measure_eqI)

lemma map_pmf_compose: "map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g"
  by (rule, transfer) (simp add: distr_distr[symmetric, where N="count_space UNIV"] measurable_def) 

lemma map_pmf_cong:
  assumes "p = q"
  shows "(\<And>x. x \<in> set_pmf q \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g q"
  unfolding `p = q`[symmetric] measure_pmf_inject[symmetric] map_pmf.rep_eq
  by (auto simp add: emeasure_distr AE_measure_pmf_iff intro!: emeasure_eq_AE measure_eqI)

lemma pmf_set_map: 
  fixes f :: "'a \<Rightarrow> 'b"
  shows "set_pmf \<circ> map_pmf f = op ` f \<circ> set_pmf"
proof (rule, transfer, clarsimp simp add: measure_distr measurable_def)
  fix f :: "'a \<Rightarrow> 'b" and M :: "'a measure"
  assume "prob_space M" and ae: "AE x in M. measure M {x} \<noteq> 0" and [simp]: "sets M = UNIV"
  interpret prob_space M by fact
  show "{x. measure M (f -` {x}) \<noteq> 0} = f ` {x. measure M {x} \<noteq> 0}"
  proof safe
    fix x assume "measure M (f -` {x}) \<noteq> 0"
    moreover have "measure M (f -` {x}) = measure M {y. f y = x \<and> measure M {y} \<noteq> 0}"
      using ae by (intro finite_measure_eq_AE) auto
    ultimately have "{y. f y = x \<and> measure M {y} \<noteq> 0} \<noteq> {}"
      by (metis measure_empty)
    then show "x \<in> f ` {x. measure M {x} \<noteq> 0}"
      by auto
  next
    fix x assume "measure M {x} \<noteq> 0"
    then have "0 < measure M {x}"
      using measure_nonneg[of M "{x}"] by auto
    also have "measure M {x} \<le> measure M (f -` {f x})"
      by (intro finite_measure_mono) auto
    finally show "measure M (f -` {f x}) = 0 \<Longrightarrow> False"
      by simp
  qed
qed

context
  fixes f :: "'a \<Rightarrow> real"
  assumes nonneg: "\<And>x. 0 \<le> f x"
  assumes prob: "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = 1"
begin

lift_definition embed_pmf :: "'a pmf" is "density (count_space UNIV) (ereal \<circ> f)"
proof (intro conjI)
  have *[simp]: "\<And>x y. ereal (f y) * indicator {x} y = ereal (f x) * indicator {x} y"
    by (simp split: split_indicator)
  show "AE x in density (count_space UNIV) (ereal \<circ> f).
    measure (density (count_space UNIV) (ereal \<circ> f)) {x} \<noteq> 0"
    by (simp add: AE_density nonneg emeasure_density measure_def nn_integral_cmult_indicator)
  show "prob_space (density (count_space UNIV) (ereal \<circ> f))"
    by default (simp add: emeasure_density prob)
qed simp

lemma pmf_embed_pmf: "pmf embed_pmf x = f x"
proof transfer
  have *[simp]: "\<And>x y. ereal (f y) * indicator {x} y = ereal (f x) * indicator {x} y"
    by (simp split: split_indicator)
  fix x show "measure (density (count_space UNIV) (ereal \<circ> f)) {x} = f x"
    by transfer (simp add: measure_def emeasure_density nn_integral_cmult_indicator nonneg)
qed

end

lemma embed_pmf_transfer:
  "rel_fun (eq_onp (\<lambda>f::'a \<Rightarrow> real. (\<forall>x. 0 \<le> f x) \<and> (\<integral>\<^sup>+x. ereal (f x) \<partial>count_space UNIV) = 1)) pmf_as_measure.cr_pmf (\<lambda>f. density (count_space UNIV) (ereal \<circ> f)) embed_pmf"
  by (auto simp: rel_fun_def eq_onp_def embed_pmf.transfer)

lemma td_pmf_embed_pmf:
  "type_definition pmf embed_pmf {f::'a \<Rightarrow> real. (\<forall>x. 0 \<le> f x) \<and> (\<integral>\<^sup>+x. ereal (f x) \<partial>count_space UNIV) = 1}"
  unfolding type_definition_def
proof safe
  fix p :: "'a pmf"
  have "(\<integral>\<^sup>+ x. 1 \<partial>measure_pmf p) = 1"
    using measure_pmf.emeasure_space_1[of p] by simp
  then show *: "(\<integral>\<^sup>+ x. ereal (pmf p x) \<partial>count_space UNIV) = 1"
    by (simp add: measure_pmf_eq_density nn_integral_density pmf_nonneg del: nn_integral_const)

  show "embed_pmf (pmf p) = p"
    by (intro measure_pmf_inject[THEN iffD1])
       (simp add: * embed_pmf.rep_eq pmf_nonneg measure_pmf_eq_density[of p] comp_def)
next
  fix f :: "'a \<Rightarrow> real" assume "\<forall>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = 1"
  then show "pmf (embed_pmf f) = f"
    by (auto intro!: pmf_embed_pmf)
qed (rule pmf_nonneg)

end

locale pmf_as_function
begin

setup_lifting td_pmf_embed_pmf

end 

(*

definition
  "rel_pmf P d1 d2 \<longleftrightarrow> (\<exists>p3. (\<forall>(x, y) \<in> set_pmf p3. P x y) \<and> map_pmf fst p3 = d1 \<and> map_pmf snd p3 = d2)"

lift_definition pmf_join :: "real \<Rightarrow> 'a pmf \<Rightarrow> 'a pmf \<Rightarrow> 'a pmf" is
  "\<lambda>p M1 M2. density (count_space UNIV) (\<lambda>x. p * measure M1 {x} + (1 - p) * measure M2 {x})"
sorry

lift_definition pmf_single :: "'a \<Rightarrow> 'a pmf" is
  "\<lambda>x. uniform_measure (count_space UNIV) {x}"
sorry

bnf pmf: "'a pmf" map: map_pmf sets: set_pmf bd : "natLeq" rel: pmf_rel
proof -
  show "map_pmf id = id" by (rule map_pmf_id)
  show "\<And>f g. map_pmf (f \<circ> g) = map_pmf f \<circ> map_pmf g" by (rule map_pmf_compose) 
  show "\<And>f g::'a \<Rightarrow> 'b. \<And>p. (\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x) \<Longrightarrow> map_pmf f p = map_pmf g p"
    by (intro map_pmg_cong refl)

  show "\<And>f::'a \<Rightarrow> 'b. set_pmf \<circ> map_pmf f = op ` f \<circ> set_pmf"
    by (rule pmf_set_map)

  { fix p :: "'s pmf"
    have "(card_of (set_pmf p), card_of (UNIV :: nat set)) \<in> ordLeq"
      by (rule card_of_ordLeqI[where f="to_nat_on (set_pmf p)"])
         (auto intro: countable_set_pmf inj_on_to_nat_on)
    also have "(card_of (UNIV :: nat set), natLeq) \<in> ordLeq"
      by (metis Field_natLeq card_of_least natLeq_Well_order)
    finally show "(card_of (set_pmf p), natLeq) \<in> ordLeq" . }

  show "\<And>R. pmf_rel R =
         (BNF_Util.Grp {x. set_pmf x \<subseteq> {(x, y). R x y}} (map_pmf fst))\<inverse>\<inverse> OO
         BNF_Util.Grp {x. set_pmf x \<subseteq> {(x, y). R x y}} (map_pmf snd)"
     by (auto simp add: fun_eq_iff pmf_rel_def BNF_Util.Grp_def OO_def)

  { let ?f = "map_pmf fst" and ?s = "map_pmf snd"
    fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and A assume "\<And>x y. (x, y) \<in> set_pmf A \<Longrightarrow> R x y"
    fix S :: "'b \<Rightarrow> 'c \<Rightarrow> bool" and B assume "\<And>y z. (y, z) \<in> set_pmf B \<Longrightarrow> S y z"
    assume "?f B = ?s A"
    have "\<exists>C. (\<forall>(x, z)\<in>set_pmf C. \<exists>y. R x y \<and> S y z) \<and> ?f C = ?f A \<and> ?s C = ?s B"
      sorry }
oops
  then show "\<And>R::'a \<Rightarrow> 'b \<Rightarrow> bool. \<And>S::'b \<Rightarrow> 'c \<Rightarrow> bool. pmf_rel R OO pmf_rel S \<le> pmf_rel (R OO S)"
      by (auto simp add: subset_eq pmf_rel_def fun_eq_iff OO_def Ball_def)
qed (fact natLeq_card_order natLeq_cinfinite)+

notepad
begin
  fix x y :: "nat \<Rightarrow> real"
  def IJz \<equiv> "rec_nat ((0, 0), \<lambda>_. 0) (\<lambda>n ((I, J), z).
    let a = x I - (\<Sum>j<J. z (I, j)) ; b = y J - (\<Sum>i<I. z (i, J)) in
      ((if a \<le> b then I + 1 else I, if b \<le> a then J + 1 else J), z((I, J) := min a b)))"
  def I == "fst \<circ> fst \<circ> IJz" def J == "snd \<circ> fst \<circ> IJz" def z == "snd \<circ> IJz"
  let ?a = "\<lambda>n. x (I n) - (\<Sum>j<J n. z n (I n, j))" and ?b = "\<lambda>n. y (J n) - (\<Sum>i<I n. z n (i, J n))"
  have IJz_0[simp]: "\<And>p. z 0 p = 0" "I 0 = 0" "J 0 = 0"
    by (simp_all add: I_def J_def z_def IJz_def)
  have z_Suc[simp]: "\<And>n. z (Suc n) = (z n)((I n, J n) := min (?a n) (?b n))"
    by (simp add: z_def I_def J_def IJz_def Let_def split_beta)
  have I_Suc[simp]: "\<And>n. I (Suc n) = (if ?a n \<le> ?b n then I n + 1 else I n)"
    by (simp add: z_def I_def J_def IJz_def Let_def split_beta)
  have J_Suc[simp]: "\<And>n. J (Suc n) = (if ?b n \<le> ?a n then J n + 1 else J n)"
    by (simp add: z_def I_def J_def IJz_def Let_def split_beta)
  
  { fix N have "\<And>p. z N p \<noteq> 0 \<Longrightarrow> \<exists>n<N. p = (I n, J n)"
      by (induct N) (auto simp add: less_Suc_eq split: split_if_asm) }
  
  { fix i n assume "i < I n"
    then have "(\<Sum>j. z n (i, j)) = x i" 
    oops
*)

end

