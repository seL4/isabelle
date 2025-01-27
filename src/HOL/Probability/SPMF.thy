(* Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Discrete subprobability distribution\<close>

theory SPMF imports
  Probability_Mass_Function
  "HOL-Library.Complete_Partial_Order2"
  "HOL-Library.Rewrite"
begin

subsection \<open>Auxiliary material\<close>

lemma cSUP_singleton [simp]: "(SUP x\<in>{x}. f x :: _ :: conditionally_complete_lattice) = f x"
  by (metis cSup_singleton image_empty image_insert)

subsubsection \<open>More about extended reals\<close>

lemma [simp]:
  shows ennreal_max_0: "ennreal (max 0 x) = ennreal x"
    and ennreal_max_0': "ennreal (max x 0) = ennreal x"
  by(simp_all add: max_def ennreal_eq_0_iff)

lemma e2ennreal_0 [simp]: "e2ennreal 0 = 0"
  by(simp add: zero_ennreal_def)

lemma enn2real_bot [simp]: "enn2real \<bottom> = 0"
  by(simp add: bot_ennreal_def)

lemma continuous_at_ennreal[continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. ennreal (f x))"
  unfolding continuous_def by auto

lemma ennreal_Sup:
  assumes *: "(SUP a\<in>A. ennreal a) \<noteq> \<top>"
  and "A \<noteq> {}"
  shows "ennreal (Sup A) = (SUP a\<in>A. ennreal a)"
proof (rule continuous_at_Sup_mono)
  obtain r where r: "ennreal r = (SUP a\<in>A. ennreal a)" "r \<ge> 0"
    using * by(cases "(SUP a\<in>A. ennreal a)") simp_all
  then show "bdd_above A"
    by(auto intro!: SUP_upper bdd_aboveI[of _ r] simp add: ennreal_le_iff[symmetric])
qed (auto simp: mono_def continuous_at_imp_continuous_at_within continuous_at_ennreal ennreal_leI assms)

lemma ennreal_SUP:
  "\<lbrakk> (SUP a\<in>A. ennreal (f a)) \<noteq> \<top>; A \<noteq> {} \<rbrakk> \<Longrightarrow> ennreal (SUP a\<in>A. f a) = (SUP a\<in>A. ennreal (f a))"
  using ennreal_Sup[of "f ` A"] by (auto simp: image_comp)

lemma ennreal_lt_0: "x < 0 \<Longrightarrow> ennreal x = 0"
  by(simp add: ennreal_eq_0_iff)

subsubsection \<open>More about \<^typ>\<open>'a option\<close>\<close>

lemma None_in_map_option_image [simp]: "None \<in> map_option f ` A \<longleftrightarrow> None \<in> A"
  by auto

lemma Some_in_map_option_image [simp]: "Some x \<in> map_option f ` A \<longleftrightarrow> (\<exists>y. x = f y \<and> Some y \<in> A)"
  by (smt (verit, best) imageE imageI map_option_eq_Some)

lemma case_option_collapse: "case_option x (\<lambda>_. x) = (\<lambda>_. x)"
  by(simp add: fun_eq_iff split: option.split)

lemma case_option_id: "case_option None Some = id"
  by(rule ext)(simp split: option.split)

inductive ord_option :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> bool"
  for ord :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  None: "ord_option ord None x"
| Some: "ord x y \<Longrightarrow> ord_option ord (Some x) (Some y)"

inductive_simps ord_option_simps [simp]:
  "ord_option ord None x"
  "ord_option ord x None"
  "ord_option ord (Some x) (Some y)"
  "ord_option ord (Some x) None"

inductive_simps ord_option_eq_simps [simp]:
  "ord_option (=) None y"
  "ord_option (=) (Some x) y"

lemma ord_option_reflI: "(\<And>y. y \<in> set_option x \<Longrightarrow> ord y y) \<Longrightarrow> ord_option ord x x"
  by(cases x) simp_all

lemma reflp_ord_option: "reflp ord \<Longrightarrow> reflp (ord_option ord)"
  by(simp add: reflp_def ord_option_reflI)

lemma ord_option_trans:
  "\<lbrakk> ord_option ord x y; ord_option ord y z;
    \<And>a b c. \<lbrakk> a \<in> set_option x; b \<in> set_option y; c \<in> set_option z; ord a b; ord b c \<rbrakk> \<Longrightarrow> ord a c \<rbrakk>
  \<Longrightarrow> ord_option ord x z"
  by(auto elim!: ord_option.cases)

lemma transp_ord_option: "transp ord \<Longrightarrow> transp (ord_option ord)"
  unfolding transp_def by(blast intro: ord_option_trans)

lemma antisymp_ord_option: "antisymp ord \<Longrightarrow> antisymp (ord_option ord)"
  by(auto intro!: antisympI elim!: ord_option.cases dest: antisympD)

lemma ord_option_chainD:
  "Complete_Partial_Order.chain (ord_option ord) Y
  \<Longrightarrow> Complete_Partial_Order.chain ord {x. Some x \<in> Y}"
  by(rule chainI)(auto dest: chainD)

definition lub_option :: "('a set \<Rightarrow> 'b) \<Rightarrow> 'a option set \<Rightarrow> 'b option"
  where "lub_option lub Y = (if Y \<subseteq> {None} then None else Some (lub {x. Some x \<in> Y}))"

lemma map_lub_option: "map_option f (lub_option lub Y) = lub_option (f \<circ> lub) Y"
  by(simp add: lub_option_def)

lemma lub_option_upper:
  assumes "Complete_Partial_Order.chain (ord_option ord) Y" "x \<in> Y"
    and lub_upper: "\<And>Y x. \<lbrakk> Complete_Partial_Order.chain ord Y; x \<in> Y \<rbrakk> \<Longrightarrow> ord x (lub Y)"
  shows "ord_option ord x (lub_option lub Y)"
  using assms(1-2)
  by(cases x)(auto simp: lub_option_def intro: lub_upper[OF ord_option_chainD])

lemma lub_option_least:
  assumes Y: "Complete_Partial_Order.chain (ord_option ord) Y"
    and upper: "\<And>x. x \<in> Y \<Longrightarrow> ord_option ord x y"
  assumes lub_least: "\<And>Y y. \<lbrakk> Complete_Partial_Order.chain ord Y; \<And>x. x \<in> Y \<Longrightarrow> ord x y \<rbrakk> \<Longrightarrow> ord (lub Y) y"
  shows "ord_option ord (lub_option lub Y) y"
  using Y
  by(cases y)(auto 4 3 simp add: lub_option_def intro: lub_least[OF ord_option_chainD] dest: upper)

lemma lub_map_option: "lub_option lub (map_option f ` Y) = lub_option (lub \<circ> (`) f) Y"
proof -
  have "\<And>u y. \<lbrakk>Some u \<in> Y; y \<in> Y\<rbrakk> \<Longrightarrow> {f y |y. Some y \<in> Y} = f ` {x. Some x \<in> Y}"
    by blast
  then show ?thesis
    by (auto simp: lub_option_def)
qed

lemma ord_option_mono: "\<lbrakk> ord_option A x y; \<And>x y. A x y \<Longrightarrow> B x y \<rbrakk> \<Longrightarrow> ord_option B x y"
  by(auto elim: ord_option.cases)

lemma ord_option_mono' [mono]:
  "(\<And>x y. A x y \<longrightarrow> B x y) \<Longrightarrow> ord_option A x y \<longrightarrow> ord_option B x y"
  by(blast intro: ord_option_mono)

lemma ord_option_compp: "ord_option (A OO B) = ord_option A OO ord_option B"
  by(auto simp: fun_eq_iff elim!: ord_option.cases intro: ord_option.intros)

lemma ord_option_inf: "inf (ord_option A) (ord_option B) = ord_option (inf A B)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" by(auto elim!: ord_option.cases)
qed(auto elim: ord_option_mono)

lemma ord_option_map2: "ord_option ord x (map_option f y) = ord_option (\<lambda>x y. ord x (f y)) x y"
  by(auto elim: ord_option.cases)

lemma ord_option_map1: "ord_option ord (map_option f x) y = ord_option (\<lambda>x y. ord (f x) y) x y"
  by(auto elim: ord_option.cases)

lemma option_ord_Some1_iff: "option_ord (Some x) y \<longleftrightarrow> y = Some x"
  by(auto simp: flat_ord_def)

subsubsection \<open>A relator for sets that treats sets like predicates\<close>

context includes lifting_syntax
begin

definition rel_pred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "rel_pred R A B = (R ===> (=)) (\<lambda>x. x \<in> A) (\<lambda>y. y \<in> B)"

lemma rel_predI: "(R ===> (=)) (\<lambda>x. x \<in> A) (\<lambda>y. y \<in> B) \<Longrightarrow> rel_pred R A B"
  by(simp add: rel_pred_def)

lemma rel_predD: "\<lbrakk> rel_pred R A B; R x y \<rbrakk> \<Longrightarrow> x \<in> A \<longleftrightarrow> y \<in> B"
  by(simp add: rel_pred_def rel_fun_def)

lemma Collect_parametric: "((A ===> (=)) ===> rel_pred A) Collect Collect"
  \<comment> \<open>Declare this rule as @{attribute transfer_rule} only locally
      because it blows up the search space for @{method transfer}
      (in combination with @{thm [source] Collect_transfer})\<close>
  by(simp add: rel_funI rel_predI)

end

subsubsection \<open>Monotonicity rules\<close>

lemma monotone_gfp_eadd1: "monotone (\<ge>) (\<ge>) (\<lambda>x. x + y :: enat)"
  by(auto intro!: monotoneI)

lemma monotone_gfp_eadd2: "monotone (\<ge>) (\<ge>) (\<lambda>y. x + y :: enat)"
  by(auto intro!: monotoneI)

lemma mono2mono_gfp_eadd[THEN gfp.mono2mono2, cont_intro, simp]:
  shows monotone_eadd: "monotone (rel_prod (\<ge>) (\<ge>)) (\<ge>) (\<lambda>(x, y). x + y :: enat)"
  by(simp add: monotone_gfp_eadd1 monotone_gfp_eadd2)

lemma eadd_gfp_partial_function_mono [partial_function_mono]:
  "\<lbrakk> monotone (fun_ord (\<ge>)) (\<ge>) f; monotone (fun_ord (\<ge>)) (\<ge>) g \<rbrakk>
  \<Longrightarrow> monotone (fun_ord (\<ge>)) (\<ge>) (\<lambda>x. f x + g x :: enat)"
  by(rule mono2mono_gfp_eadd)

lemma mono2mono_ereal[THEN lfp.mono2mono]:
  shows monotone_ereal: "monotone (\<le>) (\<le>) ereal"
  by(rule monotoneI) simp

lemma mono2mono_ennreal[THEN lfp.mono2mono]:
  shows monotone_ennreal: "monotone (\<le>) (\<le>) ennreal"
  by(rule monotoneI)(simp add: ennreal_leI)

subsubsection \<open>Bijections\<close>

lemma bi_unique_rel_set_bij_betw:
  assumes unique: "bi_unique R"
  and rel: "rel_set R A B"
  shows "\<exists>f. bij_betw f A B \<and> (\<forall>x\<in>A. R x (f x))"
proof -
  from assms obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> R x (f x)" and B: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
    by (metis bi_unique_rel_set_lemma image_eqI)
  have "inj_on f A"
    by (metis (no_types, lifting) bi_unique_def f inj_on_def unique) 
  moreover have "f ` A = B" using rel
    by (smt (verit) bi_unique_def bi_unique_rel_set_lemma f image_cong unique)
  ultimately have "bij_betw f A B" unfolding bij_betw_def ..
  thus ?thesis using f by blast
qed

lemma bij_betw_rel_setD: "bij_betw f A B \<Longrightarrow> rel_set (\<lambda>x y. y = f x) A B"
  by(rule rel_setI)(auto dest: bij_betwE bij_betw_imp_surj_on[symmetric])

subsection \<open>Subprobability mass function\<close>

type_synonym 'a spmf = "'a option pmf"
translations (type) "'a spmf" \<leftharpoondown> (type) "'a option pmf"

definition measure_spmf :: "'a spmf \<Rightarrow> 'a measure"
  where "measure_spmf p = distr (restrict_space (measure_pmf p) (range Some)) (count_space UNIV) the"

abbreviation spmf :: "'a spmf \<Rightarrow> 'a \<Rightarrow> real"
  where "spmf p x \<equiv> pmf p (Some x)"

lemma space_measure_spmf: "space (measure_spmf p) = UNIV"
  by(simp add: measure_spmf_def)

lemma sets_measure_spmf [simp, measurable_cong]: "sets (measure_spmf p) = sets (count_space UNIV)"
  by(simp add: measure_spmf_def)

lemma measure_spmf_not_bot [simp]: "measure_spmf p \<noteq> \<bottom>"
  by (metis empty_not_UNIV space_bot space_measure_spmf)

lemma measurable_the_measure_pmf_Some [measurable, simp]:
  "the \<in> measurable (restrict_space (measure_pmf p) (range Some)) (count_space UNIV)"
  by(auto simp: measurable_def sets_restrict_space space_restrict_space integral_restrict_space)

lemma measurable_spmf_measure1[simp]: "measurable (measure_spmf M) N = UNIV \<rightarrow> space N"
  by(auto simp: measurable_def space_measure_spmf)

lemma measurable_spmf_measure2[simp]: "measurable N (measure_spmf M) = measurable N (count_space UNIV)"
  by(intro measurable_cong_sets) simp_all

lemma subprob_space_measure_spmf [simp, intro!]: "subprob_space (measure_spmf p)"
proof
  show "emeasure (measure_spmf p) (space (measure_spmf p)) \<le> 1"
    by(simp add: measure_spmf_def emeasure_distr emeasure_restrict_space space_restrict_space measure_pmf.measure_le_1)
qed(simp add: space_measure_spmf)

interpretation measure_spmf: subprob_space "measure_spmf p" for p
  by(rule subprob_space_measure_spmf)

lemma finite_measure_spmf [simp]: "finite_measure (measure_spmf p)"
  by unfold_locales

lemma spmf_conv_measure_spmf: "spmf p x = measure (measure_spmf p) {x}"
  by(auto simp: measure_spmf_def measure_distr measure_restrict_space pmf.rep_eq space_restrict_space intro: arg_cong2[where f=measure])

lemma emeasure_measure_spmf_conv_measure_pmf:
  "emeasure (measure_spmf p) A = emeasure (measure_pmf p) (Some ` A)"
  by(auto simp: measure_spmf_def emeasure_distr emeasure_restrict_space space_restrict_space intro: arg_cong2[where f=emeasure])

lemma measure_measure_spmf_conv_measure_pmf:
  "measure (measure_spmf p) A = measure (measure_pmf p) (Some ` A)"
  using emeasure_measure_spmf_conv_measure_pmf[of p A]
  by(simp add: measure_spmf.emeasure_eq_measure measure_pmf.emeasure_eq_measure)

lemma emeasure_spmf_map_pmf_Some [simp]:
  "emeasure (measure_spmf (map_pmf Some p)) A = emeasure (measure_pmf p) A"
  by(auto simp: measure_spmf_def emeasure_distr emeasure_restrict_space space_restrict_space intro: arg_cong2[where f=emeasure])

lemma measure_spmf_map_pmf_Some [simp]:
  "measure (measure_spmf (map_pmf Some p)) A = measure (measure_pmf p) A"
  using emeasure_spmf_map_pmf_Some[of p A] by(simp add: measure_spmf.emeasure_eq_measure measure_pmf.emeasure_eq_measure)

lemma nn_integral_measure_spmf: "(\<integral>\<^sup>+ x. f x \<partial>measure_spmf p) = \<integral>\<^sup>+ x. ennreal (spmf p x) * f x \<partial>count_space UNIV"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = \<integral>\<^sup>+ x. pmf p x * f (the x) \<partial>count_space (range Some)"
    by(simp add: measure_spmf_def nn_integral_distr nn_integral_restrict_space nn_integral_measure_pmf nn_integral_count_space_indicator ac_simps 
        flip: times_ereal.simps [symmetric])
  also have "\<dots> = \<integral>\<^sup>+ x. ennreal (spmf p (the x)) * f (the x) \<partial>count_space (range Some)"
    by(rule nn_integral_cong) auto
  also have "\<dots> = \<integral>\<^sup>+ x. spmf p (the (Some x)) * f (the (Some x)) \<partial>count_space UNIV"
    by(rule nn_integral_bij_count_space[symmetric])(simp add: bij_betw_def)
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed

lemma integral_measure_spmf:
  assumes "integrable (measure_spmf p) f"
  shows "(\<integral> x. f x \<partial>measure_spmf p) = \<integral> x. spmf p x * f x \<partial>count_space UNIV"
proof -
  have "integrable (count_space UNIV) (\<lambda>x. spmf p x * f x)"
    using assms by(simp add: integrable_iff_bounded nn_integral_measure_spmf abs_mult ennreal_mult'')
  then show ?thesis using assms
    by(simp add: real_lebesgue_integral_def nn_integral_measure_spmf ennreal_mult'[symmetric])
qed

lemma emeasure_spmf_single: "emeasure (measure_spmf p) {x} = spmf p x"
  by(simp add: measure_spmf.emeasure_eq_measure spmf_conv_measure_spmf)

lemma measurable_measure_spmf[measurable]:
  "(\<lambda>x. measure_spmf (M x)) \<in> measurable (count_space UNIV) (subprob_algebra (count_space UNIV))"
  by (auto simp: space_subprob_algebra)

lemma nn_integral_measure_spmf_conv_measure_pmf:
  assumes [measurable]: "f \<in> borel_measurable (count_space UNIV)"
  shows "nn_integral (measure_spmf p) f = nn_integral (restrict_space (measure_pmf p) (range Some)) (f \<circ> the)"
  by(simp add: measure_spmf_def nn_integral_distr o_def)

lemma measure_spmf_in_space_subprob_algebra [simp]:
  "measure_spmf p \<in> space (subprob_algebra (count_space UNIV))"
  by(simp add: space_subprob_algebra)

lemma nn_integral_spmf_neq_top: "(\<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV) \<noteq> \<top>"
  using nn_integral_measure_spmf[where f="\<lambda>_. 1", of p, symmetric] 
  by simp

lemma SUP_spmf_neq_top': "(SUP p\<in>Y. ennreal (spmf p x)) \<noteq> \<top>"
  by (metis SUP_least ennreal_le_1 ennreal_one_neq_top neq_top_trans pmf_le_1)

lemma SUP_spmf_neq_top: "(SUP i. ennreal (spmf (Y i) x)) \<noteq> \<top>"
  by (meson SUP_eq_top_iff ennreal_le_1 ennreal_one_less_top linorder_not_le pmf_le_1)

lemma SUP_emeasure_spmf_neq_top: "(SUP p\<in>Y. emeasure (measure_spmf p) A) \<noteq> \<top>"
  by (metis ennreal_one_less_top less_SUP_iff linorder_not_le measure_spmf.subprob_emeasure_le_1)

subsection \<open>Support\<close>

definition set_spmf :: "'a spmf \<Rightarrow> 'a set"
  where "set_spmf p = set_pmf p \<bind> set_option"

lemma set_spmf_rep_eq: "set_spmf p = {x. measure (measure_spmf p) {x} \<noteq> 0}"
proof -
  have "\<And>x :: 'a. the -` {x} \<inter> range Some = {Some x}" by auto
  then show ?thesis
    unfolding set_spmf_def measure_spmf_def
    by(auto simp: set_pmf.rep_eq  measure_distr measure_restrict_space space_restrict_space)
qed

lemma in_set_spmf: "x \<in> set_spmf p \<longleftrightarrow> Some x \<in> set_pmf p"
  by(simp add: set_spmf_def)

lemma AE_measure_spmf_iff [simp]: "(AE x in measure_spmf p. P x) \<longleftrightarrow> (\<forall>x\<in>set_spmf p. P x)"
  unfolding set_spmf_def measure_spmf_def
  by(force simp: AE_distr_iff AE_restrict_space_iff AE_measure_pmf_iff cong del: AE_cong)

lemma spmf_eq_0_set_spmf: "spmf p x = 0 \<longleftrightarrow> x \<notin> set_spmf p"
  by(auto simp: pmf_eq_0_set_pmf set_spmf_def)

lemma in_set_spmf_iff_spmf: "x \<in> set_spmf p \<longleftrightarrow> spmf p x \<noteq> 0"
  by(auto simp: set_spmf_def set_pmf_iff)

lemma set_spmf_return_pmf_None [simp]: "set_spmf (return_pmf None) = {}"
  by(auto simp: set_spmf_def)

lemma countable_set_spmf [simp]: "countable (set_spmf p)"
  by(simp add: set_spmf_def bind_UNION)

lemma spmf_eqI:
  assumes "\<And>i. spmf p i = spmf q i"
  shows "p = q"
proof(rule pmf_eqI)
  fix i
  show "pmf p i = pmf q i"
  proof(cases i)
    case (Some i')
    thus ?thesis by(simp add: assms)
  next
    case None
    have "ennreal (pmf p i) = measure (measure_pmf p) {i}" by(simp add: pmf_def)
    also have "{i} = space (measure_pmf p) - range Some"
      by(auto simp: None intro: ccontr)
    also have "measure (measure_pmf p) \<dots> = ennreal 1 - measure (measure_pmf p) (range Some)"
      by(simp add: measure_pmf.prob_compl ennreal_minus[symmetric] del: space_measure_pmf)
    also have "range Some = (\<Union>x\<in>set_spmf p. {Some x}) \<union> Some ` (- set_spmf p)"
      by auto
    also have "measure (measure_pmf p) \<dots> = measure (measure_pmf p) (\<Union>x\<in>set_spmf p. {Some x})"
      by(rule measure_pmf.measure_zero_union)(auto simp: measure_pmf.prob_eq_0 AE_measure_pmf_iff in_set_spmf_iff_spmf set_pmf_iff)
    also have "ennreal \<dots> = \<integral>\<^sup>+ x. measure (measure_pmf p) {Some x} \<partial>count_space (set_spmf p)"
      unfolding measure_pmf.emeasure_eq_measure[symmetric]
      by(simp_all add: emeasure_UN_countable disjoint_family_on_def)
    also have "\<dots> = \<integral>\<^sup>+ x. spmf p x \<partial>count_space (set_spmf p)" by(simp add: pmf_def)
    also have "\<dots> = \<integral>\<^sup>+ x. spmf q x \<partial>count_space (set_spmf p)" by(simp add: assms)
    also have "set_spmf p = set_spmf q" by(auto simp: in_set_spmf_iff_spmf assms)
    also have "(\<integral>\<^sup>+ x. spmf q x \<partial>count_space (set_spmf q)) = \<integral>\<^sup>+ x. measure (measure_pmf q) {Some x} \<partial>count_space (set_spmf q)"
      by(simp add: pmf_def)
    also have "\<dots> = measure (measure_pmf q) (\<Union>x\<in>set_spmf q. {Some x})"
      unfolding measure_pmf.emeasure_eq_measure[symmetric]
      by(simp_all add: emeasure_UN_countable disjoint_family_on_def)
    also have "\<dots> = measure (measure_pmf q) ((\<Union>x\<in>set_spmf q. {Some x}) \<union> Some ` (- set_spmf q))"
      by(rule ennreal_cong measure_pmf.measure_zero_union[symmetric])+(auto simp: measure_pmf.prob_eq_0 AE_measure_pmf_iff in_set_spmf_iff_spmf set_pmf_iff)
    also have "((\<Union>x\<in>set_spmf q. {Some x}) \<union> Some ` (- set_spmf q)) = range Some" by auto
    also have "ennreal 1 - measure (measure_pmf q) \<dots> = measure (measure_pmf q) (space (measure_pmf q) - range Some)"
      by(simp add: one_ereal_def measure_pmf.prob_compl ennreal_minus[symmetric] del: space_measure_pmf)
    also have "space (measure_pmf q) - range Some = {i}"
      by(auto simp: None intro: ccontr)
    also have "measure (measure_pmf q) \<dots> = pmf q i" by(simp add: pmf_def)
    finally show ?thesis by simp
  qed
qed

lemma integral_measure_spmf_restrict:
  fixes f ::  "'a \<Rightarrow> 'b :: {banach, second_countable_topology}"
  shows "(\<integral> x. f x \<partial>measure_spmf M) = (\<integral> x. f x \<partial>restrict_space (measure_spmf M) (set_spmf M))"
  by(auto intro!: integral_cong_AE simp add: integral_restrict_space)

lemma nn_integral_measure_spmf':
  "(\<integral>\<^sup>+ x. f x \<partial>measure_spmf p) = \<integral>\<^sup>+ x. ennreal (spmf p x) * f x \<partial>count_space (set_spmf p)"
  by(auto simp: nn_integral_measure_spmf nn_integral_count_space_indicator in_set_spmf_iff_spmf intro!: nn_integral_cong split: split_indicator)

subsection \<open>Functorial structure\<close>

abbreviation map_spmf :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a spmf \<Rightarrow> 'b spmf"
  where "map_spmf f \<equiv> map_pmf (map_option f)"

context begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "spmf")\<close>

lemma map_comp: "map_spmf f (map_spmf g p) = map_spmf (f \<circ> g) p"
  by(simp add: pmf.map_comp o_def option.map_comp)

lemma map_id0: "map_spmf id = id"
  by(simp add: pmf.map_id option.map_id0)

lemma map_id [simp]: "map_spmf id p = p"
  by(simp add: map_id0)

lemma map_ident [simp]: "map_spmf (\<lambda>x. x) p = p"
  by(simp add: id_def[symmetric])

end

lemma set_map_spmf [simp]: "set_spmf (map_spmf f p) = f ` set_spmf p"
  by(simp add: set_spmf_def image_bind bind_image o_def Option.option.set_map)

lemma map_spmf_cong:
  "\<lbrakk> p = q; \<And>x. x \<in> set_spmf q \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> map_spmf f p = map_spmf g q"
  by(auto intro: pmf.map_cong option.map_cong simp add: in_set_spmf)

lemma map_spmf_cong_simp:
  "\<lbrakk> p = q; \<And>x. x \<in> set_spmf q =simp=> f x = g x \<rbrakk>
  \<Longrightarrow> map_spmf f p = map_spmf g q"
  unfolding simp_implies_def by(rule map_spmf_cong)

lemma map_spmf_idI: "(\<And>x. x \<in> set_spmf p \<Longrightarrow> f x = x) \<Longrightarrow> map_spmf f p = p"
  by(rule map_pmf_idI map_option_idI)+(simp add: in_set_spmf)

lemma emeasure_map_spmf:
  "emeasure (measure_spmf (map_spmf f p)) A = emeasure (measure_spmf p) (f -` A)"
  by(auto simp: measure_spmf_def emeasure_distr measurable_restrict_space1 space_restrict_space emeasure_restrict_space intro: arg_cong2[where f=emeasure])

lemma measure_map_spmf: "measure (measure_spmf (map_spmf f p)) A = measure (measure_spmf p) (f -` A)"
  using emeasure_map_spmf[of f p A] by(simp add: measure_spmf.emeasure_eq_measure)

lemma measure_map_spmf_conv_distr:
  "measure_spmf (map_spmf f p) = distr (measure_spmf p) (count_space UNIV) f"
  by(rule measure_eqI)(simp_all add: emeasure_map_spmf emeasure_distr)

lemma spmf_map_pmf_Some [simp]: "spmf (map_pmf Some p) i = pmf p i"
  by(simp add: pmf_map_inj')

lemma spmf_map_inj: "\<lbrakk> inj_on f (set_spmf M); x \<in> set_spmf M \<rbrakk> \<Longrightarrow> spmf (map_spmf f M) (f x) = spmf M x"
  by (smt (verit) elem_set in_set_spmf inj_on_def option.inj_map_strong option.map(2) pmf_map_inj)

lemma spmf_map_inj': "inj f \<Longrightarrow> spmf (map_spmf f M) (f x) = spmf M x"
  by(subst option.map(2)[symmetric, where f=f])(rule pmf_map_inj'[OF option.inj_map])

lemma spmf_map_outside: "x \<notin> f ` set_spmf M \<Longrightarrow> spmf (map_spmf f M) x = 0"
  unfolding spmf_eq_0_set_spmf by simp

lemma ennreal_spmf_map: "ennreal (spmf (map_spmf f p) x) = emeasure (measure_spmf p) (f -` {x})"
  by (metis emeasure_map_spmf emeasure_spmf_single)

lemma spmf_map: "spmf (map_spmf f p) x = measure (measure_spmf p) (f -` {x})"
  using ennreal_spmf_map[of f p x] by(simp add: measure_spmf.emeasure_eq_measure)

lemma ennreal_spmf_map_conv_nn_integral:
  "ennreal (spmf (map_spmf f p) x) = integral\<^sup>N (measure_spmf p) (indicator (f -` {x}))"
  by (simp add: ennreal_spmf_map)

subsection \<open>Monad operations\<close>

subsubsection \<open>Return\<close>

abbreviation return_spmf :: "'a \<Rightarrow> 'a spmf"
  where "return_spmf x \<equiv> return_pmf (Some x)"

lemma pmf_return_spmf: "pmf (return_spmf x) y = indicator {y} (Some x)"
  by(fact pmf_return)

lemma measure_spmf_return_spmf: "measure_spmf (return_spmf x) = Giry_Monad.return (count_space UNIV) x"
  by(rule measure_eqI)(simp_all add: measure_spmf_def emeasure_distr space_restrict_space emeasure_restrict_space indicator_def)

lemma measure_spmf_return_pmf_None [simp]: "measure_spmf (return_pmf None) = null_measure (count_space UNIV)"
  by (simp add: emeasure_measure_spmf_conv_measure_pmf measure_eqI)

lemma set_return_spmf [simp]: "set_spmf (return_spmf x) = {x}"
  by(auto simp: set_spmf_def)

subsubsection \<open>Bind\<close>

definition bind_spmf :: "'a spmf \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'b spmf"
  where "bind_spmf x f = bind_pmf x (\<lambda>a. case a of None \<Rightarrow> return_pmf None | Some a' \<Rightarrow> f a')"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bind_spmf

lemma return_None_bind_spmf [simp]: "return_pmf None \<bind> (f :: 'a \<Rightarrow> _) = return_pmf None"
  by(simp add: bind_spmf_def bind_return_pmf)

lemma return_bind_spmf [simp]: "return_spmf x \<bind> f = f x"
  by(simp add: bind_spmf_def bind_return_pmf)

lemma bind_return_spmf [simp]: "x \<bind> return_spmf = x"
proof -
  have "\<And>a :: 'a option. (case a of None \<Rightarrow> return_pmf None | Some a' \<Rightarrow> return_spmf a') = return_pmf a"
    by(simp split: option.split)
  then show ?thesis
    by(simp add: bind_spmf_def bind_return_pmf')
qed

lemma bind_spmf_assoc [simp]:
  fixes x :: "'a spmf" and f :: "'a \<Rightarrow> 'b spmf" and g :: "'b \<Rightarrow> 'c spmf"
  shows "(x \<bind> f) \<bind> g = x \<bind> (\<lambda>y. f y \<bind> g)"
  unfolding bind_spmf_def
  by (smt (verit, best) bind_assoc_pmf bind_pmf_cong bind_return_pmf option.case_eq_if)

lemma pmf_bind_spmf_None: "pmf (p \<bind> f) None = pmf p None + \<integral> x. pmf (f x) None \<partial>measure_spmf p"
  (is "?lhs = ?rhs")
proof -
  let ?f = "\<lambda>x. pmf (case x of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) None"
  have "?lhs = \<integral> x. ?f x \<partial>measure_pmf p"
    by(simp add: bind_spmf_def pmf_bind)
  also have "\<dots> = \<integral> x. ?f None * indicator {None} x + ?f x * indicator (range Some) x \<partial>measure_pmf p"
    by(rule Bochner_Integration.integral_cong)(auto simp: indicator_def)
  also have "\<dots> = (\<integral> x. ?f None * indicator {None} x \<partial>measure_pmf p) + (\<integral> x. ?f x * indicator (range Some) x \<partial>measure_pmf p)"
    by(rule Bochner_Integration.integral_add)(auto 4 3 intro: integrable_real_mult_indicator measure_pmf.integrable_const_bound[where B=1] simp add: AE_measure_pmf_iff pmf_le_1)
  also have "\<dots> = pmf p None + \<integral> x. indicator (range Some) x * pmf (f (the x)) None \<partial>measure_pmf p"
    by(auto simp: measure_measure_pmf_finite indicator_eq_0_iff intro!: Bochner_Integration.integral_cong)
  also have "\<dots> = ?rhs" 
    unfolding measure_spmf_def
    by(subst integral_distr)(auto simp: integral_restrict_space)
  finally show ?thesis .
qed

lemma spmf_bind: "spmf (p \<bind> f) y = \<integral> x. spmf (f x) y \<partial>measure_spmf p"
proof -
  have "\<And>x. spmf (case x of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) y =
         indicat_real (range Some) x * spmf (f (the x)) y"
    by (simp add: split: option.split)
  then show ?thesis
    by (simp add: measure_spmf_def integral_distr bind_spmf_def pmf_bind integral_restrict_space)
qed

lemma ennreal_spmf_bind: "ennreal (spmf (p \<bind> f) x) = \<integral>\<^sup>+ y. spmf (f y) x \<partial>measure_spmf p"
proof -
  have "\<And>y. ennreal (spmf (case y of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) x) =
             ennreal (spmf (f (the y)) x) * indicator (range Some) y"
    by (simp add: split: option.split)
  then show ?thesis
    by (simp add: bind_spmf_def ennreal_pmf_bind nn_integral_measure_spmf_conv_measure_pmf nn_integral_restrict_space)
qed

lemma measure_spmf_bind_pmf: "measure_spmf (p \<bind> f) = measure_pmf p \<bind> measure_spmf \<circ> f"
  (is "?lhs = ?rhs")
proof(rule measure_eqI)
  show "sets ?lhs = sets ?rhs"
    by (simp add: Giry_Monad.bind_def)
next
  fix A :: "'a set"
  have "emeasure ?lhs A = \<integral>\<^sup>+ x. emeasure (measure_spmf (f x)) A \<partial>measure_pmf p"
    by(simp add: measure_spmf_def emeasure_distr space_restrict_space emeasure_restrict_space bind_spmf_def)
  also have "\<dots> = emeasure ?rhs A"
    by(simp add: emeasure_bind[where N="count_space UNIV"] space_measure_spmf space_subprob_algebra)
  finally show "emeasure ?lhs A = emeasure ?rhs A" .
qed

lemma measure_spmf_bind: "measure_spmf (p \<bind> f) = measure_spmf p \<bind> measure_spmf \<circ> f"
  (is "?lhs = ?rhs")
proof(rule measure_eqI)
  show "sets ?lhs = sets ?rhs"
    by(simp add: sets_bind[where N="count_space UNIV"] space_measure_spmf)
next
  fix A :: "'a set"
  let ?A = "the -` A \<inter> range Some"
  have "emeasure ?lhs A = \<integral>\<^sup>+ x. emeasure (measure_pmf (case x of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x)) ?A \<partial>measure_pmf p"
    by(simp add: measure_spmf_def emeasure_distr space_restrict_space emeasure_restrict_space bind_spmf_def)
  also have "\<dots> =  \<integral>\<^sup>+ x. emeasure (measure_pmf (f (the x))) ?A * indicator (range Some) x \<partial>measure_pmf p"
    by(rule nn_integral_cong)(auto split: option.split simp add: indicator_def)
  also have "\<dots> = \<integral>\<^sup>+ x. emeasure (measure_spmf (f x)) A \<partial>measure_spmf p"
    by(simp add: measure_spmf_def nn_integral_distr nn_integral_restrict_space emeasure_distr space_restrict_space emeasure_restrict_space)
  also have "\<dots> = emeasure ?rhs A"
    by(simp add: emeasure_bind[where N="count_space UNIV"] space_measure_spmf space_subprob_algebra)
  finally show "emeasure ?lhs A = emeasure ?rhs A" .
qed

lemma map_spmf_bind_spmf: "map_spmf f (bind_spmf p g) = bind_spmf p (map_spmf f \<circ> g)"
  by(auto simp: bind_spmf_def map_bind_pmf fun_eq_iff split: option.split intro: arg_cong2[where f=bind_pmf])

lemma bind_map_spmf: "map_spmf f p \<bind> g = p \<bind> g \<circ> f"
  by(simp add: bind_spmf_def bind_map_pmf o_def cong del: option.case_cong_weak)

lemma spmf_bind_leI:
  assumes "\<And>y. y \<in> set_spmf p \<Longrightarrow> spmf (f y) x \<le> r"
  and "0 \<le> r"
  shows "spmf (bind_spmf p f) x \<le> r"
proof -
  have "ennreal (spmf (bind_spmf p f) x) = \<integral>\<^sup>+ y. spmf (f y) x \<partial>measure_spmf p" 
    by(rule ennreal_spmf_bind)
  also have "\<dots> \<le> \<integral>\<^sup>+ y. r \<partial>measure_spmf p" 
    by(rule nn_integral_mono_AE)(simp add: assms)
  also have "\<dots> \<le> r" 
    using assms measure_spmf.emeasure_space_le_1
    by(auto simp: measure_spmf.emeasure_eq_measure intro!: mult_left_le)
  finally show ?thesis using assms(2) by(simp)
qed

lemma map_spmf_conv_bind_spmf: "map_spmf f p = (p \<bind> (\<lambda>x. return_spmf (f x)))"
  by(simp add: map_pmf_def bind_spmf_def)(rule bind_pmf_cong, simp_all split: option.split)

lemma bind_spmf_cong:
  "\<lbrakk> p = q; \<And>x. x \<in> set_spmf q \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> bind_spmf p f = bind_spmf q g"
  by(auto simp: bind_spmf_def in_set_spmf intro: bind_pmf_cong option.case_cong)

lemma bind_spmf_cong_simp:
  "\<lbrakk> p = q; \<And>x. x \<in> set_spmf q =simp=> f x = g x \<rbrakk>
  \<Longrightarrow> bind_spmf p f = bind_spmf q g"
  by(simp add: simp_implies_def cong: bind_spmf_cong)

lemma set_bind_spmf: "set_spmf (M \<bind> f) = set_spmf M \<bind> (set_spmf \<circ> f)"
  by(auto simp: set_spmf_def bind_spmf_def bind_UNION split: option.splits)

lemma bind_spmf_const_return_None [simp]: "bind_spmf p (\<lambda>_. return_pmf None) = return_pmf None"
  by(simp add: bind_spmf_def case_option_collapse)

lemma bind_commute_spmf:
  "bind_spmf p (\<lambda>x. bind_spmf q (f x)) = bind_spmf q (\<lambda>y. bind_spmf p (\<lambda>x. f x y))"
  (is "?lhs = ?rhs")
proof -
  let ?f = "\<lambda>x y. case x of None \<Rightarrow> return_pmf None | Some a \<Rightarrow> (case y of None \<Rightarrow> return_pmf None | Some b \<Rightarrow> f a b)"
  have "?lhs = p \<bind> (\<lambda>x. q \<bind> ?f x)"
    unfolding bind_spmf_def by(rule bind_pmf_cong[OF refl])(simp split: option.split)
  also have "\<dots> = q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. ?f x y))" by(rule bind_commute_pmf)
  also have "\<dots> = ?rhs" unfolding bind_spmf_def
    by(rule bind_pmf_cong[OF refl])(auto split: option.split, metis bind_spmf_const_return_None bind_spmf_def)
  finally show ?thesis .
qed

subsection \<open>Relator\<close>

abbreviation rel_spmf :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> 'b spmf \<Rightarrow> bool"
  where "rel_spmf R \<equiv> rel_pmf (rel_option R)"

lemma rel_spmf_mono:
  "\<lbrakk>rel_spmf A f g; \<And>x y. A x y \<Longrightarrow> B x y \<rbrakk> \<Longrightarrow> rel_spmf B f g"
  by (metis option.rel_sel pmf.rel_mono_strong)

lemma rel_spmf_mono_strong:
  "\<lbrakk> rel_spmf A f g; \<And>x y. \<lbrakk> A x y; x \<in> set_spmf f; y \<in> set_spmf g \<rbrakk> \<Longrightarrow> B x y \<rbrakk> \<Longrightarrow> rel_spmf B f g"
  by (metis elem_set in_set_spmf option.rel_mono_strong pmf.rel_mono_strong)

lemma rel_spmf_reflI: "(\<And>x. x \<in> set_spmf p \<Longrightarrow> P x x) \<Longrightarrow> rel_spmf P p p"
  by (metis (mono_tags, lifting) option.rel_eq pmf.rel_eq rel_spmf_mono_strong)

lemma rel_spmfI [intro?]:
  "\<lbrakk> \<And>x y. (x, y) \<in> set_spmf pq \<Longrightarrow> P x y; map_spmf fst pq = p; map_spmf snd pq = q \<rbrakk>
  \<Longrightarrow> rel_spmf P p q"
by(rule rel_pmf.intros[where pq="map_pmf (\<lambda>x. case x of None \<Rightarrow> (None, None) | Some (a, b) \<Rightarrow> (Some a, Some b)) pq"])
  (auto simp: pmf.map_comp o_def in_set_spmf split: option.splits intro: pmf.map_cong)

lemma rel_spmfE [elim?, consumes 1, case_names rel_spmf]:
  assumes "rel_spmf P p q"
  obtains pq where
    "\<And>x y. (x, y) \<in> set_spmf pq \<Longrightarrow> P x y"
    "p = map_spmf fst pq"
    "q = map_spmf snd pq"
  using assms
proof(cases rule: rel_pmf.cases[consumes 1, case_names rel_pmf])
  case (rel_pmf pq)
  let ?pq = "map_pmf (\<lambda>(a, b). case (a, b) of (Some x, Some y) \<Rightarrow> Some (x, y) | _ \<Rightarrow> None) pq"
  have "\<And>x y. (x, y) \<in> set_spmf ?pq \<Longrightarrow> P x y"
    by(auto simp: in_set_spmf split: option.split_asm dest: rel_pmf(1))
  moreover
  have "\<And>x. (x, None) \<in> set_pmf pq \<Longrightarrow> x = None" by(auto dest!: rel_pmf(1))
  then have "p = map_spmf fst ?pq" using rel_pmf(2)
    by(auto simp: pmf.map_comp split_beta intro!: pmf.map_cong split: option.split)
  moreover
  have "\<And>y. (None, y) \<in> set_pmf pq \<Longrightarrow> y = None" by(auto dest!: rel_pmf(1))
  then have "q = map_spmf snd ?pq" using rel_pmf(3)
    by(auto simp: pmf.map_comp split_beta intro!: pmf.map_cong split: option.split)
  ultimately show thesis ..
qed

lemma rel_spmf_simps:
  "rel_spmf R p q \<longleftrightarrow> (\<exists>pq. (\<forall>(x, y)\<in>set_spmf pq. R x y) \<and> map_spmf fst pq = p \<and> map_spmf snd pq = q)"
  by(auto intro: rel_spmfI elim!: rel_spmfE)

lemma spmf_rel_map:
  shows spmf_rel_map1: "\<And>R f x. rel_spmf R (map_spmf f x) = rel_spmf (\<lambda>x. R (f x)) x"
    and spmf_rel_map2: "\<And>R x g y. rel_spmf R x (map_spmf g y) = rel_spmf (\<lambda>x y. R x (g y)) x y"
  by(simp_all add: fun_eq_iff pmf.rel_map option.rel_map[abs_def])

lemma spmf_rel_conversep: "rel_spmf R\<inverse>\<inverse> = (rel_spmf R)\<inverse>\<inverse>"
  by(simp add: option.rel_conversep pmf.rel_conversep)

lemma spmf_rel_eq: "rel_spmf (=) = (=)"
  by(simp add: pmf.rel_eq option.rel_eq)

context includes lifting_syntax
begin

lemma bind_spmf_parametric [transfer_rule]:
  "(rel_spmf A ===> (A ===> rel_spmf B) ===> rel_spmf B) bind_spmf bind_spmf"
  unfolding bind_spmf_def[abs_def] by transfer_prover

lemma return_spmf_parametric: "(A ===> rel_spmf A) return_spmf return_spmf"
  by transfer_prover

lemma map_spmf_parametric: "((A ===> B) ===> rel_spmf A ===> rel_spmf B) map_spmf map_spmf"
  by transfer_prover

lemma rel_spmf_parametric:
  "((A ===> B ===> (=)) ===> rel_spmf A ===> rel_spmf B ===> (=)) rel_spmf rel_spmf"
  by transfer_prover

lemma set_spmf_parametric [transfer_rule]:
  "(rel_spmf A ===> rel_set A) set_spmf set_spmf"
  unfolding set_spmf_def[abs_def] by transfer_prover

lemma return_spmf_None_parametric:
  "(rel_spmf A) (return_pmf None) (return_pmf None)"
  by simp

end

lemma rel_spmf_bindI:
  "\<lbrakk> rel_spmf R p q; \<And>x y. R x y \<Longrightarrow> rel_spmf P (f x) (g y) \<rbrakk>
  \<Longrightarrow> rel_spmf P (p \<bind> f) (q \<bind> g)"
  by(fact bind_spmf_parametric[THEN rel_funD, THEN rel_funD, OF _ rel_funI])

lemma rel_spmf_bind_reflI:
  "(\<And>x. x \<in> set_spmf p \<Longrightarrow> rel_spmf P (f x) (g x)) \<Longrightarrow> rel_spmf P (p \<bind> f) (p \<bind> g)"
  by(rule rel_spmf_bindI[where R="\<lambda>x y. x = y \<and> x \<in> set_spmf p"])(auto intro: rel_spmf_reflI)

lemma rel_pmf_return_pmfI: "P x y \<Longrightarrow> rel_pmf P (return_pmf x) (return_pmf y)"
  by simp

context includes lifting_syntax
begin

text \<open>We do not yet have a relator for \<^typ>\<open>'a measure\<close>, so we combine \<^const>\<open>measure\<close> and \<^const>\<open>measure_pmf\<close>\<close>
lemma measure_pmf_parametric:
  "(rel_pmf A ===> rel_pred A ===> (=)) (\<lambda>p. measure (measure_pmf p)) (\<lambda>q. measure (measure_pmf q))"
proof(rule rel_funI)+
  fix p q X Y
  assume "rel_pmf A p q" and "rel_pred A X Y"
  from this(1) obtain pq where A: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> A x y"
    and p: "p = map_pmf fst pq" and q: "q = map_pmf snd pq" by cases auto
  show "measure p X = measure q Y" unfolding p q measure_map_pmf
    by(rule measure_pmf.finite_measure_eq_AE)(auto simp: AE_measure_pmf_iff dest!: A rel_predD[OF \<open>rel_pred _ _ _\<close>])
qed

lemma measure_spmf_parametric:
  "(rel_spmf A ===> rel_pred A ===> (=)) (\<lambda>p. measure (measure_spmf p)) (\<lambda>q. measure (measure_spmf q))"
proof -
  have "\<And>x y xa ya. rel_pred A xa ya \<Longrightarrow> rel_pred (rel_option A) (Some ` xa) (Some ` ya)"
    by(auto simp: rel_pred_def rel_fun_def elim: option.rel_cases)
  then show ?thesis
  unfolding measure_measure_spmf_conv_measure_pmf[abs_def]
  by (intro rel_funI) (force elim!: measure_pmf_parametric[THEN rel_funD, THEN rel_funD])
qed

end

subsection \<open>From \<^typ>\<open>'a pmf\<close> to \<^typ>\<open>'a spmf\<close>\<close>

definition spmf_of_pmf :: "'a pmf \<Rightarrow> 'a spmf"
  where "spmf_of_pmf = map_pmf Some"

lemma set_spmf_spmf_of_pmf [simp]: "set_spmf (spmf_of_pmf p) = set_pmf p"
  by(auto simp: spmf_of_pmf_def set_spmf_def bind_image o_def)

lemma spmf_spmf_of_pmf [simp]: "spmf (spmf_of_pmf p) x = pmf p x"
  by(simp add: spmf_of_pmf_def)

lemma pmf_spmf_of_pmf_None [simp]: "pmf (spmf_of_pmf p) None = 0"
  using ennreal_pmf_map[of Some p None] by(simp add: spmf_of_pmf_def)

lemma emeasure_spmf_of_pmf [simp]: "emeasure (measure_spmf (spmf_of_pmf p)) A = emeasure (measure_pmf p) A"
  by(simp add: emeasure_measure_spmf_conv_measure_pmf spmf_of_pmf_def inj_vimage_image_eq)

lemma measure_spmf_spmf_of_pmf [simp]: "measure_spmf (spmf_of_pmf p) = measure_pmf p"
  by(rule measure_eqI) simp_all

lemma map_spmf_of_pmf [simp]: "map_spmf f (spmf_of_pmf p) = spmf_of_pmf (map_pmf f p)"
  by(simp add: spmf_of_pmf_def pmf.map_comp o_def)

lemma rel_spmf_spmf_of_pmf [simp]: "rel_spmf R (spmf_of_pmf p) (spmf_of_pmf q) = rel_pmf R p q"
  by(simp add: spmf_of_pmf_def pmf.rel_map)

lemma spmf_of_pmf_return_pmf [simp]: "spmf_of_pmf (return_pmf x) = return_spmf x"
  by(simp add: spmf_of_pmf_def)

lemma bind_spmf_of_pmf [simp]: "bind_spmf (spmf_of_pmf p) f = bind_pmf p f"
  by(simp add: spmf_of_pmf_def bind_spmf_def bind_map_pmf)

lemma set_spmf_bind_pmf: "set_spmf (bind_pmf p f) = Set.bind (set_pmf p) (set_spmf \<circ> f)"
  unfolding bind_spmf_of_pmf[symmetric] by(subst set_bind_spmf) simp

lemma spmf_of_pmf_bind: "spmf_of_pmf (bind_pmf p f) = bind_pmf p (\<lambda>x. spmf_of_pmf (f x))"
  by(simp add: spmf_of_pmf_def map_bind_pmf)

lemma bind_pmf_return_spmf: "p \<bind> (\<lambda>x. return_spmf (f x)) = spmf_of_pmf (map_pmf f p)"
  by(simp add: map_pmf_def spmf_of_pmf_bind)

subsection \<open>Weight of a subprobability\<close>

abbreviation weight_spmf :: "'a spmf \<Rightarrow> real"
  where "weight_spmf p \<equiv> measure (measure_spmf p) (space (measure_spmf p))"

lemma weight_spmf_def: "weight_spmf p = measure (measure_spmf p) UNIV"
  by(simp add: space_measure_spmf)

lemma weight_spmf_le_1: "weight_spmf p \<le> 1"
  by(rule measure_spmf.subprob_measure_le_1)

lemma weight_return_spmf [simp]: "weight_spmf (return_spmf x) = 1"
  by(simp add: measure_spmf_return_spmf measure_return)

lemma weight_return_pmf_None [simp]: "weight_spmf (return_pmf None) = 0"
  by(simp)

lemma weight_map_spmf [simp]: "weight_spmf (map_spmf f p) = weight_spmf p"
  by(simp add: weight_spmf_def measure_map_spmf)

lemma weight_spmf_of_pmf [simp]: "weight_spmf (spmf_of_pmf p) = 1"
  by simp

lemma weight_spmf_nonneg: "weight_spmf p \<ge> 0"
  by(fact measure_nonneg)

lemma (in finite_measure) integrable_weight_spmf [simp]:
  "(\<lambda>x. weight_spmf (f x)) \<in> borel_measurable M \<Longrightarrow> integrable M (\<lambda>x. weight_spmf (f x))"
  by(rule integrable_const_bound[where B=1])(simp_all add: weight_spmf_nonneg weight_spmf_le_1)

lemma weight_spmf_eq_nn_integral_spmf: "weight_spmf p = \<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV"
  by (metis NO_MATCH_def measure_spmf.emeasure_eq_measure nn_integral_count_space_indicator nn_integral_indicator nn_integral_measure_spmf sets_UNIV sets_measure_spmf space_measure_spmf)

lemma weight_spmf_eq_nn_integral_support:
  "weight_spmf p = \<integral>\<^sup>+ x. spmf p x \<partial>count_space (set_spmf p)"
  unfolding weight_spmf_eq_nn_integral_spmf
  by(auto simp: nn_integral_count_space_indicator in_set_spmf_iff_spmf intro!: nn_integral_cong split: split_indicator)

lemma pmf_None_eq_weight_spmf: "pmf p None = 1 - weight_spmf p"
proof -
  have "weight_spmf p = \<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV" by(rule weight_spmf_eq_nn_integral_spmf)
  also have "\<dots> = \<integral>\<^sup>+ x. ennreal (pmf p x) * indicator (range Some) x \<partial>count_space UNIV"
    by(simp add: nn_integral_count_space_indicator[symmetric] embed_measure_count_space[symmetric] nn_integral_embed_measure measurable_embed_measure1)
  also have "\<dots> + pmf p None = \<integral>\<^sup>+ x. ennreal (pmf p x) * indicator (range Some) x + ennreal (pmf p None) * indicator {None} x \<partial>count_space UNIV"
    by(subst nn_integral_add)(simp_all add: max_def)
  also have "\<dots> = \<integral>\<^sup>+ x. pmf p x \<partial>count_space UNIV"
    by(rule nn_integral_cong)(auto split: split_indicator)
  also have "\<dots> = 1" by (simp add: nn_integral_pmf)
  finally show ?thesis by(simp add: ennreal_plus[symmetric] del: ennreal_plus)
qed

lemma weight_spmf_conv_pmf_None: "weight_spmf p = 1 - pmf p None"
  by(simp add: pmf_None_eq_weight_spmf)

lemma weight_spmf_lt_0: "\<not> weight_spmf p < 0"
  by(simp add: not_less weight_spmf_nonneg)

lemma spmf_le_weight: "spmf p x \<le> weight_spmf p"
  by (simp add: measure_spmf.bounded_measure spmf_conv_measure_spmf)

lemma weight_spmf_eq_0: "weight_spmf p = 0 \<longleftrightarrow> p = return_pmf None"
  by (metis measure_le_0_iff measure_spmf.bounded_measure spmf_conv_measure_spmf spmf_eqI weight_return_pmf_None)

lemma weight_bind_spmf: "weight_spmf (x \<bind> f) = lebesgue_integral (measure_spmf x) (weight_spmf \<circ> f)"
  unfolding weight_spmf_def
  by(simp add: measure_spmf_bind o_def measure_spmf.measure_bind[where N="count_space UNIV"])

lemma rel_spmf_weightD: "rel_spmf A p q \<Longrightarrow> weight_spmf p = weight_spmf q"
  by(erule rel_spmfE) simp

lemma rel_spmf_bij_betw:
  assumes f: "bij_betw f (set_spmf p) (set_spmf q)"
  and eq: "\<And>x. x \<in> set_spmf p \<Longrightarrow> spmf p x = spmf q (f x)"
  shows "rel_spmf (\<lambda>x y. f x = y) p q"
proof -
  let ?f = "map_option f"

  have weq: "ennreal (weight_spmf p) = ennreal (weight_spmf q)"
    unfolding weight_spmf_eq_nn_integral_support
    by(subst nn_integral_bij_count_space[OF f, symmetric])(rule nn_integral_cong_AE, simp add: eq AE_count_space)
  then have "None \<in> set_pmf p \<longleftrightarrow> None \<in> set_pmf q"
    by(simp add: pmf_None_eq_weight_spmf set_pmf_iff)
  with f have "bij_betw (map_option f) (set_pmf p) (set_pmf q)"
    apply(auto simp: bij_betw_def in_set_spmf inj_on_def intro: option.expand split: option.split)
    apply(rename_tac [!] x)
    apply(case_tac [!] x)
    apply(auto iff: in_set_spmf)
    done
  then have "rel_pmf (\<lambda>x y. ?f x = y) p q"
  proof (rule rel_pmf_bij_betw)
    show "pmf p x = pmf q (map_option f x)" if "x \<in> set_pmf p" for x
    proof (cases x)
      case None
      then show ?thesis
        by (metis ennreal_inj measure_nonneg option.map_disc_iff pmf_None_eq_weight_spmf weq)
    qed (use eq in_set_spmf that in force)
  qed
  thus ?thesis
    by (smt (verit, ccfv_SIG) None_eq_map_option_iff option.map_sel option.rel_sel pmf.rel_mono_strong) 
qed

subsection \<open>From density to spmfs\<close>

context fixes f :: "'a \<Rightarrow> real" begin

definition embed_spmf :: "'a spmf"
  where "embed_spmf = embed_pmf (\<lambda>x. case x of None \<Rightarrow> 1 - enn2real (\<integral>\<^sup>+ x. ennreal (f x) \<partial>count_space UNIV) | Some x' \<Rightarrow> max 0 (f x'))"

context
  assumes prob: "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>count_space UNIV) \<le> 1"
begin

lemma nn_integral_embed_spmf_eq_1:
  "(\<integral>\<^sup>+ x. ennreal (case x of None \<Rightarrow> 1 - enn2real (\<integral>\<^sup>+ x. ennreal (f x) \<partial>count_space UNIV) | Some x' \<Rightarrow> max 0 (f x')) \<partial>count_space UNIV) = 1"
  (is "?lhs = _" is "(\<integral>\<^sup>+ x. ?f x \<partial>?M) = _")
proof -
  have "?lhs = \<integral>\<^sup>+ x. ?f x * indicator {None} x + ?f x * indicator (range Some) x \<partial>?M"
    by(rule nn_integral_cong)(auto split: split_indicator)
  also have "\<dots> = (1 - enn2real (\<integral>\<^sup>+ x. ennreal (f x) \<partial>count_space UNIV)) + \<integral>\<^sup>+ x. ?f x * indicator (range Some) x \<partial>?M"
    (is "_ = ?None + ?Some")
    by(subst nn_integral_add)(simp_all add: AE_count_space max_def le_diff_eq real_le_ereal_iff one_ereal_def[symmetric] prob split: option.split)
  also have "?Some = \<integral>\<^sup>+ x. ?f x \<partial>count_space (range Some)"
    by(simp add: nn_integral_count_space_indicator)
  also have "count_space (range Some) = embed_measure (count_space UNIV) Some"
    by(simp add: embed_measure_count_space)
  also have "(\<integral>\<^sup>+ x. ?f x \<partial>\<dots>) = \<integral>\<^sup>+ x. ennreal (f x) \<partial>count_space UNIV"
    by(subst nn_integral_embed_measure)(simp_all add: measurable_embed_measure1)
  also have "?None + \<dots> = 1" using prob
    by(auto simp: ennreal_minus[symmetric] ennreal_1[symmetric] ennreal_enn2real_if top_unique simp del: ennreal_1)(simp add: diff_add_self_ennreal)
  finally show ?thesis .
qed

lemma pmf_embed_spmf_None: "pmf embed_spmf None = 1 - enn2real (\<integral>\<^sup>+ x. ennreal (f x) \<partial>count_space UNIV)"
unfolding embed_spmf_def
  by (smt (verit, del_insts) enn2real_leI ennreal_1 nn_integral_cong nn_integral_embed_spmf_eq_1
      option.case_eq_if pmf_embed_pmf prob)

lemma spmf_embed_spmf [simp]: "spmf embed_spmf x = max 0 (f x)"
  unfolding embed_spmf_def
  by (smt (verit, best) enn2real_leI ennreal_1 nn_integral_cong nn_integral_embed_spmf_eq_1 option.case_eq_if option.simps(5) pmf_embed_pmf prob)

end

end

lemma embed_spmf_K_0[simp]: "embed_spmf (\<lambda>_. 0) = return_pmf None" 
  by(rule spmf_eqI)(simp add: zero_ereal_def[symmetric])

subsection \<open>Ordering on spmfs\<close>

text \<open>
  \<^const>\<open>rel_pmf\<close> does not preserve a ccpo structure. Counterexample by Saheb-Djahromi:
  Take prefix order over \<open>bool llist\<close> and
  the set \<open>range (\<lambda>n :: nat. uniform (llist_n n))\<close> where \<open>llist_n\<close> is the set
  of all \<open>llist\<close>s of length \<open>n\<close> and \<open>uniform\<close> returns a uniform distribution over
  the given set. The set forms a chain in \<open>ord_pmf lprefix\<close>, but it has not an upper bound.
  Any upper bound may contain only infinite lists in its support because otherwise it is not greater
  than the \<open>n+1\<close>-st element in the chain where \<open>n\<close> is the length of the finite list.
  Moreover its support must contain all infinite lists, because otherwise there is a finite list
  all of whose finite extensions are not in the support - a contradiction to the upper bound property.
  Hence, the support is uncountable, but pmf's only have countable support.

  However, if all chains in the ccpo are finite, then it should preserve the ccpo structure.
\<close>

abbreviation ord_spmf :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> 'a spmf \<Rightarrow> bool"
  where "ord_spmf ord \<equiv> rel_pmf (ord_option ord)"

locale ord_spmf_syntax begin
notation ord_spmf (infix \<open>\<sqsubseteq>\<index>\<close> 60)
end

lemma ord_spmf_map_spmf1: "ord_spmf R (map_spmf f p) = ord_spmf (\<lambda>x. R (f x)) p"
  by(simp add: pmf.rel_map[abs_def] ord_option_map1[abs_def])

lemma ord_spmf_map_spmf2: "ord_spmf R p (map_spmf f q) = ord_spmf (\<lambda>x y. R x (f y)) p q"
  by(simp add: pmf.rel_map ord_option_map2)

lemma ord_spmf_map_spmf12: "ord_spmf R (map_spmf f p) (map_spmf f q) = ord_spmf (\<lambda>x y. R (f x) (f y)) p q"
  by(simp add: pmf.rel_map ord_option_map1[abs_def] ord_option_map2)

lemmas ord_spmf_map_spmf = ord_spmf_map_spmf1 ord_spmf_map_spmf2 ord_spmf_map_spmf12

context fixes ord :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (structure) begin
interpretation ord_spmf_syntax .

lemma ord_spmfI:
  "\<lbrakk> \<And>x y. (x, y) \<in> set_spmf pq \<Longrightarrow> ord x y; map_spmf fst pq = p; map_spmf snd pq = q \<rbrakk>
  \<Longrightarrow> p \<sqsubseteq> q"
  by(rule rel_pmf.intros[where pq="map_pmf (\<lambda>x. case x of None \<Rightarrow> (None, None) | Some (a, b) \<Rightarrow> (Some a, Some b)) pq"])
    (auto simp: pmf.map_comp o_def in_set_spmf split: option.splits intro: pmf.map_cong)

lemma ord_spmf_None [simp]: "return_pmf None \<sqsubseteq> x"
  by(rule rel_pmf.intros[where pq="map_pmf (Pair None) x"])(auto simp: pmf.map_comp o_def)

lemma ord_spmf_reflI: "(\<And>x. x \<in> set_spmf p \<Longrightarrow> ord x x) \<Longrightarrow> p \<sqsubseteq> p"
  by (metis elem_set in_set_spmf ord_option_reflI pmf.rel_refl_strong)

lemma rel_spmf_inf:
  assumes "p \<sqsubseteq> q"
  and "q \<sqsubseteq> p"
  and refl: "reflp ord"
  and trans: "transp ord"
  shows "rel_spmf (inf ord ord\<inverse>\<inverse>) p q"
proof -
  from \<open>p \<sqsubseteq> q\<close> \<open>q \<sqsubseteq> p\<close>
  have "rel_pmf (inf (ord_option ord) (ord_option ord)\<inverse>\<inverse>) p q"
    using local.refl local.trans reflp_ord_option rel_pmf_inf transp_ord_option by blast
  also have "inf (ord_option ord) (ord_option ord)\<inverse>\<inverse> = rel_option (inf ord ord\<inverse>\<inverse>)"
    by(auto simp: fun_eq_iff elim: ord_option.cases option.rel_cases)
  finally show ?thesis .
qed

end

lemma ord_spmf_return_spmf2: "ord_spmf R p (return_spmf y) \<longleftrightarrow> (\<forall>x\<in>set_spmf p. R x y)"
  by(auto simp: rel_pmf_return_pmf2 in_set_spmf ord_option.simps intro: ccontr)

lemma ord_spmf_mono: "\<lbrakk> ord_spmf A p q; \<And>x y. A x y \<Longrightarrow> B x y \<rbrakk> \<Longrightarrow> ord_spmf B p q"
  by(erule pmf.rel_mono_strong)(erule ord_option_mono)

lemma ord_spmf_compp: "ord_spmf (A OO B) = ord_spmf A OO ord_spmf B"
  by(simp add: ord_option_compp pmf.rel_compp)

lemma ord_spmf_bindI:
  assumes pq: "ord_spmf R p q"
    and fg: "\<And>x y. R x y \<Longrightarrow> ord_spmf P (f x) (g y)"
  shows "ord_spmf P (p \<bind> f) (q \<bind> g)"
  unfolding bind_spmf_def using pq
  by(rule rel_pmf_bindI)(auto split: option.split intro: fg)

lemma ord_spmf_bind_reflI:
  "(\<And>x. x \<in> set_spmf p \<Longrightarrow> ord_spmf R (f x) (g x)) \<Longrightarrow> ord_spmf R (p \<bind> f) (p \<bind> g)"
  by(rule ord_spmf_bindI[where R="\<lambda>x y. x = y \<and> x \<in> set_spmf p"])(auto intro: ord_spmf_reflI)

lemma ord_pmf_increaseI:
  assumes le: "\<And>x. spmf p x \<le> spmf q x"
  and refl: "\<And>x. x \<in> set_spmf p \<Longrightarrow> R x x"
  shows "ord_spmf R p q"
proof(rule rel_pmf.intros)
  define pq where "pq = embed_pmf
    (\<lambda>(x, y). case x of Some x' \<Rightarrow> (case y of Some y' \<Rightarrow> if x' = y' then spmf p x' else 0 | None \<Rightarrow> 0)
      | None \<Rightarrow> (case y of None \<Rightarrow> pmf q None | Some y' \<Rightarrow> spmf q y' - spmf p y'))"
     (is "_ = embed_pmf ?f")
  have nonneg: "\<And>xy. ?f xy \<ge> 0"
    by(clarsimp simp add: le field_simps split: option.split)
  have integral: "(\<integral>\<^sup>+ xy. ?f xy \<partial>count_space UNIV) = 1" (is "nn_integral ?M _ = _")
  proof -
    have "(\<integral>\<^sup>+ xy. ?f xy \<partial>count_space UNIV) =
      \<integral>\<^sup>+ xy. ennreal (?f xy) * indicator {(None, None)} xy +
             ennreal (?f xy) * indicator (range (\<lambda>x. (None, Some x))) xy +
             ennreal (?f xy) * indicator (range (\<lambda>x. (Some x, Some x))) xy \<partial>?M"
      by(rule nn_integral_cong)(auto split: split_indicator option.splits if_split_asm)
    also have "\<dots> = (\<integral>\<^sup>+ xy. ?f xy * indicator {(None, None)} xy \<partial>?M) +
        (\<integral>\<^sup>+ xy. ennreal (?f xy) * indicator (range (\<lambda>x. (None, Some x))) xy \<partial>?M) +
        (\<integral>\<^sup>+ xy. ennreal (?f xy) * indicator (range (\<lambda>x. (Some x, Some x))) xy \<partial>?M)"
      (is "_ = ?None + ?Some2 + ?Some")
      by(subst nn_integral_add)(simp_all add: nn_integral_add AE_count_space le_diff_eq le split: option.split)
    also have "?None = pmf q None" by simp
    also have "?Some2 = \<integral>\<^sup>+ x. ennreal (spmf q x) - spmf p x \<partial>count_space UNIV"
      by(simp add: nn_integral_count_space_indicator[symmetric] embed_measure_count_space[symmetric] inj_on_def nn_integral_embed_measure measurable_embed_measure1 ennreal_minus)
    also have "\<dots> = (\<integral>\<^sup>+ x. spmf q x \<partial>count_space UNIV) - (\<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV)"
      (is "_ = ?Some2' - ?Some2''")
      by(subst nn_integral_diff)(simp_all add: le nn_integral_spmf_neq_top)
    also have "?Some = \<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV"
      by(simp add: nn_integral_count_space_indicator[symmetric] embed_measure_count_space[symmetric] inj_on_def nn_integral_embed_measure measurable_embed_measure1)
    also have "pmf q None + (?Some2' - ?Some2'') + \<dots> = pmf q None + ?Some2'"
      by(auto simp: diff_add_self_ennreal le intro!: nn_integral_mono)
    also have "\<dots> = \<integral>\<^sup>+ x. ennreal (pmf q x) * indicator {None} x + ennreal (pmf q x) * indicator (range Some) x \<partial>count_space UNIV"
      by(subst nn_integral_add)(simp_all add: nn_integral_count_space_indicator[symmetric] embed_measure_count_space[symmetric] nn_integral_embed_measure measurable_embed_measure1)
    also have "\<dots> = \<integral>\<^sup>+ x. pmf q x \<partial>count_space UNIV"
      by(rule nn_integral_cong)(auto split: split_indicator)
    also have "\<dots> = 1" 
      by(simp add: nn_integral_pmf)
    finally show ?thesis .
  qed
  note f = nonneg integral

  { fix x y
    assume "(x, y) \<in> set_pmf pq"
    hence "?f (x, y) \<noteq> 0" unfolding pq_def by(simp add: set_embed_pmf[OF f])
    then show "ord_option R x y"
      by(simp add: spmf_eq_0_set_spmf refl split: option.split_asm if_split_asm) }

  have weight_le: "weight_spmf p \<le> weight_spmf q"
    by(subst ennreal_le_iff[symmetric])(auto simp: weight_spmf_eq_nn_integral_spmf intro!: nn_integral_mono le)

  show "map_pmf fst pq = p"
  proof(rule pmf_eqI)
    fix i :: "'a option"
    have bi: "bij_betw (Pair i) UNIV (fst -` {i})"
      by(auto simp: bij_betw_def inj_on_def)
    have "ennreal (pmf (map_pmf fst pq) i) = (\<integral>\<^sup>+ y. pmf pq (i, y) \<partial>count_space UNIV)"
      unfolding pq_def ennreal_pmf_map
      apply (simp add: embed_pmf.rep_eq[OF f] o_def emeasure_density flip: nn_integral_count_space_indicator)
      by (smt (verit, best) nn_integral_bij_count_space [OF bi] integral nn_integral_cong nonneg pmf_embed_pmf)
    also have "\<dots> = pmf p i"
    proof(cases i)
      case (Some x)
      have "(\<integral>\<^sup>+ y. pmf pq (Some x, y) \<partial>count_space UNIV) = \<integral>\<^sup>+ y. pmf p (Some x) * indicator {Some x} y \<partial>count_space UNIV"
        by(rule nn_integral_cong)(simp add: pq_def pmf_embed_pmf[OF f] split: option.split)
      then show ?thesis using Some by simp
    next
      case None
      have "(\<integral>\<^sup>+ y. pmf pq (None, y) \<partial>count_space UNIV) =
            (\<integral>\<^sup>+ y. ennreal (pmf pq (None, Some (the y))) * indicator (range Some) y +
                   ennreal (pmf pq (None, None)) * indicator {None} y \<partial>count_space UNIV)"
        by(rule nn_integral_cong)(auto split: split_indicator)
      also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (pmf pq (None, Some (the y))) \<partial>count_space (range Some)) + pmf pq (None, None)"
        by(subst nn_integral_add)(simp_all add: nn_integral_count_space_indicator)
      also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (spmf q y) - ennreal (spmf p y) \<partial>count_space UNIV) + pmf q None"
        by(simp add: pq_def pmf_embed_pmf[OF f] embed_measure_count_space[symmetric] nn_integral_embed_measure measurable_embed_measure1 ennreal_minus)
      also have "(\<integral>\<^sup>+ y. ennreal (spmf q y) - ennreal (spmf p y) \<partial>count_space UNIV) =
                 (\<integral>\<^sup>+ y. spmf q y \<partial>count_space UNIV) - (\<integral>\<^sup>+ y. spmf p y \<partial>count_space UNIV)"
        by(subst nn_integral_diff)(simp_all add: AE_count_space le nn_integral_spmf_neq_top split: split_indicator)
      also have "\<dots> = pmf p None - pmf q None"
        by(simp add: pmf_None_eq_weight_spmf weight_spmf_eq_nn_integral_spmf[symmetric] ennreal_minus)
      also have "\<dots> = ennreal (pmf p None) - ennreal (pmf q None)" by(simp add: ennreal_minus)
      finally show ?thesis using None weight_le
        by(auto simp: diff_add_self_ennreal pmf_None_eq_weight_spmf intro: ennreal_leI)
    qed
    finally show "pmf (map_pmf fst pq) i = pmf p i" by simp
  qed

  show "map_pmf snd pq = q"
  proof(rule pmf_eqI)
    fix i :: "'a option"
    have bi: "bij_betw (\<lambda>x. (x, i)) UNIV (snd -` {i})"
      by (auto simp: bij_betw_def inj_on_def)
    have "ennreal (pmf (map_pmf snd pq) i) = (\<integral>\<^sup>+ x. pmf pq (x, i) \<partial>count_space UNIV)"
      unfolding pq_def ennreal_pmf_map
      apply(simp add: embed_pmf.rep_eq[OF f] o_def emeasure_density nn_integral_count_space_indicator[symmetric])
      by (smt (verit, best) nn_integral_bij_count_space [OF bi] integral nn_integral_cong nonneg pmf_embed_pmf)
    also have "\<dots> = ennreal (pmf q i)"
    proof(cases i)
      case None
      have "(\<integral>\<^sup>+ x. pmf pq (x, None) \<partial>count_space UNIV) = \<integral>\<^sup>+ x. pmf q None * indicator {None :: 'a option} x \<partial>count_space UNIV"
        by(rule nn_integral_cong)(simp add: pq_def pmf_embed_pmf[OF f] split: option.split)
      then show ?thesis using None by simp
    next
      case (Some y)
      have "(\<integral>\<^sup>+ x. pmf pq (x, Some y) \<partial>count_space UNIV) =
        (\<integral>\<^sup>+ x. ennreal (pmf pq (x, Some y)) * indicator (range Some) x +
               ennreal (pmf pq (None, Some y)) * indicator {None} x \<partial>count_space UNIV)"
        by(rule nn_integral_cong)(auto split: split_indicator)
      also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (pmf pq (x, Some y)) * indicator (range Some) x \<partial>count_space UNIV) + pmf pq (None, Some y)"
        by(subst nn_integral_add)(simp_all)
      also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (spmf p y) * indicator {Some y} x \<partial>count_space UNIV) + (spmf q y - spmf p y)"
        by(auto simp: pq_def pmf_embed_pmf[OF f] one_ereal_def[symmetric] simp del: nn_integral_indicator_singleton intro!: arg_cong2[where f="(+)"] nn_integral_cong split: option.split)
      also have "\<dots> = spmf q y" by(simp add: ennreal_minus[symmetric] le)
      finally show ?thesis using Some by simp
    qed
    finally show "pmf (map_pmf snd pq) i = pmf q i" by simp
  qed
qed

lemma ord_spmf_eq_leD:
  assumes "ord_spmf (=) p q"
  shows "spmf p x \<le> spmf q x"
proof(cases "x \<in> set_spmf p")
  case False
  thus ?thesis by(simp add: in_set_spmf_iff_spmf)
next
  case True
  from assms obtain pq
    where pq: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> ord_option (=) x y"
    and p: "p = map_pmf fst pq"
    and q: "q = map_pmf snd pq" by cases auto
  have "ennreal (spmf p x) = integral\<^sup>N pq (indicator (fst -` {Some x}))"
    using p by(simp add: ennreal_pmf_map)
  also have "\<dots> = integral\<^sup>N pq (indicator {(Some x, Some x)})"
    by(rule nn_integral_cong_AE)(auto simp: AE_measure_pmf_iff split: split_indicator dest: pq)
  also have "\<dots> \<le> integral\<^sup>N pq (indicator (snd -` {Some x}))"
    by(rule nn_integral_mono) simp
  also have "\<dots> = ennreal (spmf q x)" using q by(simp add: ennreal_pmf_map)
  finally show ?thesis by simp
qed

lemma ord_spmf_eqD_set_spmf: "ord_spmf (=) p q \<Longrightarrow> set_spmf p \<subseteq> set_spmf q"
  by (metis ord_spmf_eq_leD pmf_le_0_iff spmf_eq_0_set_spmf subsetI)

lemma ord_spmf_eqD_emeasure:
  "ord_spmf (=) p q \<Longrightarrow> emeasure (measure_spmf p) A \<le> emeasure (measure_spmf q) A"
  by(auto intro!: nn_integral_mono split: split_indicator dest: ord_spmf_eq_leD simp add: nn_integral_measure_spmf nn_integral_indicator[symmetric])

lemma ord_spmf_eqD_measure_spmf: "ord_spmf (=) p q \<Longrightarrow> measure_spmf p \<le> measure_spmf q"
  by (subst le_measure) (auto simp: ord_spmf_eqD_emeasure)

subsection \<open>CCPO structure for the flat ccpo \<^term>\<open>ord_option (=)\<close>\<close>

context fixes Y :: "'a spmf set" begin

definition lub_spmf :: "'a spmf"
where "lub_spmf = embed_spmf (\<lambda>x. enn2real (SUP p \<in> Y. ennreal (spmf p x)))"
  \<comment> \<open>We go through \<^typ>\<open>ennreal\<close> to have a sensible definition even if \<^term>\<open>Y\<close> is empty.\<close>

lemma lub_spmf_empty [simp]: "SPMF.lub_spmf {} = return_pmf None"
  by(simp add: SPMF.lub_spmf_def bot_ereal_def)

context assumes chain: "Complete_Partial_Order.chain (ord_spmf (=)) Y" 
begin

lemma chain_ord_spmf_eqD: "Complete_Partial_Order.chain (\<le>) ((\<lambda>p x. ennreal (spmf p x)) ` Y)"
  (is "Complete_Partial_Order.chain _ (?f ` _)")
proof(rule chainI)
  fix f g
  assume "f \<in> ?f ` Y" "g \<in> ?f ` Y"
  then obtain p q where f: "f = ?f p" "p \<in> Y" and g: "g = ?f q" "q \<in> Y" by blast
  from chain \<open>p \<in> Y\<close> \<open>q \<in> Y\<close> have "ord_spmf (=) p q \<or> ord_spmf (=) q p" by(rule chainD)
  thus "f \<le> g \<or> g \<le> f"
    by (metis ennreal_leI f(1) g(1) le_funI ord_spmf_eq_leD)
qed

lemma ord_spmf_eq_pmf_None_eq:
  assumes le: "ord_spmf (=) p q"
  and None: "pmf p None = pmf q None"
  shows "p = q"
proof(rule spmf_eqI)
  fix i
  from le have le': "\<And>x. spmf p x \<le> spmf q x" by(rule ord_spmf_eq_leD)
  have "(\<integral>\<^sup>+ x. ennreal (spmf q x) - spmf p x \<partial>count_space UNIV) =
     (\<integral>\<^sup>+ x. spmf q x \<partial>count_space UNIV) - (\<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV)"
    by(subst nn_integral_diff)(simp_all add: AE_count_space le' nn_integral_spmf_neq_top)
  also have "\<dots> = (1 - pmf q None) - (1 - pmf p None)" unfolding pmf_None_eq_weight_spmf
    by(simp add: weight_spmf_eq_nn_integral_spmf[symmetric] ennreal_minus)
  also have "\<dots> = 0" using None by simp
  finally have "\<And>x. spmf q x \<le> spmf p x"
    by(simp add: nn_integral_0_iff_AE AE_count_space ennreal_minus ennreal_eq_0_iff)
  with le' show "spmf p i = spmf q i" by(rule antisym)
qed

lemma ord_spmf_eqD_pmf_None:
  assumes "ord_spmf (=) x y"
  shows "pmf x None \<ge> pmf y None"
  using assms
  apply cases
  apply(clarsimp simp only: ennreal_le_iff[symmetric, OF pmf_nonneg] ennreal_pmf_map)
  apply(fastforce simp: AE_measure_pmf_iff intro!: nn_integral_mono_AE)
  done

text \<open>
  Chains on \<^typ>\<open>'a spmf\<close> maintain countable support.
  Thanks to Johannes Hölzl for the proof idea.
\<close>
lemma spmf_chain_countable: "countable (\<Union>p\<in>Y. set_spmf p)"
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(cases "\<exists>x\<in>Y. \<forall>y\<in>Y. ord_spmf (=) y x")
    case True
    then obtain x where x: "x \<in> Y" and upper: "\<And>y. y \<in> Y \<Longrightarrow> ord_spmf (=) y x" by blast
    hence "(\<Union>x\<in>Y. set_spmf x) \<subseteq> set_spmf x" by(auto dest: ord_spmf_eqD_set_spmf)
    thus ?thesis by(rule countable_subset) simp
  next
    case False
    define N :: "'a option pmf \<Rightarrow> real" where "N p = pmf p None" for p

    have N_less_imp_le_spmf: "\<lbrakk> x \<in> Y; y \<in> Y; N y < N x \<rbrakk> \<Longrightarrow> ord_spmf (=) x y" for x y
      using chainD[OF chain, of x y] ord_spmf_eqD_pmf_None[of x y] ord_spmf_eqD_pmf_None[of y x]
      by (auto simp: N_def)
    have N_eq_imp_eq: "\<lbrakk> x \<in> Y; y \<in> Y; N y = N x \<rbrakk> \<Longrightarrow> x = y" for x y
      using chainD[OF chain, of x y] by(auto simp: N_def dest: ord_spmf_eq_pmf_None_eq)

    have NC: "N ` Y \<noteq> {}" "bdd_below (N ` Y)"
      using \<open>Y \<noteq> {}\<close> by(auto intro!: bdd_belowI[of _ 0] simp: N_def)
    have NC_less: "Inf (N ` Y) < N x" if "x \<in> Y" for x unfolding cInf_less_iff[OF NC]
    proof(rule ccontr)
      assume **: "\<not> (\<exists>y\<in>N ` Y. y < N x)"
      { fix y
        assume "y \<in> Y"
        with ** consider "N x < N y" | "N x = N y" by(auto simp: not_less le_less)
        hence "ord_spmf (=) y x" using \<open>y \<in> Y\<close> \<open>x \<in> Y\<close>
          by cases(auto dest: N_less_imp_le_spmf N_eq_imp_eq intro: ord_spmf_reflI) }
      with False \<open>x \<in> Y\<close> show False by blast
    qed

    from NC have "Inf (N ` Y) \<in> closure (N ` Y)" by (intro closure_contains_Inf)
    then obtain X' where "\<And>n. X' n \<in> N ` Y" and X': "X' \<longlonglongrightarrow> Inf (N ` Y)"
      unfolding closure_sequential by auto
    then obtain X where X: "\<And>n. X n \<in> Y" and "X' = (\<lambda>n. N (X n))" unfolding image_iff Bex_def by metis

    with X' have seq: "(\<lambda>n. N (X n)) \<longlonglongrightarrow> Inf (N ` Y)" by simp
    have "(\<Union>x \<in> Y. set_spmf x) \<subseteq> (\<Union>n. set_spmf (X n))"
    proof(rule UN_least)
      fix x
      assume "x \<in> Y"
      from order_tendstoD(2)[OF seq NC_less[OF \<open>x \<in> Y\<close>]]
      obtain i where "N (X i) < N x" by (auto simp: eventually_sequentially)
      thus "set_spmf x \<subseteq> (\<Union>n. set_spmf (X n))" using X \<open>x \<in> Y\<close>
        by(blast dest: N_less_imp_le_spmf ord_spmf_eqD_set_spmf)
    qed
    thus ?thesis by(rule countable_subset) simp
  qed
qed simp

lemma lub_spmf_subprob: "(\<integral>\<^sup>+ x. (SUP p \<in> Y. ennreal (spmf p x)) \<partial>count_space UNIV) \<le> 1"
proof(cases "Y = {}")
  case True
  thus ?thesis by(simp add: bot_ennreal)
next
  case False
  let ?B = "\<Union>p\<in>Y. set_spmf p"
  have countable: "countable ?B" by(rule spmf_chain_countable)

  have "(\<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x)) \<partial>count_space UNIV) =
        (\<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x) * indicator ?B x) \<partial>count_space UNIV)"
    by (intro nn_integral_cong arg_cong [of _ _ Sup]) (auto split: split_indicator simp add: spmf_eq_0_set_spmf)
  also have "\<dots> = (\<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x)) \<partial>count_space ?B)"
    unfolding ennreal_indicator[symmetric] using False
    by(subst SUP_mult_right_ennreal[symmetric])(simp add: ennreal_indicator nn_integral_count_space_indicator)
  also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ x. spmf p x \<partial>count_space ?B)" using False _ countable
    by(rule nn_integral_monotone_convergence_SUP_countable)(rule chain_ord_spmf_eqD)
  also have "\<dots> \<le> 1"
  proof(rule SUP_least)
    fix p
    assume "p \<in> Y"
    have "(\<integral>\<^sup>+ x. spmf p x \<partial>count_space ?B) = \<integral>\<^sup>+ x. ennreal (spmf p x) * indicator ?B x \<partial>count_space UNIV"
      by(simp add: nn_integral_count_space_indicator)
    also have "\<dots> = \<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV"
      by(rule nn_integral_cong)(auto split: split_indicator simp add: spmf_eq_0_set_spmf \<open>p \<in> Y\<close>)
    also have "\<dots> \<le> 1"
      by(simp add: weight_spmf_eq_nn_integral_spmf[symmetric] weight_spmf_le_1)
    finally show "(\<integral>\<^sup>+ x. spmf p x \<partial>count_space ?B) \<le> 1" .
  qed
  finally show ?thesis .
qed

lemma spmf_lub_spmf:
  assumes "Y \<noteq> {}"
  shows "spmf lub_spmf x = (SUP p \<in> Y. spmf p x)"
proof -
  from assms obtain p where "p \<in> Y" by auto
  have "spmf lub_spmf x = max 0 (enn2real (SUP p\<in>Y. ennreal (spmf p x)))" unfolding lub_spmf_def
    by(rule spmf_embed_spmf)(simp del: SUP_eq_top_iff Sup_eq_top_iff add: ennreal_enn2real_if SUP_spmf_neq_top' lub_spmf_subprob)
  also have "\<dots> = enn2real (SUP p\<in>Y. ennreal (spmf p x))"
    by(rule max_absorb2)(simp)
  also have "\<dots> = enn2real (ennreal (SUP p \<in> Y. spmf p x))" using assms
    by(subst ennreal_SUP[symmetric])(simp_all add: SUP_spmf_neq_top' del: SUP_eq_top_iff Sup_eq_top_iff)
  also have "0 \<le> (\<Squnion>p\<in>Y. spmf p x)" using assms
    by(auto intro!: cSUP_upper2 bdd_aboveI[where M=1] simp add: pmf_le_1)
  then have "enn2real (ennreal (SUP p \<in> Y. spmf p x)) = (SUP p \<in> Y. spmf p x)"
    by(rule enn2real_ennreal)
  finally show ?thesis .
qed

lemma ennreal_spmf_lub_spmf: "Y \<noteq> {} \<Longrightarrow> ennreal (spmf lub_spmf x) = (SUP p\<in>Y. ennreal (spmf p x))"
  by (metis SUP_spmf_neq_top' ennreal_SUP spmf_lub_spmf)

lemma lub_spmf_upper:
  assumes p: "p \<in> Y"
  shows "ord_spmf (=) p lub_spmf"
proof(rule ord_pmf_increaseI)
  fix x
  from p have [simp]: "Y \<noteq> {}" by auto
  from p have "ennreal (spmf p x) \<le> (SUP p\<in>Y. ennreal (spmf p x))" by(rule SUP_upper)
  also have "\<dots> = ennreal (spmf lub_spmf x)" using p
    by(subst spmf_lub_spmf)(auto simp: ennreal_SUP SUP_spmf_neq_top' simp del: SUP_eq_top_iff Sup_eq_top_iff)
  finally show "spmf p x \<le> spmf lub_spmf x" by simp
qed simp

lemma lub_spmf_least:
  assumes z: "\<And>x. x \<in> Y \<Longrightarrow> ord_spmf (=) x z"
  shows "ord_spmf (=) lub_spmf z"
proof(cases "Y = {}")
  case nonempty: False
  show ?thesis
  proof(rule ord_pmf_increaseI)
    fix x
    from nonempty obtain p where p: "p \<in> Y" by auto
    have "ennreal (spmf lub_spmf x) = (SUP p\<in>Y. ennreal (spmf p x))"
      by(subst spmf_lub_spmf)(auto simp: ennreal_SUP SUP_spmf_neq_top' nonempty simp del: SUP_eq_top_iff Sup_eq_top_iff)
    also have "\<dots> \<le> ennreal (spmf z x)" by(rule SUP_least)(simp add: ord_spmf_eq_leD z)
    finally show "spmf lub_spmf x \<le> spmf z x" by simp
  qed simp
qed simp

lemma set_lub_spmf: "set_spmf lub_spmf = (\<Union>p\<in>Y. set_spmf p)" (is "?lhs = ?rhs")
proof(cases "Y = {}")
  case [simp]: False
  show ?thesis
  proof(rule set_eqI)
    fix x
    have "x \<in> ?lhs \<longleftrightarrow> ennreal (spmf lub_spmf x) > 0"
      by(simp_all add: in_set_spmf_iff_spmf less_le)
    also have "\<dots> \<longleftrightarrow> (\<exists>p\<in>Y. ennreal (spmf p x) > 0)"
      by(simp add: ennreal_spmf_lub_spmf less_SUP_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> ?rhs"
      by(auto simp: in_set_spmf_iff_spmf less_le)
    finally show "x \<in> ?lhs \<longleftrightarrow> x \<in> ?rhs" .
  qed
qed simp

lemma emeasure_lub_spmf:
  assumes Y: "Y \<noteq> {}"
  shows "emeasure (measure_spmf lub_spmf) A = (SUP y\<in>Y. emeasure (measure_spmf y) A)"
  (is "?lhs = ?rhs")
proof -
  let ?M = "count_space (set_spmf lub_spmf)"
  have "?lhs = \<integral>\<^sup>+ x. ennreal (spmf lub_spmf x) * indicator A x \<partial>?M"
    by(auto simp: nn_integral_indicator[symmetric] nn_integral_measure_spmf')
  also have "\<dots> = \<integral>\<^sup>+ x. (SUP y\<in>Y. ennreal (spmf y x) * indicator A x) \<partial>?M"
    unfolding ennreal_indicator[symmetric]
    by(simp add: spmf_lub_spmf assms ennreal_SUP[OF SUP_spmf_neq_top'] SUP_mult_right_ennreal)
  also from assms have "\<dots> = (SUP y\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf y x) * indicator A x \<partial>?M)"
  proof(rule nn_integral_monotone_convergence_SUP_countable)
    have "(\<lambda>i x. ennreal (spmf i x) * indicator A x) ` Y = (\<lambda>f x. f x * indicator A x) ` (\<lambda>p x. ennreal (spmf p x)) ` Y"
      by(simp add: image_image)
    also have "Complete_Partial_Order.chain (\<le>) \<dots>" using chain_ord_spmf_eqD
      by(rule chain_imageI)(auto simp: le_fun_def split: split_indicator)
    finally show "Complete_Partial_Order.chain (\<le>) ((\<lambda>i x. ennreal (spmf i x) * indicator A x) ` Y)" .
  qed simp
  also have "\<dots> = (SUP y\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf y x) * indicator A x \<partial>count_space UNIV)"
    by(auto simp: nn_integral_count_space_indicator set_lub_spmf spmf_eq_0_set_spmf split: split_indicator intro!: arg_cong [of _ _ Sup] image_cong nn_integral_cong)
  also have "\<dots> = ?rhs"
    by(auto simp: nn_integral_indicator[symmetric] nn_integral_measure_spmf)
  finally show ?thesis .
qed

lemma measure_lub_spmf:
  assumes Y: "Y \<noteq> {}"
  shows "measure (measure_spmf lub_spmf) A = (SUP y\<in>Y. measure (measure_spmf y) A)" (is "?lhs = ?rhs")
proof -
  have "ennreal ?lhs = ennreal ?rhs"
    using emeasure_lub_spmf[OF assms] SUP_emeasure_spmf_neq_top[of A Y] Y
    unfolding measure_spmf.emeasure_eq_measure by(subst ennreal_SUP)
  moreover have "0 \<le> ?rhs" using Y
    by(auto intro!: cSUP_upper2 bdd_aboveI[where M=1] measure_spmf.subprob_measure_le_1)
  ultimately show ?thesis by(simp)
qed

lemma weight_lub_spmf:
  assumes Y: "Y \<noteq> {}"
  shows "weight_spmf lub_spmf = (SUP y\<in>Y. weight_spmf y)"
  by (smt (verit, best) SUP_cong assms measure_lub_spmf space_measure_spmf)

lemma measure_spmf_lub_spmf:
  assumes Y: "Y \<noteq> {}"
  shows "measure_spmf lub_spmf = (SUP p\<in>Y. measure_spmf p)" (is "?lhs = ?rhs")
proof(rule measure_eqI)
  from assms obtain p where p: "p \<in> Y" by auto
  from chain have chain': "Complete_Partial_Order.chain (\<le>) (measure_spmf ` Y)"
    by(rule chain_imageI)(rule ord_spmf_eqD_measure_spmf)
  show "sets ?lhs = sets ?rhs"
    using Y by (subst sets_SUP) auto
  show "emeasure ?lhs A = emeasure ?rhs A" for A
    using chain' Y p by (subst emeasure_SUP_chain) (auto simp:  emeasure_lub_spmf)
qed

end

end

lemma partial_function_definitions_spmf: "partial_function_definitions (ord_spmf (=)) lub_spmf"
  (is "partial_function_definitions ?R _")
proof
  fix x show "?R x x" by(simp add: ord_spmf_reflI)
next
  fix x y z
  assume "?R x y" "?R y z"
  with transp_ord_option[OF transp_equality] show "?R x z" by(rule transp_rel_pmf[THEN transpD])
next
  fix x y
  assume "?R x y" "?R y x"
  thus "x = y"
    by(rule rel_pmf_antisym)(simp_all add: reflp_ord_option transp_ord_option antisymp_ord_option)
next
  fix Y x
  assume "Complete_Partial_Order.chain ?R Y" "x \<in> Y"
  then show "?R x (lub_spmf Y)"
    by(rule lub_spmf_upper)
next
  fix Y z
  assume "Complete_Partial_Order.chain ?R Y" "\<And>x. x \<in> Y \<Longrightarrow> ?R x z"
  then show "?R (lub_spmf Y) z"
    by(cases "Y = {}")(simp_all add: lub_spmf_least)
qed

lemma ccpo_spmf: "class.ccpo lub_spmf (ord_spmf (=)) (mk_less (ord_spmf (=)))"
  by(metis ccpo partial_function_definitions_spmf)

interpretation spmf: partial_function_definitions "ord_spmf (=)" "lub_spmf"
  rewrites "lub_spmf {} \<equiv> return_pmf None"
  by(rule partial_function_definitions_spmf) simp

declaration \<open>Partial_Function.init "spmf" \<^term>\<open>spmf.fixp_fun\<close>
  \<^term>\<open>spmf.mono_body\<close> @{thm spmf.fixp_rule_uc} @{thm spmf.fixp_induct_uc}
  NONE\<close>

declare spmf.leq_refl[simp]
declare admissible_leI[OF ccpo_spmf, cont_intro]

abbreviation "mono_spmf \<equiv> monotone (fun_ord (ord_spmf (=))) (ord_spmf (=))"

lemma lub_spmf_const [simp]: "lub_spmf {p} = p"
  by(rule spmf_eqI)(simp add: spmf_lub_spmf[OF ccpo.chain_singleton[OF ccpo_spmf]])

lemma bind_spmf_mono':
  assumes fg: "ord_spmf (=) f g"
    and hk: "\<And>x :: 'a. ord_spmf (=) (h x) (k x)"
  shows "ord_spmf (=) (f \<bind> h) (g \<bind> k)"
  unfolding bind_spmf_def using assms(1)
  by(rule rel_pmf_bindI)(auto split: option.split simp add: hk)

lemma bind_spmf_mono [partial_function_mono]:
  assumes mf: "mono_spmf B" and mg: "\<And>y. mono_spmf (\<lambda>f. C y f)"
  shows "mono_spmf (\<lambda>f. bind_spmf (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b spmf"
  assume fg: "fun_ord (ord_spmf (=)) f g"
  with mf have "ord_spmf (=) (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  moreover from mg have "\<And>y'. ord_spmf (=) (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  ultimately show "ord_spmf (=) (bind_spmf (B f) (\<lambda>y. C y f)) (bind_spmf (B g) (\<lambda>y'. C y' g))"
    by(rule bind_spmf_mono')
qed

lemma monotone_bind_spmf1: "monotone (ord_spmf (=)) (ord_spmf (=)) (\<lambda>y. bind_spmf y g)"
  by(rule monotoneI)(simp add: bind_spmf_mono' ord_spmf_reflI)

lemma monotone_bind_spmf2:
  assumes g: "\<And>x. monotone ord (ord_spmf (=)) (\<lambda>y. g y x)"
  shows "monotone ord (ord_spmf (=)) (\<lambda>y. bind_spmf p (g y))"
  by(rule monotoneI)(auto intro: bind_spmf_mono' monotoneD[OF g] ord_spmf_reflI)

lemma bind_lub_spmf:
  assumes chain: "Complete_Partial_Order.chain (ord_spmf (=)) Y"
  shows "bind_spmf (lub_spmf Y) f = lub_spmf ((\<lambda>p. bind_spmf p f) ` Y)" (is "?lhs = ?rhs")
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p x. ennreal (spmf p x * spmf (f x) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp: le_fun_def dest: ord_spmf_eq_leD intro: mult_right_mono)
    have chain'': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. p \<bind> f) ` Y)"
      using chain by(rule chain_imageI)(auto intro!: monotoneI bind_spmf_mono' ord_spmf_reflI)
    let ?M = "count_space (set_spmf (lub_spmf Y))"
    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ x. ennreal (spmf (lub_spmf Y) x) * ennreal (spmf (f x) i) \<partial>?M"
      by(auto simp: ennreal_spmf_lub_spmf ennreal_spmf_bind nn_integral_measure_spmf')
    also have "\<dots> = \<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x * spmf (f x) i)) \<partial>?M"
      by(subst ennreal_spmf_lub_spmf[OF chain Y])(subst SUP_mult_right_ennreal, simp_all add: ennreal_mult Y)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf p x * spmf (f x) i) \<partial>?M)"
      using Y chain' by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf p f) i))"
      by(auto simp: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_indicator set_lub_spmf[OF chain] in_set_spmf_iff_spmf ennreal_mult intro!: arg_cong [of _ _ Sup] image_cong nn_integral_cong split: split_indicator)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'' by(simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp

lemma map_lub_spmf:
  "Complete_Partial_Order.chain (ord_spmf (=)) Y
  \<Longrightarrow> map_spmf f (lub_spmf Y) = lub_spmf (map_spmf f ` Y)"
  unfolding map_spmf_conv_bind_spmf[abs_def] by(simp add: bind_lub_spmf o_def)

lemma mcont_bind_spmf1: "mcont lub_spmf (ord_spmf (=)) lub_spmf (ord_spmf (=)) (\<lambda>y. bind_spmf y f)"
  using monotone_bind_spmf1
  by(intro contI mcontI) (auto simp: bind_lub_spmf)

lemma bind_lub_spmf2:
  assumes chain: "Complete_Partial_Order.chain ord Y"
    and g: "\<And>y. monotone ord (ord_spmf (=)) (g y)"
  shows "bind_spmf x (\<lambda>y. lub_spmf (g y ` Y)) = lub_spmf ((\<lambda>p. bind_spmf x (\<lambda>y. g y p)) ` Y)"
    (is "?lhs = ?rhs")
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "\<And>y. Complete_Partial_Order.chain (ord_spmf (=)) (g y ` Y)"
      using chain g[THEN monotoneD] by(rule chain_imageI)
    have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p y. ennreal (spmf x y * spmf (g y p) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp: le_fun_def dest: ord_spmf_eq_leD monotoneD[OF g] intro!: mult_left_mono)
    have chain''': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. bind_spmf x (\<lambda>y. g y p)) ` Y)"
      using chain by(rule chain_imageI)(rule monotone_bind_spmf2[OF g, THEN monotoneD])

    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ y. (SUP p\<in>Y. ennreal (spmf x y * spmf (g y p) i)) \<partial>count_space (set_spmf x)"
      by(simp add: ennreal_spmf_bind ennreal_spmf_lub_spmf[OF chain'] Y nn_integral_measure_spmf' SUP_mult_left_ennreal ennreal_mult image_comp)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ y. ennreal (spmf x y * spmf (g y p) i) \<partial>count_space (set_spmf x))"
      unfolding nn_integral_measure_spmf' using Y chain''
      by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf x (\<lambda>y. g y p)) i))"
      by(simp add: ennreal_spmf_bind nn_integral_measure_spmf' ennreal_mult)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'''
      by(auto simp: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp

lemma mcont_bind_spmf [cont_intro]:
  assumes f: "mcont luba orda lub_spmf (ord_spmf (=)) f"
  and g: "\<And>y. mcont luba orda lub_spmf (ord_spmf (=)) (g y)"
  shows "mcont luba orda lub_spmf (ord_spmf (=)) (\<lambda>x. bind_spmf (f x) (\<lambda>y. g y x))"
proof(rule spmf.mcont2mcont'[OF _ _ f])
  fix z
  show "mcont lub_spmf (ord_spmf (=)) lub_spmf (ord_spmf (=)) (\<lambda>x. bind_spmf x (\<lambda>y. g y z))"
    by(rule mcont_bind_spmf1)
next
  fix x
  let ?f = "\<lambda>z. bind_spmf x (\<lambda>y. g y z)"
  have "monotone orda (ord_spmf (=)) ?f" using mcont_mono[OF g] by(rule monotone_bind_spmf2)
  moreover have "cont luba orda lub_spmf (ord_spmf (=)) ?f"
  proof(rule contI)
    fix Y
    assume chain: "Complete_Partial_Order.chain orda Y" and Y: "Y \<noteq> {}"
    have "bind_spmf x (\<lambda>y. g y (luba Y)) = bind_spmf x (\<lambda>y. lub_spmf (g y ` Y))"
      by(rule bind_spmf_cong)(simp_all add: mcont_contD[OF g chain Y])
    also have "\<dots> = lub_spmf ((\<lambda>p. x \<bind> (\<lambda>y. g y p)) ` Y)" using chain
      by(rule bind_lub_spmf2)(rule mcont_mono[OF g])
    finally show "bind_spmf x (\<lambda>y. g y (luba Y)) = \<dots>" .
  qed
  ultimately show "mcont luba orda lub_spmf (ord_spmf (=)) ?f" by(rule mcontI)
qed

lemma bind_pmf_mono [partial_function_mono]:
  "(\<And>y. mono_spmf (\<lambda>f. C y f)) \<Longrightarrow> mono_spmf (\<lambda>f. bind_pmf p (\<lambda>x. C x f))"
  using bind_spmf_mono[of "\<lambda>_. spmf_of_pmf p" C] by simp

lemma map_spmf_mono [partial_function_mono]: "mono_spmf B \<Longrightarrow> mono_spmf (\<lambda>g. map_spmf f (B g))"
  unfolding map_spmf_conv_bind_spmf by(rule bind_spmf_mono) simp_all

lemma mcont_map_spmf [cont_intro]:
  "mcont luba orda lub_spmf (ord_spmf (=)) g
  \<Longrightarrow> mcont luba orda lub_spmf (ord_spmf (=)) (\<lambda>x. map_spmf f (g x))"
  unfolding map_spmf_conv_bind_spmf by(rule mcont_bind_spmf) simp_all

lemma monotone_set_spmf: "monotone (ord_spmf (=)) (\<subseteq>) set_spmf"
  by(rule monotoneI)(rule ord_spmf_eqD_set_spmf)

lemma cont_set_spmf: "cont lub_spmf (ord_spmf (=)) Union (\<subseteq>) set_spmf"
  by(rule contI)(subst set_lub_spmf; simp)

lemma mcont2mcont_set_spmf[THEN mcont2mcont, cont_intro]:
  shows mcont_set_spmf: "mcont lub_spmf (ord_spmf (=)) Union (\<subseteq>) set_spmf"
  by(rule mcontI monotone_set_spmf cont_set_spmf)+

lemma monotone_spmf: "monotone (ord_spmf (=)) (\<le>) (\<lambda>p. spmf p x)"
  by(rule monotoneI)(simp add: ord_spmf_eq_leD)

lemma cont_spmf: "cont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p. spmf p x)"
  by(rule contI)(simp add: spmf_lub_spmf)

lemma mcont_spmf: "mcont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p. spmf p x)"
  by(metis mcontI monotone_spmf cont_spmf)

lemma cont_ennreal_spmf: "cont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p. ennreal (spmf p x))"
  by(rule contI)(simp add: ennreal_spmf_lub_spmf)

lemma mcont2mcont_ennreal_spmf [THEN mcont2mcont, cont_intro]:
  shows mcont_ennreal_spmf: "mcont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p. ennreal (spmf p x))"
  by(metis mcontI mono2mono_ennreal monotone_spmf cont_ennreal_spmf)

lemma nn_integral_map_spmf [simp]: "nn_integral (measure_spmf (map_spmf f p)) g = nn_integral (measure_spmf p) (g \<circ> f)"
  by(force simp: measure_spmf_def nn_integral_distr nn_integral_restrict_space intro: nn_integral_cong split: split_indicator)

subsubsection \<open>Admissibility of \<^term>\<open>rel_spmf\<close>\<close>

lemma rel_spmf_measureD:
  assumes "rel_spmf R p q"
  shows "measure (measure_spmf p) A \<le> measure (measure_spmf q) {y. \<exists>x\<in>A. R x y}" (is "?lhs \<le> ?rhs")
proof -
  have "?lhs = measure (measure_pmf p) (Some ` A)" by(simp add: measure_measure_spmf_conv_measure_pmf)
  also have "\<dots> \<le> measure (measure_pmf q) {y. \<exists>x\<in>Some ` A. rel_option R x y}"
    using assms by(rule rel_pmf_measureD)
  also have "\<dots> = ?rhs" unfolding measure_measure_spmf_conv_measure_pmf
    by(rule arg_cong2[where f=measure])(auto simp: option_rel_Some1)
  finally show ?thesis .
qed

locale rel_spmf_characterisation =
  assumes rel_pmf_measureI:
    "\<And>(R :: 'a option \<Rightarrow> 'b option \<Rightarrow> bool) p q.
    (\<And>A. measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y})
    \<Longrightarrow> rel_pmf R p q"
  \<comment> \<open>This assumption is shown to hold in general in the AFP entry \<open>MFMC_Countable\<close>.\<close>
begin

context fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" begin

lemma rel_spmf_measureI:
  assumes eq1: "\<And>A. measure (measure_spmf p) A \<le> measure (measure_spmf q) {y. \<exists>x\<in>A. R x y}"
  assumes eq2: "weight_spmf q \<le> weight_spmf p"
  shows "rel_spmf R p q"
proof(rule rel_pmf_measureI)
  fix A :: "'a option set"
  define A' where "A' = the ` (A \<inter> range Some)"
  define A'' where "A'' = A \<inter> {None}"
  have A: "A = Some ` A' \<union> A''" "Some ` A' \<inter> A'' = {}"
    unfolding A'_def A''_def by(auto simp: image_iff)
  have "measure (measure_pmf p) A = measure (measure_pmf p) (Some ` A') + measure (measure_pmf p) A''"
    by(simp add: A measure_pmf.finite_measure_Union)
  also have "measure (measure_pmf p) (Some ` A') = measure (measure_spmf p) A'"
    by(simp add: measure_measure_spmf_conv_measure_pmf)
  also have "\<dots> \<le> measure (measure_spmf q) {y. \<exists>x\<in>A'. R x y}" by(rule eq1)
  also (ord_eq_le_trans[OF _ add_right_mono])
  have "\<dots> = measure (measure_pmf q) {y. \<exists>x\<in>A'. rel_option R (Some x) y}"
    unfolding measure_measure_spmf_conv_measure_pmf
    by(rule arg_cong2[where f=measure])(auto simp: A'_def option_rel_Some1)
  also
  { have "weight_spmf p \<le> measure (measure_spmf q) {y. \<exists>x. R x y}"
      using eq1[of UNIV] unfolding weight_spmf_def by simp
    also have "\<dots> \<le> weight_spmf q" unfolding weight_spmf_def
      by(rule measure_spmf.finite_measure_mono) simp_all
    finally have "weight_spmf p = weight_spmf q" using eq2 by simp }
  then have "measure (measure_pmf p) A'' = measure (measure_pmf q) (if None \<in> A then {None} else {})"
    unfolding A''_def by(simp add: pmf_None_eq_weight_spmf measure_pmf_single)
  also have "measure (measure_pmf q) {y. \<exists>x\<in>A'. rel_option R (Some x) y} + \<dots> = measure (measure_pmf q) {y. \<exists>x\<in>A. rel_option R x y}"
    by(subst measure_pmf.finite_measure_Union[symmetric])
      (auto 4 3 intro!: arg_cong2[where f=measure] simp add: option_rel_Some1 option_rel_Some2 A'_def intro: rev_bexI elim: option.rel_cases)
  finally show "measure (measure_pmf p) A \<le> \<dots>" .
qed

lemma admissible_rel_spmf:
  "ccpo.admissible (prod_lub lub_spmf lub_spmf) (rel_prod (ord_spmf (=)) (ord_spmf (=))) (case_prod (rel_spmf R))"
  (is "ccpo.admissible ?lub ?ord ?P")
proof(rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and R: "\<forall>(p, q) \<in> Y. rel_spmf R p q"
  from R have R: "\<And>p q. (p, q) \<in> Y \<Longrightarrow> rel_spmf R p q" by auto
  have chain1: "Complete_Partial_Order.chain (ord_spmf (=)) (fst ` Y)"
    and chain2: "Complete_Partial_Order.chain (ord_spmf (=)) (snd ` Y)"
    using chain by(rule chain_imageI; clarsimp)+
  from Y have Y1: "fst ` Y \<noteq> {}" and Y2: "snd ` Y \<noteq> {}" by auto

  have "rel_spmf R (lub_spmf (fst ` Y)) (lub_spmf (snd ` Y))"
  proof(rule rel_spmf_measureI)
    show "weight_spmf (lub_spmf (snd ` Y)) \<le> weight_spmf (lub_spmf (fst ` Y))"
      by(auto simp: weight_lub_spmf chain1 chain2 Y rel_spmf_weightD[OF R, symmetric] intro!: cSUP_least intro: cSUP_upper2[OF bdd_aboveI2[OF weight_spmf_le_1]])

    fix A
    have "measure (measure_spmf (lub_spmf (fst ` Y))) A = (SUP y\<in>fst ` Y. measure (measure_spmf y) A)"
      using chain1 Y1 by(rule measure_lub_spmf)
    also have "\<dots> \<le> (SUP y\<in>snd ` Y. measure (measure_spmf y) {y. \<exists>x\<in>A. R x y})" using Y1
      by(rule cSUP_least)(auto intro!: cSUP_upper2[OF bdd_aboveI2[OF measure_spmf.subprob_measure_le_1]] rel_spmf_measureD R)
    also have "\<dots> = measure (measure_spmf (lub_spmf (snd ` Y))) {y. \<exists>x\<in>A. R x y}"
      using chain2 Y2 by(rule measure_lub_spmf[symmetric])
    finally show "measure (measure_spmf (lub_spmf (fst ` Y))) A \<le> \<dots>" .
  qed
  then show "?P (?lub Y)" by(simp add: prod_lub_def)
qed

lemma admissible_rel_spmf_mcont [cont_intro]:
  "\<lbrakk> mcont lub ord lub_spmf (ord_spmf (=)) f; mcont lub ord lub_spmf (ord_spmf (=)) g \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. rel_spmf R (f x) (g x))"
  by(rule admissible_subst[OF admissible_rel_spmf, where f="\<lambda>x. (f x, g x)", simplified])(rule mcont_Pair)

context includes lifting_syntax
begin

lemma fixp_spmf_parametric':
  assumes f: "\<And>x. monotone (ord_spmf (=)) (ord_spmf (=)) F"
    and g: "\<And>x. monotone (ord_spmf (=)) (ord_spmf (=)) G"
    and param: "(rel_spmf R ===> rel_spmf R) F G"
  shows "(rel_spmf R) (ccpo.fixp lub_spmf (ord_spmf (=)) F) (ccpo.fixp lub_spmf (ord_spmf (=)) G)"
  by(rule parallel_fixp_induct[OF ccpo_spmf ccpo_spmf _ f g])(auto intro: param[THEN rel_funD])

lemma fixp_spmf_parametric:
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_spmf (\<lambda>f. G f x)"
  and param: "((A ===> rel_spmf R) ===> A ===> rel_spmf R) F G"
  shows "(A ===> rel_spmf R) (spmf.fixp_fun F) (spmf.fixp_fun G)"
using f g
proof(rule parallel_fixp_induct_1_1[OF partial_function_definitions_spmf partial_function_definitions_spmf _ _ reflexive reflexive, where P="(A ===> rel_spmf R)"])
  show "ccpo.admissible (prod_lub (fun_lub lub_spmf) (fun_lub lub_spmf)) (rel_prod (fun_ord (ord_spmf (=))) (fun_ord (ord_spmf (=)))) (\<lambda>x. (A ===> rel_spmf R) (fst x) (snd x))"
    unfolding rel_fun_def
    by(fastforce intro: admissible_all admissible_imp admissible_rel_spmf_mcont)
  show "(A ===> rel_spmf R) (\<lambda>_. lub_spmf {}) (\<lambda>_. lub_spmf {})" 
    by auto
  show "(A ===> rel_spmf R) (F f) (G g)" if "(A ===> rel_spmf R) f g" for f g
    using that by(rule rel_funD[OF param])
qed

end

end

end

subsection \<open>Restrictions on spmfs\<close>

definition restrict_spmf :: "'a spmf \<Rightarrow> 'a set \<Rightarrow> 'a spmf" (infixl \<open>\<upharpoonleft>\<close> 110)
  where "p \<upharpoonleft> A = map_pmf (\<lambda>x. x \<bind> (\<lambda>y. if y \<in> A then Some y else None)) p"

lemma set_restrict_spmf [simp]: "set_spmf (p \<upharpoonleft> A) = set_spmf p \<inter> A"
  by(fastforce simp: restrict_spmf_def set_spmf_def split: bind_splits if_split_asm)

lemma restrict_map_spmf: "map_spmf f p \<upharpoonleft> A = map_spmf f (p \<upharpoonleft> (f -` A))"
  by(simp add: restrict_spmf_def pmf.map_comp o_def map_option_bind bind_map_option if_distrib cong del: if_weak_cong)

lemma restrict_restrict_spmf [simp]: "p \<upharpoonleft> A \<upharpoonleft> B = p \<upharpoonleft> (A \<inter> B)"
  by(auto simp: restrict_spmf_def pmf.map_comp o_def intro!: pmf.map_cong bind_option_cong)

lemma restrict_spmf_empty [simp]: "p \<upharpoonleft> {} = return_pmf None"
  by(simp add: restrict_spmf_def)

lemma restrict_spmf_UNIV [simp]: "p \<upharpoonleft> UNIV = p"
  by(simp add: restrict_spmf_def)

lemma spmf_restrict_spmf_outside [simp]: "x \<notin> A \<Longrightarrow> spmf (p \<upharpoonleft> A) x = 0"
  by(simp add: spmf_eq_0_set_spmf)

lemma emeasure_restrict_spmf [simp]: "emeasure (measure_spmf (p \<upharpoonleft> A)) X = emeasure (measure_spmf p) (X \<inter> A)"
proof -
  have "(\<lambda>x. x \<bind> (\<lambda>y. if y \<in> A then Some y else None)) -` the -` X \<inter>
        (\<lambda>x. x \<bind> (\<lambda>y. if y \<in> A then Some y else None)) -` range Some =
        the -` X \<inter> the -` A \<inter> range Some"
    by(auto split: bind_splits if_split_asm)
  then show ?thesis
    by (simp add: restrict_spmf_def measure_spmf_def emeasure_distr emeasure_restrict_space)
qed

lemma measure_restrict_spmf [simp]:
  "measure (measure_spmf (p \<upharpoonleft> A)) X = measure (measure_spmf p) (X \<inter> A)"
  using emeasure_restrict_spmf[of p A X]
  by(simp only: measure_spmf.emeasure_eq_measure ennreal_inj measure_nonneg)

lemma spmf_restrict_spmf: "spmf (p \<upharpoonleft> A) x = (if x \<in> A then spmf p x else 0)"
  by(simp add: spmf_conv_measure_spmf)

lemma spmf_restrict_spmf_inside [simp]: "x \<in> A \<Longrightarrow> spmf (p \<upharpoonleft> A) x = spmf p x"
  by(simp add: spmf_restrict_spmf)

lemma pmf_restrict_spmf_None: "pmf (p \<upharpoonleft> A) None = pmf p None + measure (measure_spmf p) (- A)"
proof -
  have [simp]: "None \<notin> Some ` (- A)" by auto
  have "(\<lambda>x. x \<bind> (\<lambda>y. if y \<in> A then Some y else None)) -` {None} = {None} \<union> (Some ` (- A))"
    by(auto split: bind_splits if_split_asm)
  then show ?thesis unfolding ereal.inject[symmetric]
    by(simp add: restrict_spmf_def ennreal_pmf_map emeasure_pmf_single del: ereal.inject)
      (simp add: pmf.rep_eq measure_pmf.finite_measure_Union[symmetric] measure_measure_spmf_conv_measure_pmf measure_pmf.emeasure_eq_measure)
qed

lemma restrict_spmf_trivial: "(\<And>x. x \<in> set_spmf p \<Longrightarrow> x \<in> A) \<Longrightarrow> p \<upharpoonleft> A = p"
  by(rule spmf_eqI)(auto simp: spmf_restrict_spmf spmf_eq_0_set_spmf)

lemma restrict_spmf_trivial': "set_spmf p \<subseteq> A \<Longrightarrow> p \<upharpoonleft> A = p"
  by(rule restrict_spmf_trivial) blast

lemma restrict_return_spmf: "return_spmf x \<upharpoonleft> A = (if x \<in> A then return_spmf x else return_pmf None)"
  by(simp add: restrict_spmf_def)

lemma restrict_return_spmf_inside [simp]: "x \<in> A \<Longrightarrow> return_spmf x \<upharpoonleft> A = return_spmf x"
  by(simp add: restrict_return_spmf)

lemma restrict_return_spmf_outside [simp]: "x \<notin> A \<Longrightarrow> return_spmf x \<upharpoonleft> A = return_pmf None"
  by(simp add: restrict_return_spmf)

lemma restrict_spmf_return_pmf_None [simp]: "return_pmf None \<upharpoonleft> A = return_pmf None"
  by(simp add: restrict_spmf_def)

lemma restrict_bind_pmf: "bind_pmf p g \<upharpoonleft> A = p \<bind> (\<lambda>x. g x \<upharpoonleft> A)"
  by(simp add: restrict_spmf_def map_bind_pmf o_def)

lemma restrict_bind_spmf: "bind_spmf p g \<upharpoonleft> A = p \<bind> (\<lambda>x. g x \<upharpoonleft> A)"
  by(auto simp: bind_spmf_def restrict_bind_pmf cong del: option.case_cong_weak cong: option.case_cong intro!: bind_pmf_cong split: option.split)

lemma bind_restrict_pmf: "bind_pmf (p \<upharpoonleft> A) g = p \<bind> (\<lambda>x. if x \<in> Some ` A then g x else g None)"
  by(auto simp: restrict_spmf_def bind_map_pmf fun_eq_iff split: bind_split intro: arg_cong2[where f=bind_pmf])

lemma bind_restrict_spmf: "bind_spmf (p \<upharpoonleft> A) g = p \<bind> (\<lambda>x. if x \<in> A then g x else return_pmf None)"
  by(auto simp: bind_spmf_def bind_restrict_pmf fun_eq_iff intro: arg_cong2[where f=bind_pmf] split: option.split)

lemma spmf_map_restrict: "spmf (map_spmf fst (p \<upharpoonleft> (snd -` {y}))) x = spmf p (x, y)"
  by(subst spmf_map)(auto intro: arg_cong2[where f=measure] simp add: spmf_conv_measure_spmf)

lemma measure_eqI_restrict_spmf:
  assumes "rel_spmf R (restrict_spmf p A) (restrict_spmf q B)"
  shows "measure (measure_spmf p) A = measure (measure_spmf q) B"
proof -
  from assms have "weight_spmf (restrict_spmf p A) = weight_spmf (restrict_spmf q B)" by(rule rel_spmf_weightD)
  thus ?thesis by(simp add: weight_spmf_def)
qed

subsection \<open>Subprobability distributions of sets\<close>

definition spmf_of_set :: "'a set \<Rightarrow> 'a spmf"
where
  "spmf_of_set A = (if finite A \<and> A \<noteq> {} then spmf_of_pmf (pmf_of_set A) else return_pmf None)"

lemma spmf_of_set: "spmf (spmf_of_set A) x = indicator A x / card A"
  by(auto simp: spmf_of_set_def)

lemma pmf_spmf_of_set_None [simp]: "pmf (spmf_of_set A) None = indicator {A. infinite A \<or> A = {}} A"
  by(simp add: spmf_of_set_def)

lemma set_spmf_of_set: "set_spmf (spmf_of_set A) = (if finite A then A else {})"
  by(simp add: spmf_of_set_def)

lemma set_spmf_of_set_finite [simp]: "finite A \<Longrightarrow> set_spmf (spmf_of_set A) = A"
  by(simp add: set_spmf_of_set)

lemma spmf_of_set_singleton: "spmf_of_set {x} = return_spmf x"
  by(simp add: spmf_of_set_def pmf_of_set_singleton)

lemma map_spmf_of_set_inj_on [simp]:
  "inj_on f A \<Longrightarrow> map_spmf f (spmf_of_set A) = spmf_of_set (f ` A)"
  by(auto simp: spmf_of_set_def map_pmf_of_set_inj dest: finite_imageD)

lemma spmf_of_pmf_pmf_of_set [simp]:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> spmf_of_pmf (pmf_of_set A) = spmf_of_set A"
  by(simp add: spmf_of_set_def)

lemma weight_spmf_of_set:
  "weight_spmf (spmf_of_set A) = (if finite A \<and> A \<noteq> {} then 1 else 0)"
  by(auto simp only: spmf_of_set_def weight_spmf_of_pmf weight_return_pmf_None split: if_split)

lemma weight_spmf_of_set_finite [simp]: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> weight_spmf (spmf_of_set A) = 1"
  by(simp add: weight_spmf_of_set)

lemma weight_spmf_of_set_infinite [simp]: "infinite A \<Longrightarrow> weight_spmf (spmf_of_set A) = 0"
  by(simp add: weight_spmf_of_set)

lemma measure_spmf_spmf_of_set:
  "measure_spmf (spmf_of_set A) = (if finite A \<and> A \<noteq> {} then measure_pmf (pmf_of_set A) else null_measure (count_space UNIV))"
  by(simp add: spmf_of_set_def del: spmf_of_pmf_pmf_of_set)

lemma emeasure_spmf_of_set:
  "emeasure (measure_spmf (spmf_of_set S)) A = card (S \<inter> A) / card S"
  by(auto simp: measure_spmf_spmf_of_set emeasure_pmf_of_set)

lemma measure_spmf_of_set:
  "measure (measure_spmf (spmf_of_set S)) A = card (S \<inter> A) / card S"
  by(auto simp: measure_spmf_spmf_of_set measure_pmf_of_set)

lemma nn_integral_spmf_of_set: "nn_integral (measure_spmf (spmf_of_set A)) f = sum f A / card A"
  by(cases "finite A")(auto simp: spmf_of_set_def nn_integral_pmf_of_set card_gt_0_iff simp del: spmf_of_pmf_pmf_of_set)

lemma integral_spmf_of_set: "integral\<^sup>L (measure_spmf (spmf_of_set A)) f = sum f A / card A"
  by (metis card.infinite div_0 division_ring_divide_zero integral_null_measure integral_pmf_of_set measure_spmf_spmf_of_set of_nat_0 sum.empty)

notepad begin \<comment> \<open>\<^const>\<open>pmf_of_set\<close> is not fully parametric.\<close>
  define R :: "nat \<Rightarrow> nat \<Rightarrow> bool" where "R x y \<longleftrightarrow> (x \<noteq> 0 \<longrightarrow> y = 0)" for x y
  define A :: "nat set" where "A = {0, 1}"
  define B :: "nat set" where "B = {0, 1, 2}"
  have "rel_set R A B" unfolding R_def[abs_def] A_def B_def rel_set_def by auto
  have "\<not> rel_pmf R (pmf_of_set A) (pmf_of_set B)"
  proof
    assume "rel_pmf R (pmf_of_set A) (pmf_of_set B)"
    then obtain pq where pq: "\<And>x y. (x, y) \<in> set_pmf pq \<Longrightarrow> R x y"
      and 1: "map_pmf fst pq = pmf_of_set A"
      and 2: "map_pmf snd pq = pmf_of_set B"
      by cases auto
    have "pmf (pmf_of_set B) 1 = 1 / 3" by(simp add: B_def)
    have "pmf (pmf_of_set B) 2 = 1 / 3" by(simp add: B_def)

    have "2 / 3 = pmf (pmf_of_set B) 1 + pmf (pmf_of_set B) 2" by(simp add: B_def)
    also have "\<dots> = measure (measure_pmf (pmf_of_set B)) ({1} \<union> {2})"
      by(subst measure_pmf.finite_measure_Union)(simp_all add: measure_pmf_single)
    also have "\<dots> = emeasure (measure_pmf pq) (snd -` {2, 1})"
      unfolding 2[symmetric] measure_pmf.emeasure_eq_measure[symmetric] by(simp)
    also have "\<dots> = emeasure (measure_pmf pq) {(0, 2), (0, 1)}"
      by(rule emeasure_eq_AE)(auto simp: AE_measure_pmf_iff R_def dest!: pq)
    also have "\<dots> \<le> emeasure (measure_pmf pq) (fst -` {0})"
      by(rule emeasure_mono) auto
    also have "\<dots> = emeasure (measure_pmf (pmf_of_set A)) {0}"
      unfolding 1[symmetric] by simp
    also have "\<dots> = pmf (pmf_of_set A) 0"
      by(simp add: measure_pmf_single measure_pmf.emeasure_eq_measure)
    also have "pmf (pmf_of_set A) 0 = 1 / 2" by(simp add: A_def)
    finally show False by(subst (asm) ennreal_le_iff; simp)
  qed
end

lemma rel_pmf_of_set_bij:
  assumes f: "bij_betw f A B"
  and A: "A \<noteq> {}" "finite A"
  and B: "B \<noteq> {}" "finite B"
  and R: "\<And>x. x \<in> A \<Longrightarrow> R x (f x)"
  shows "rel_pmf R (pmf_of_set A) (pmf_of_set B)"
proof(rule pmf.rel_mono_strong)
  define AB where "AB = (\<lambda>x. (x, f x)) ` A"
  define R' where "R' x y \<longleftrightarrow> (x, y) \<in> AB" for x y
  have "(x, y) \<in> AB" if "(x, y) \<in> set_pmf (pmf_of_set AB)" for x y
    using that by(auto simp: AB_def A)
  moreover have "map_pmf fst (pmf_of_set AB) = pmf_of_set A"
    by(simp add: AB_def map_pmf_of_set_inj[symmetric] inj_on_def A pmf.map_comp o_def)
  moreover
  from f have [simp]: "inj_on f A" by(rule bij_betw_imp_inj_on)
  from f have [simp]: "f ` A = B" by(rule bij_betw_imp_surj_on)
  have "map_pmf snd (pmf_of_set AB) = pmf_of_set B"
    by(simp add: AB_def map_pmf_of_set_inj[symmetric] inj_on_def A pmf.map_comp o_def)
      (simp add: map_pmf_of_set_inj A)
  ultimately show "rel_pmf (\<lambda>x y. (x, y) \<in> AB) (pmf_of_set A) (pmf_of_set B)" ..
qed(auto intro: R)

lemma rel_spmf_of_set_bij:
  assumes f: "bij_betw f A B"
  and R: "\<And>x. x \<in> A \<Longrightarrow> R x (f x)"
  shows "rel_spmf R (spmf_of_set A) (spmf_of_set B)"
proof -
  obtain "finite A \<longleftrightarrow> finite B" "A = {} \<longleftrightarrow> B = {}"
    using bij_betw_empty1 bij_betw_empty2 bij_betw_finite f by blast 
  then show ?thesis 
    using assms
    by (metis rel_pmf_of_set_bij rel_spmf_spmf_of_pmf return_spmf_None_parametric spmf_of_set_def)
qed

context includes lifting_syntax
begin

lemma rel_spmf_of_set:
  assumes "bi_unique R"
  shows "(rel_set R ===> rel_spmf R) spmf_of_set spmf_of_set"
proof
  fix A B
  assume R: "rel_set R A B"
  with assms obtain f where "bij_betw f A B" and f: "\<And>x. x \<in> A \<Longrightarrow> R x (f x)"
    by(auto dest: bi_unique_rel_set_bij_betw)
  then show "rel_spmf R (spmf_of_set A) (spmf_of_set B)" 
    by(rule rel_spmf_of_set_bij)
qed

end

lemma map_mem_spmf_of_set:
  assumes "finite B" "B \<noteq> {}"
  shows "map_spmf (\<lambda>x. x \<in> A) (spmf_of_set B) = spmf_of_pmf (bernoulli_pmf (card (A \<inter> B) / card B))"
  (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  fix i
  have "ennreal (spmf ?lhs i) = card (B \<inter> (\<lambda>x. x \<in> A) -` {i}) / (card B)"
    by(subst ennreal_spmf_map)(simp add: measure_spmf_spmf_of_set assms emeasure_pmf_of_set)
  also have "\<dots> = (if i then card (B \<inter> A) / card B else card (B - A) / card B)"
    by(auto intro: arg_cong[where f=card])
  also have "\<dots> = (if i then card (B \<inter> A) / card B else (card B - card (B \<inter> A)) / card B)"
    by(auto simp: card_Diff_subset_Int assms)
  also have "\<dots> = ennreal (spmf ?rhs i)"
    by(simp add: assms card_gt_0_iff field_simps card_mono Int_commute of_nat_diff)
  finally show "spmf ?lhs i = spmf ?rhs i" by simp
qed

abbreviation coin_spmf :: "bool spmf"
where "coin_spmf \<equiv> spmf_of_set UNIV"

lemma map_eq_const_coin_spmf: "map_spmf ((=) c) coin_spmf = coin_spmf"
proof -
  have "inj ((\<longleftrightarrow>) c)" "range ((\<longleftrightarrow>) c) = UNIV" by(auto intro: inj_onI)
  then show ?thesis by simp
qed

lemma bind_coin_spmf_eq_const: "coin_spmf \<bind> (\<lambda>x :: bool. return_spmf (b = x)) = coin_spmf"
  using map_eq_const_coin_spmf unfolding map_spmf_conv_bind_spmf by simp

lemma bind_coin_spmf_eq_const': "coin_spmf \<bind> (\<lambda>x :: bool. return_spmf (x = b)) = coin_spmf"
  by(rewrite in "_ = \<hole>" bind_coin_spmf_eq_const[symmetric, of b])(auto intro: bind_spmf_cong)

subsection \<open>Losslessness\<close>

definition lossless_spmf :: "'a spmf \<Rightarrow> bool"
  where "lossless_spmf p \<longleftrightarrow> weight_spmf p = 1"

lemma lossless_iff_pmf_None: "lossless_spmf p \<longleftrightarrow> pmf p None = 0"
  by(simp add: lossless_spmf_def pmf_None_eq_weight_spmf)

lemma lossless_return_spmf [iff]: "lossless_spmf (return_spmf x)"
  by(simp add: lossless_iff_pmf_None)

lemma lossless_return_pmf_None [iff]: "\<not> lossless_spmf (return_pmf None)"
  by(simp add: lossless_iff_pmf_None)

lemma lossless_map_spmf [simp]: "lossless_spmf (map_spmf f p) \<longleftrightarrow> lossless_spmf p"
  by(auto simp: lossless_iff_pmf_None pmf_eq_0_set_pmf)

lemma lossless_bind_spmf [simp]:
  "lossless_spmf (p \<bind> f) \<longleftrightarrow> lossless_spmf p \<and> (\<forall>x\<in>set_spmf p. lossless_spmf (f x))"
  by(simp add: lossless_iff_pmf_None pmf_bind_spmf_None add_nonneg_eq_0_iff integral_nonneg_AE integral_nonneg_eq_0_iff_AE measure_spmf.integrable_const_bound[where B=1] pmf_le_1)

lemma lossless_weight_spmfD: "lossless_spmf p \<Longrightarrow> weight_spmf p = 1"
  by(simp add: lossless_spmf_def)

lemma lossless_iff_set_pmf_None:
  "lossless_spmf p \<longleftrightarrow> None \<notin> set_pmf p"
  by (simp add: lossless_iff_pmf_None pmf_eq_0_set_pmf)

lemma lossless_spmf_of_set [simp]: "lossless_spmf (spmf_of_set A) \<longleftrightarrow> finite A \<and> A \<noteq> {}"
  by(auto simp: lossless_spmf_def weight_spmf_of_set)

lemma lossless_spmf_spmf_of_spmf [simp]: "lossless_spmf (spmf_of_pmf p)"
  by(simp add: lossless_spmf_def)

lemma lossless_spmf_bind_pmf [simp]:
  "lossless_spmf (bind_pmf p f) \<longleftrightarrow> (\<forall>x\<in>set_pmf p. lossless_spmf (f x))"
  by(simp add: lossless_iff_pmf_None pmf_bind integral_nonneg_AE integral_nonneg_eq_0_iff_AE measure_pmf.integrable_const_bound[where B=1] AE_measure_pmf_iff pmf_le_1)

lemma lossless_spmf_conv_spmf_of_pmf: "lossless_spmf p \<longleftrightarrow> (\<exists>p'. p = spmf_of_pmf p')"
proof
  assume "lossless_spmf p"
  hence *: "\<And>y. y \<in> set_pmf p \<Longrightarrow> \<exists>x. y = Some x"
    by(case_tac y)(simp_all add: lossless_iff_set_pmf_None)

  let ?p = "map_pmf the p"
  have "p = spmf_of_pmf ?p"
  proof(rule spmf_eqI)
    fix i
    have "ennreal (pmf (map_pmf the p) i) = \<integral>\<^sup>+ x. indicator (the -` {i}) x \<partial>p" by(simp add: ennreal_pmf_map)
    also have "\<dots> = \<integral>\<^sup>+ x. indicator {i} x \<partial>measure_spmf p" unfolding measure_spmf_def
      by(subst nn_integral_distr)(auto simp: nn_integral_restrict_space AE_measure_pmf_iff simp del: nn_integral_indicator intro!: nn_integral_cong_AE split: split_indicator dest!: * )
    also have "\<dots> = spmf p i" by(simp add: emeasure_spmf_single)
    finally show "spmf p i = spmf (spmf_of_pmf ?p) i" by simp
  qed
  thus "\<exists>p'. p = spmf_of_pmf p'" ..
qed auto

lemma spmf_False_conv_True: "lossless_spmf p \<Longrightarrow> spmf p False = 1 - spmf p True"
  by(clarsimp simp add: lossless_spmf_conv_spmf_of_pmf pmf_False_conv_True)

lemma spmf_True_conv_False: "lossless_spmf p \<Longrightarrow> spmf p True = 1 - spmf p False"
  by(simp add: spmf_False_conv_True)

lemma bind_eq_return_spmf:
  "bind_spmf p f = return_spmf x \<longleftrightarrow> (\<forall>y\<in>set_spmf p. f y = return_spmf x) \<and> lossless_spmf p"
  apply (simp add: bind_spmf_def bind_eq_return_pmf split: option.split)
  by (metis in_set_spmf lossless_iff_set_pmf_None not_None_eq)

lemma rel_spmf_return_spmf2:
  "rel_spmf R p (return_spmf x) \<longleftrightarrow> lossless_spmf p \<and> (\<forall>a\<in>set_spmf p. R a x)"
  apply (simp add: lossless_iff_set_pmf_None rel_pmf_return_pmf2 option_rel_Some2 in_set_spmf)
  by (metis in_set_spmf not_None_eq option.sel)

lemma rel_spmf_return_spmf1:
  "rel_spmf R (return_spmf x) p \<longleftrightarrow> lossless_spmf p \<and> (\<forall>a\<in>set_spmf p. R x a)"
  using rel_spmf_return_spmf2[of "R\<inverse>\<inverse>"] by(simp add: spmf_rel_conversep)

lemma rel_spmf_bindI1:
  assumes f: "\<And>x. x \<in> set_spmf p \<Longrightarrow> rel_spmf R (f x) q"
  and p: "lossless_spmf p"
  shows "rel_spmf R (bind_spmf p f) q"
proof -
  fix x :: 'a
  have "rel_spmf R (bind_spmf p f) (bind_spmf (return_spmf x) (\<lambda>_. q))"
    by(rule rel_spmf_bindI[where R="\<lambda>x _. x \<in> set_spmf p"])(simp_all add: rel_spmf_return_spmf2 p f)
  then show ?thesis by simp
qed

lemma rel_spmf_bindI2:
  "\<lbrakk> \<And>x. x \<in> set_spmf q \<Longrightarrow> rel_spmf R p (f x); lossless_spmf q \<rbrakk>
  \<Longrightarrow> rel_spmf R p (bind_spmf q f)"
  using rel_spmf_bindI1[of q "conversep R" f p] by(simp add: spmf_rel_conversep)

subsection \<open>Scaling\<close>

definition scale_spmf :: "real \<Rightarrow> 'a spmf \<Rightarrow> 'a spmf"
where
  "scale_spmf r p = embed_spmf (\<lambda>x. min (inverse (weight_spmf p)) (max 0 r) * spmf p x)"

lemma scale_spmf_le_1:
  "(\<integral>\<^sup>+ x. min (inverse (weight_spmf p)) (max 0 r) * spmf p x \<partial>count_space UNIV) \<le> 1" (is "?lhs \<le> _")
proof -
  have "?lhs = min (inverse (weight_spmf p)) (max 0 r) * \<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV"
    by(subst nn_integral_cmult[symmetric])(simp_all add: weight_spmf_nonneg max_def min_def ennreal_mult)
  also have "\<dots> \<le> 1" unfolding weight_spmf_eq_nn_integral_spmf[symmetric]
    by(simp add: min_def max_def weight_spmf_nonneg order.strict_iff_order field_simps ennreal_mult[symmetric])
  finally show ?thesis .
qed

lemma spmf_scale_spmf: "spmf (scale_spmf r p) x = max 0 (min (inverse (weight_spmf p)) r) * spmf p x" (is "?lhs = ?rhs")
  unfolding scale_spmf_def
  apply(subst spmf_embed_spmf[OF scale_spmf_le_1])
  apply(simp add: max_def min_def measure_le_0_iff field_simps weight_spmf_nonneg not_le order.strict_iff_order)
  apply(metis antisym_conv order_trans weight_spmf_nonneg zero_le_mult_iff zero_le_one)
  done

lemma real_inverse_le_1_iff: fixes x :: real
  shows "\<lbrakk> 0 \<le> x; x \<le> 1 \<rbrakk> \<Longrightarrow> 1 / x \<le> 1 \<longleftrightarrow> x = 1 \<or> x = 0"
  by auto

lemma spmf_scale_spmf': "r \<le> 1 \<Longrightarrow> spmf (scale_spmf r p) x = max 0 r * spmf p x"
  using real_inverse_le_1_iff[OF weight_spmf_nonneg weight_spmf_le_1, of p]
  by(auto simp: spmf_scale_spmf max_def min_def field_simps)(metis pmf_le_0_iff spmf_le_weight)

lemma scale_spmf_neg: "r \<le> 0 \<Longrightarrow> scale_spmf r p = return_pmf None"
  by(rule spmf_eqI)(simp add: spmf_scale_spmf' max_def)

lemma scale_spmf_return_None [simp]: "scale_spmf r (return_pmf None) = return_pmf None"
  by(rule spmf_eqI)(simp add: spmf_scale_spmf)

lemma scale_spmf_conv_bind_bernoulli:
  assumes "r \<le> 1"
  shows "scale_spmf r p = bind_pmf (bernoulli_pmf r) (\<lambda>b. if b then p else return_pmf None)" (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  fix x
  have "\<lbrakk>weight_spmf p = 0\<rbrakk> \<Longrightarrow> spmf p x = 0"
    by (metis pmf_le_0_iff spmf_le_weight)
  moreover have "\<lbrakk>weight_spmf p \<noteq> 0; 1 / weight_spmf p < 1\<rbrakk> \<Longrightarrow> weight_spmf p = 1"
    by (smt (verit) divide_less_eq_1 measure_spmf.subprob_measure_le_1 weight_spmf_lt_0)
  ultimately have "ennreal (spmf ?lhs x) = ennreal (spmf ?rhs x)" 
    using assms
    unfolding spmf_scale_spmf ennreal_pmf_bind nn_integral_measure_pmf UNIV_bool bernoulli_pmf.rep_eq
    by(auto simp: nn_integral_count_space_finite max_def min_def field_simps 
          real_inverse_le_1_iff[OF weight_spmf_nonneg weight_spmf_le_1]  ennreal_mult[symmetric])
  thus "spmf ?lhs x = spmf ?rhs x" by simp
qed

lemma nn_integral_spmf: "(\<integral>\<^sup>+ x. spmf p x \<partial>count_space A) = emeasure (measure_spmf p) A"
proof -
  have "bij_betw Some A (the -` A \<inter> range Some)"
    by(auto simp: bij_betw_def)
  then show ?thesis
    by (metis bij_betw_def emeasure_measure_spmf_conv_measure_pmf nn_integral_pmf')
qed

lemma measure_spmf_scale_spmf: "measure_spmf (scale_spmf r p) = scale_measure (min (inverse (weight_spmf p)) r) (measure_spmf p)"
  by(rule measure_eqI; simp add: spmf_scale_spmf ennreal_mult' flip: nn_integral_spmf nn_integral_cmult)

lemma measure_spmf_scale_spmf':
  assumes "r \<le> 1"
  shows "measure_spmf (scale_spmf r p) = scale_measure r (measure_spmf p)"
proof(cases "weight_spmf p > 0")
  case True
  with assms show ?thesis    
    by(simp add: measure_spmf_scale_spmf field_simps weight_spmf_le_1 mult_le_one)
next
  case False
  then show ?thesis
    by (simp add: order_less_le weight_spmf_eq_0)
qed

lemma scale_spmf_1 [simp]: "scale_spmf 1 p = p"
  by (simp add: spmf_eqI spmf_scale_spmf')

lemma scale_spmf_0 [simp]: "scale_spmf 0 p = return_pmf None"
  by (simp add: scale_spmf_neg)

lemma bind_scale_spmf:
  assumes r: "r \<le> 1"
  shows "bind_spmf (scale_spmf r p) f = bind_spmf p (\<lambda>x. scale_spmf r (f x))"
  (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  fix x
  have "ennreal (spmf ?lhs x) = ennreal (spmf ?rhs x)" 
    using r
    by(simp add: ennreal_spmf_bind measure_spmf_scale_spmf' nn_integral_scale_measure spmf_scale_spmf'
        ennreal_mult nn_integral_cmult)
  thus "spmf ?lhs x = spmf ?rhs x" by simp
qed

lemma scale_bind_spmf:
  assumes "r \<le> 1"
  shows "scale_spmf r (bind_spmf p f) = bind_spmf p (\<lambda>x. scale_spmf r (f x))"
  (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  fix x
  have "ennreal (spmf ?lhs x) = ennreal (spmf ?rhs x)" using assms
    unfolding spmf_scale_spmf'[OF assms]
    by(simp add: ennreal_mult ennreal_spmf_bind spmf_scale_spmf' nn_integral_cmult max_def min_def)
  thus "spmf ?lhs x = spmf ?rhs x" by simp
qed

lemma bind_spmf_const: "bind_spmf p (\<lambda>x. q) = scale_spmf (weight_spmf p) q" (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  fix x
  have "ennreal (spmf ?lhs x) = ennreal (spmf ?rhs x)"
    using measure_spmf.subprob_measure_le_1[of p "space (measure_spmf p)"]
    by(subst ennreal_spmf_bind)(simp add: spmf_scale_spmf' weight_spmf_le_1 ennreal_mult mult.commute max_def min_def measure_spmf.emeasure_eq_measure)
  thus "spmf ?lhs x = spmf ?rhs x" by simp
qed

lemma map_scale_spmf: "map_spmf f (scale_spmf r p) = scale_spmf r (map_spmf f p)" (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  fix i
  show "spmf ?lhs i = spmf ?rhs i" unfolding spmf_scale_spmf
    by(subst (1 2) spmf_map)(auto simp: measure_spmf_scale_spmf max_def min_def ennreal_lt_0)
qed

lemma set_scale_spmf: "set_spmf (scale_spmf r p) = (if r > 0 then set_spmf p else {})"
  apply(auto simp: in_set_spmf_iff_spmf spmf_scale_spmf)
  apply(simp add: min_def weight_spmf_eq_0 split: if_split_asm)
  done

lemma set_scale_spmf' [simp]: "0 < r \<Longrightarrow> set_spmf (scale_spmf r p) = set_spmf p"
  by(simp add: set_scale_spmf)

lemma rel_spmf_scaleI:
  assumes "r > 0 \<Longrightarrow> rel_spmf A p q"
  shows "rel_spmf A (scale_spmf r p) (scale_spmf r q)"
proof(cases "r > 0")
  case True
  from assms[OF True] show ?thesis
    by(rule rel_spmfE)(auto simp: map_scale_spmf[symmetric] spmf_rel_map True intro: rel_spmf_reflI)
qed(simp add: not_less scale_spmf_neg)

lemma weight_scale_spmf: "weight_spmf (scale_spmf r p) = min 1 (max 0 r * weight_spmf p)"
proof -
  have "\<lbrakk>1 / weight_spmf p \<le> r; ennreal r * ennreal (weight_spmf p) < 1\<rbrakk> \<Longrightarrow> weight_spmf p = 0"
    by (smt (verit) ennreal_less_one_iff ennreal_mult'' measure_le_0_iff mult_imp_less_div_pos)
  moreover
  have "\<lbrakk>r < 1 / weight_spmf p; 1 \<le> ennreal r * ennreal (weight_spmf p)\<rbrakk> \<Longrightarrow> weight_spmf p = 0"
    by (smt (verit, ccfv_threshold) ennreal_ge_1 ennreal_mult'' mult_imp_div_pos_le weight_spmf_lt_0)
  ultimately
  have "ennreal (weight_spmf (scale_spmf r p)) = min 1 (max 0 r * ennreal (weight_spmf p))"
    unfolding weight_spmf_eq_nn_integral_spmf
    apply(simp add: spmf_scale_spmf ennreal_mult zero_ereal_def[symmetric] nn_integral_cmult)
    apply(auto simp: weight_spmf_eq_nn_integral_spmf[symmetric] field_simps min_def max_def not_le weight_spmf_lt_0 ennreal_mult[symmetric])
    done
  thus ?thesis
    by(auto simp: min_def max_def ennreal_mult[symmetric] split: if_split_asm)
qed

lemma weight_scale_spmf' [simp]:
  "\<lbrakk> 0 \<le> r; r \<le> 1 \<rbrakk> \<Longrightarrow> weight_spmf (scale_spmf r p) = r * weight_spmf p"
  by(simp add: weight_scale_spmf max_def min_def)(metis antisym_conv mult_left_le order_trans weight_spmf_le_1)

lemma pmf_scale_spmf_None:
  "pmf (scale_spmf k p) None = 1 - min 1 (max 0 k * (1 - pmf p None))"
  unfolding pmf_None_eq_weight_spmf by(simp add: weight_scale_spmf)

lemma scale_scale_spmf:
  "scale_spmf r (scale_spmf r' p) = scale_spmf (r * max 0 (min (inverse (weight_spmf p)) r')) p"
  (is "?lhs = ?rhs")
proof(cases "weight_spmf p > 0")
  case False
  thus ?thesis
    by (simp add: weight_spmf_eq_0 zero_less_measure_iff)
next
  case True
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have *: "max 0 (min (1 / weight_spmf p) r') * max 0 (min (1 / min 1 (weight_spmf p * max 0 r')) r) =
          max 0 (min (1 / weight_spmf p) (r * max 0 (min (1 / weight_spmf p) r')))"
      using True
      by (simp add: max_def) (auto simp: min_def field_simps zero_le_mult_iff)
    show "spmf ?lhs i = spmf ?rhs i"
      by (simp add: spmf_scale_spmf) (metis * inverse_eq_divide mult.commute weight_scale_spmf)
  qed
qed

lemma scale_scale_spmf' [simp]:
  assumes "0 \<le> r" "r \<le> 1" "0 \<le> r'" "r' \<le> 1"
  shows "scale_spmf r (scale_spmf r' p) = scale_spmf (r * r') p"
proof(cases "weight_spmf p > 0")
  case True
  with assms have "r' = 1" if "1 \<le> r' * weight_spmf p"
    by (smt (verit, best) measure_spmf.subprob_measure_le_1 mult_eq_1 mult_le_one that)
  with assms True show ?thesis
    by (smt (verit, best) eq_divide_imp measure_le_0_iff mult.assoc mult_nonneg_nonneg scale_scale_spmf weight_scale_spmf')
next
  case False
  with assms show ?thesis
    by (simp add: weight_spmf_eq_0 zero_less_measure_iff)
qed

lemma scale_spmf_eq_same: "scale_spmf r p = p \<longleftrightarrow> weight_spmf p = 0 \<or> r = 1 \<or> r \<ge> 1 \<and> weight_spmf p = 1"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "weight_spmf (scale_spmf r p) = weight_spmf p" by simp
  hence *: "min 1 (max 0 r * weight_spmf p) = weight_spmf p" by(simp add: weight_scale_spmf)
  hence **: "weight_spmf p = 0 \<or> r \<ge> 1" by(auto simp: min_def max_def split: if_split_asm)
  show ?rhs
  proof(cases "weight_spmf p = 0")
    case False
    with ** have "r \<ge> 1" 
      by simp
    with * False have "r = 1 \<or> weight_spmf p = 1" 
      by(simp add: max_def min_def not_le split: if_split_asm)
    with \<open>r \<ge> 1\<close> show ?thesis 
      by simp
  qed simp
next
  show "weight_spmf p = 0 \<or> r = 1 \<or> 1 \<le> r \<and> weight_spmf p = 1 \<Longrightarrow> scale_spmf r p = p"
    by (smt (verit) div_by_1 inverse_eq_divide inverse_positive_iff_positive scale_scale_spmf scale_spmf_1)
qed

lemma map_const_spmf_of_set:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> map_spmf (\<lambda>_. c) (spmf_of_set A) = return_spmf c"
  by(simp add: map_spmf_conv_bind_spmf bind_spmf_const)

subsection \<open>Conditional spmfs\<close>

lemma set_pmf_Int_Some: "set_pmf p \<inter> Some ` A = {} \<longleftrightarrow> set_spmf p \<inter> A = {}"
  by(auto simp: in_set_spmf)

lemma measure_spmf_zero_iff: "measure (measure_spmf p) A = 0 \<longleftrightarrow> set_spmf p \<inter> A = {}"
  unfolding measure_measure_spmf_conv_measure_pmf by(simp add: measure_pmf_zero_iff set_pmf_Int_Some)

definition cond_spmf :: "'a spmf \<Rightarrow> 'a set \<Rightarrow> 'a spmf"
  where "cond_spmf p A = (if set_spmf p \<inter> A = {} then return_pmf None else cond_pmf p (Some ` A))"

lemma set_cond_spmf [simp]: "set_spmf (cond_spmf p A) = set_spmf p \<inter> A"
  by(auto 4 4 simp add: cond_spmf_def in_set_spmf iff: set_cond_pmf[THEN set_eq_iff[THEN iffD1], THEN spec, rotated])

lemma cond_map_spmf [simp]: "cond_spmf (map_spmf f p) A = map_spmf f (cond_spmf p (f -` A))"
proof -
  have "map_option f -` Some ` A = Some ` f -` A" by auto
  moreover have "set_pmf p \<inter> map_option f -` Some ` A \<noteq> {}" if "Some x \<in> set_pmf p" "f x \<in> A" for x
    using that by auto
  ultimately show ?thesis by(auto simp: cond_spmf_def in_set_spmf cond_map_pmf)
qed

lemma spmf_cond_spmf [simp]:
  "spmf (cond_spmf p A) x = (if x \<in> A then spmf p x / measure (measure_spmf p) A else 0)"
  by(auto simp: cond_spmf_def pmf_cond set_pmf_Int_Some[symmetric] measure_measure_spmf_conv_measure_pmf measure_pmf_zero_iff)

lemma bind_eq_return_pmf_None:
  "bind_spmf p f = return_pmf None \<longleftrightarrow> (\<forall>x\<in>set_spmf p. f x = return_pmf None)"
  by(auto simp: bind_spmf_def bind_eq_return_pmf in_set_spmf split: option.splits)

lemma return_pmf_None_eq_bind:
  "return_pmf None = bind_spmf p f \<longleftrightarrow> (\<forall>x\<in>set_spmf p. f x = return_pmf None)"
  using bind_eq_return_pmf_None[of p f] by auto

(* Conditional probabilities do not seem to interact nicely with bind. *)

subsection \<open>Product spmf\<close>

definition pair_spmf :: "'a spmf \<Rightarrow> 'b spmf \<Rightarrow> ('a \<times> 'b) spmf"
where "pair_spmf p q = bind_pmf (pair_pmf p q) (\<lambda>xy. case xy of (Some x, Some y) \<Rightarrow> return_spmf (x, y) | _ \<Rightarrow> return_pmf None)"

lemma map_fst_pair_spmf [simp]: "map_spmf fst (pair_spmf p q) = scale_spmf (weight_spmf q) p"
  unfolding bind_spmf_const[symmetric]
  apply(simp add: pair_spmf_def map_bind_pmf pair_pmf_def bind_assoc_pmf option.case_distrib)
  apply(subst bind_commute_pmf)
  apply(force intro!: bind_pmf_cong[OF refl] simp add: bind_return_pmf bind_spmf_def bind_return_pmf' case_option_collapse 
      option.case_distrib[where h="map_spmf _"] option.case_distrib[symmetric] case_option_id split: option.split cong: option.case_cong)
  done

lemma map_snd_pair_spmf [simp]: "map_spmf snd (pair_spmf p q) = scale_spmf (weight_spmf p) q"
  unfolding bind_spmf_const[symmetric]
  apply(simp add: pair_spmf_def map_bind_pmf pair_pmf_def bind_assoc_pmf option.case_distrib
      cong del: option.case_cong_weak)
  apply(auto intro!: bind_pmf_cong[OF refl] simp add: bind_return_pmf bind_spmf_def bind_return_pmf' case_option_collapse
      option.case_distrib[where h="map_spmf _"] option.case_distrib[symmetric] case_option_id split: option.split cong del: option.case_cong_weak)
  done

lemma set_pair_spmf [simp]: "set_spmf (pair_spmf p q) = set_spmf p \<times> set_spmf q"
  by(force simp add: pair_spmf_def set_spmf_bind_pmf bind_UNION in_set_spmf split: option.splits)

lemma spmf_pair [simp]: "spmf (pair_spmf p q) (x, y) = spmf p x * spmf q y" (is "?lhs = ?rhs")
proof -
  have "ennreal ?lhs = \<integral>\<^sup>+ a. \<integral>\<^sup>+ b. indicator {(x, y)} (a, b) \<partial>measure_spmf q \<partial>measure_spmf p"
    unfolding measure_spmf_def pair_spmf_def ennreal_pmf_bind nn_integral_pair_pmf'
    by(auto simp: zero_ereal_def[symmetric] nn_integral_distr nn_integral_restrict_space nn_integral_multc[symmetric] intro!: nn_integral_cong split: option.split split_indicator)
  also have "\<dots> = \<integral>\<^sup>+ a. (\<integral>\<^sup>+ b. indicator {y} b \<partial>measure_spmf q) * indicator {x} a \<partial>measure_spmf p"
    by(subst nn_integral_multc[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ennreal ?rhs" by(simp add: emeasure_spmf_single max_def ennreal_mult mult.commute)
  finally show ?thesis by simp
qed

lemma pair_map_spmf2: "pair_spmf p (map_spmf f q) = map_spmf (apsnd f) (pair_spmf p q)"
  unfolding pair_spmf_def pair_map_pmf2 bind_map_pmf map_bind_pmf
  by (intro bind_pmf_cong refl) (auto split: option.split)

lemma pair_map_spmf1: "pair_spmf (map_spmf f p) q = map_spmf (apfst f) (pair_spmf p q)"
  unfolding pair_spmf_def pair_map_pmf1 bind_map_pmf map_bind_pmf
  by (intro bind_pmf_cong refl) (auto split: option.split)

lemma pair_map_spmf: "pair_spmf (map_spmf f p) (map_spmf g q) = map_spmf (map_prod f g) (pair_spmf p q)"
  unfolding pair_map_spmf2 pair_map_spmf1 spmf.map_comp 
  by(simp add: apfst_def apsnd_def o_def prod.map_comp)

lemma pair_spmf_alt_def: "pair_spmf p q = bind_spmf p (\<lambda>x. bind_spmf q (\<lambda>y. return_spmf (x, y)))"
  unfolding pair_spmf_def pair_pmf_def bind_spmf_def bind_assoc_pmf bind_return_pmf
  by (intro bind_pmf_cong refl) (auto split: option.split)

lemma weight_pair_spmf [simp]: "weight_spmf (pair_spmf p q) = weight_spmf p * weight_spmf q"
  unfolding pair_spmf_alt_def by(simp add: weight_bind_spmf o_def)

lemma pair_scale_spmf1: (* FIXME: generalise to arbitrary r *)
  "r \<le> 1 \<Longrightarrow> pair_spmf (scale_spmf r p) q = scale_spmf r (pair_spmf p q)"
  by(simp add: pair_spmf_alt_def scale_bind_spmf bind_scale_spmf)

lemma pair_scale_spmf2: (* FIXME: generalise to arbitrary r *)
  "r \<le> 1 \<Longrightarrow> pair_spmf p (scale_spmf r q) = scale_spmf r (pair_spmf p q)"
  by(simp add: pair_spmf_alt_def scale_bind_spmf bind_scale_spmf)

lemma pair_spmf_return_None1 [simp]: "pair_spmf (return_pmf None) p = return_pmf None"
  by(rule spmf_eqI)(clarsimp)

lemma pair_spmf_return_None2 [simp]: "pair_spmf p (return_pmf None) = return_pmf None"
  by(rule spmf_eqI)(clarsimp)

lemma pair_spmf_return_spmf1: "pair_spmf (return_spmf x) q = map_spmf (Pair x) q"
  by(rule spmf_eqI)(auto split: split_indicator simp add: spmf_map_inj' inj_on_def intro: spmf_map_outside)

lemma pair_spmf_return_spmf2: "pair_spmf p (return_spmf y) = map_spmf (\<lambda>x. (x, y)) p"
  by(rule spmf_eqI)(auto split: split_indicator simp add: inj_on_def intro!: spmf_map_outside spmf_map_inj'[symmetric])

lemma pair_spmf_return_spmf [simp]: "pair_spmf (return_spmf x) (return_spmf y) = return_spmf (x, y)"
  by(simp add: pair_spmf_return_spmf1)

lemma rel_pair_spmf_prod:
  "rel_spmf (rel_prod A B) (pair_spmf p q) (pair_spmf p' q') \<longleftrightarrow>
   rel_spmf A (scale_spmf (weight_spmf q) p) (scale_spmf (weight_spmf q') p') \<and>
   rel_spmf B (scale_spmf (weight_spmf p) q) (scale_spmf (weight_spmf p') q')"
  (is "?lhs \<longleftrightarrow> ?rhs" is "_ \<longleftrightarrow> ?A \<and> ?B" is "_ \<longleftrightarrow> rel_spmf _ ?p ?p' \<and> rel_spmf _ ?q ?q'")
proof(intro iffI conjI)
  assume ?rhs
  then obtain pq pq' where p: "map_spmf fst pq = ?p" and p': "map_spmf snd pq = ?p'"
    and q: "map_spmf fst pq' = ?q" and q': "map_spmf snd pq' = ?q'"
    and *: "\<And>x x'. (x, x') \<in> set_spmf pq \<Longrightarrow> A x x'"
    and **: "\<And>y y'. (y, y') \<in> set_spmf pq' \<Longrightarrow> B y y'" by(auto elim!: rel_spmfE)
  let ?f = "\<lambda>((x, x'), (y, y')). ((x, y), (x', y'))"
  let ?r = "1 / (weight_spmf p * weight_spmf q)"
  let ?pq = "scale_spmf ?r (map_spmf ?f (pair_spmf pq pq'))"

  { fix p :: "'x spmf" and q :: "'y spmf"
    assume "weight_spmf q \<noteq> 0"
      and "weight_spmf p \<noteq> 0"
      and "1 / (weight_spmf p * weight_spmf q) \<le> weight_spmf p * weight_spmf q"
    hence "1 \<le> (weight_spmf p * weight_spmf q) * (weight_spmf p * weight_spmf q)"
      by(simp add: pos_divide_le_eq order.strict_iff_order weight_spmf_nonneg)
    moreover have "(weight_spmf p * weight_spmf q) * (weight_spmf p * weight_spmf q) \<le> (1 * 1) * (1 * 1)"
      by(intro mult_mono)(simp_all add: weight_spmf_nonneg weight_spmf_le_1)
    ultimately have "(weight_spmf p * weight_spmf q) * (weight_spmf p * weight_spmf q) = 1" by simp
    hence *: "weight_spmf p * weight_spmf q = 1"
      by(metis antisym_conv less_le mult_less_cancel_left1 weight_pair_spmf weight_spmf_le_1 weight_spmf_nonneg)
    hence **: "weight_spmf p = 1" by(metis antisym_conv mult_left_le weight_spmf_le_1 weight_spmf_nonneg)
    moreover from * ** have "weight_spmf q = 1" by simp
    moreover note calculation }
  note full = this

  show ?lhs
  proof
    have [simp]: "fst \<circ> ?f = map_prod fst fst" by(simp add: fun_eq_iff)
    have "map_spmf fst ?pq = scale_spmf ?r (pair_spmf ?p ?q)"
      by(simp add: pair_map_spmf[symmetric] p q map_scale_spmf spmf.map_comp)
    also have "\<dots> = pair_spmf p q" using full[of p q]
      by(simp add: pair_scale_spmf1 pair_scale_spmf2 weight_spmf_le_1 weight_spmf_nonneg)
        (auto simp: scale_scale_spmf max_def min_def field_simps weight_spmf_nonneg weight_spmf_eq_0)
    finally show "map_spmf fst ?pq = \<dots>" .

    have [simp]: "snd \<circ> ?f = map_prod snd snd" by(simp add: fun_eq_iff)
    from \<open>?rhs\<close> have eq: "weight_spmf p * weight_spmf q = weight_spmf p' * weight_spmf q'"
      by(auto dest!: rel_spmf_weightD simp add: weight_spmf_le_1 weight_spmf_nonneg)

    have "map_spmf snd ?pq = scale_spmf ?r (pair_spmf ?p' ?q')"
      by(simp add: pair_map_spmf[symmetric] p' q' map_scale_spmf spmf.map_comp)
    also have "\<dots> = pair_spmf p' q'" using full[of p' q'] eq
      by(simp add: pair_scale_spmf1 pair_scale_spmf2 weight_spmf_le_1 weight_spmf_nonneg)
        (auto simp: scale_scale_spmf max_def min_def field_simps weight_spmf_nonneg weight_spmf_eq_0)
    finally show "map_spmf snd ?pq = \<dots>" .
  qed(auto simp: set_scale_spmf split: if_split_asm dest: * ** )
next
  assume ?lhs
  then obtain pq where pq: "map_spmf fst pq = pair_spmf p q"
    and pq': "map_spmf snd pq = pair_spmf p' q'"
    and *: "\<And>x y x' y'. ((x, y), (x', y')) \<in> set_spmf pq \<Longrightarrow> A x x' \<and> B y y'"
    by(auto elim: rel_spmfE)

  show ?A
  proof
    let ?f = "(\<lambda>((x, y), (x', y')). (x, x'))"
    let ?pq = "map_spmf ?f pq"
    have [simp]: "fst \<circ> ?f = fst \<circ> fst" by(simp add: split_def o_def)
    show "map_spmf fst ?pq = scale_spmf (weight_spmf q) p" using pq
      by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric])

    have [simp]: "snd \<circ> ?f = fst \<circ> snd" by(simp add: split_def o_def)
    show "map_spmf snd ?pq = scale_spmf (weight_spmf q') p'" using pq'
      by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric])
  qed(auto dest: * )

  show ?B
  proof
    let ?f = "(\<lambda>((x, y), (x', y')). (y, y'))"
    let ?pq = "map_spmf ?f pq"
    have [simp]: "fst \<circ> ?f = snd \<circ> fst" by(simp add: split_def o_def)
    show "map_spmf fst ?pq = scale_spmf (weight_spmf p) q" using pq
      by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric])

    have [simp]: "snd \<circ> ?f = snd \<circ> snd" by(simp add: split_def o_def)
    show "map_spmf snd ?pq = scale_spmf (weight_spmf p') q'" using pq'
      by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric])
  qed(auto dest: * )
qed

lemma pair_pair_spmf:
  "pair_spmf (pair_spmf p q) r = map_spmf (\<lambda>(x, (y, z)). ((x, y), z)) (pair_spmf p (pair_spmf q r))"
  by(simp add: pair_spmf_alt_def map_spmf_conv_bind_spmf)

lemma pair_commute_spmf:
  "pair_spmf p q = map_spmf (\<lambda>(y, x). (x, y)) (pair_spmf q p)"
  unfolding pair_spmf_alt_def by(subst bind_commute_spmf)(simp add: map_spmf_conv_bind_spmf)

subsection \<open>Assertions\<close>

definition assert_spmf :: "bool \<Rightarrow> unit spmf"
  where "assert_spmf b = (if b then return_spmf () else return_pmf None)"

lemma assert_spmf_simps [simp]:
  "assert_spmf True = return_spmf ()"
  "assert_spmf False = return_pmf None"
  by(simp_all add: assert_spmf_def)

lemma in_set_assert_spmf [simp]: "x \<in> set_spmf (assert_spmf p) \<longleftrightarrow> p"
  by(cases p) simp_all

lemma set_spmf_assert_spmf_eq_empty [simp]: "set_spmf (assert_spmf b) = {} \<longleftrightarrow> \<not> b"
  by auto

lemma lossless_assert_spmf [iff]: "lossless_spmf (assert_spmf b) \<longleftrightarrow> b"
  by(cases b) simp_all

subsection \<open>Try\<close>

definition try_spmf :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> 'a spmf"
  (\<open>(\<open>open_block notation=\<open>mixfix try_spmf\<close>\<close>TRY _ ELSE _)\<close> [0,60] 59)
where "TRY p ELSE q = bind_pmf p (\<lambda>x. case x of None \<Rightarrow> q | Some y \<Rightarrow> return_spmf y)"

lemma try_spmf_lossless [simp]:
  assumes "lossless_spmf p"
  shows "TRY p ELSE q = p"
proof -
  have "TRY p ELSE q = bind_pmf p return_pmf" unfolding try_spmf_def using assms
    by(auto simp: lossless_iff_set_pmf_None split: option.split intro: bind_pmf_cong)
  thus ?thesis by(simp add: bind_return_pmf')
qed

lemma try_spmf_return_spmf1: "TRY return_spmf x ELSE q = return_spmf x"
  by simp

lemma try_spmf_return_None [simp]: "TRY return_pmf None ELSE q = q"
  by(simp add: try_spmf_def bind_return_pmf)

lemma try_spmf_return_pmf_None2 [simp]: "TRY p ELSE return_pmf None = p"
  by(simp add: try_spmf_def option.case_distrib[symmetric] bind_return_pmf' case_option_id)

lemma map_try_spmf: "map_spmf f (try_spmf p q) = try_spmf (map_spmf f p) (map_spmf f q)"
  by(simp add: try_spmf_def map_bind_pmf bind_map_pmf option.case_distrib[where h="map_spmf f"] o_def cong del: option.case_cong_weak)

lemma try_spmf_bind_pmf: "TRY (bind_pmf p f) ELSE q = bind_pmf p (\<lambda>x. TRY (f x) ELSE q)"
  by(simp add: try_spmf_def bind_assoc_pmf)

lemma try_spmf_bind_spmf_lossless:
  "lossless_spmf p \<Longrightarrow> TRY (bind_spmf p f) ELSE q = bind_spmf p (\<lambda>x. TRY (f x) ELSE q)"
  by (metis (mono_tags, lifting) bind_spmf_of_pmf lossless_spmf_conv_spmf_of_pmf try_spmf_bind_pmf)

lemma try_spmf_bind_out:
  "lossless_spmf p \<Longrightarrow> bind_spmf p (\<lambda>x. TRY (f x) ELSE q) = TRY (bind_spmf p f) ELSE q"
  by(simp add: try_spmf_bind_spmf_lossless)

lemma lossless_try_spmf [simp]:
  "lossless_spmf (TRY p ELSE q) \<longleftrightarrow> lossless_spmf p \<or> lossless_spmf q"
  by(auto simp: try_spmf_def in_set_spmf lossless_iff_set_pmf_None split: option.splits)

context includes lifting_syntax
begin

lemma try_spmf_parametric [transfer_rule]:
  "(rel_spmf A ===> rel_spmf A ===> rel_spmf A) try_spmf try_spmf"
  unfolding try_spmf_def[abs_def] by transfer_prover

end

lemma try_spmf_cong:
  "\<lbrakk> p = p'; \<not> lossless_spmf p' \<Longrightarrow> q = q' \<rbrakk> \<Longrightarrow> TRY p ELSE q = TRY p' ELSE q'"
  unfolding try_spmf_def
  by(rule bind_pmf_cong)(auto split: option.split simp add: lossless_iff_set_pmf_None)

lemma rel_spmf_try_spmf:
  "\<lbrakk> rel_spmf R p p'; \<not> lossless_spmf p' \<Longrightarrow> rel_spmf R q q' \<rbrakk>
  \<Longrightarrow> rel_spmf R (TRY p ELSE q) (TRY p' ELSE q')"
  unfolding try_spmf_def
  apply(rule rel_pmf_bindI[where R="\<lambda>x y. rel_option R x y \<and> x \<in> set_pmf p \<and> y \<in> set_pmf p'"])
  apply (simp add: pmf.rel_mono_strong)
  apply(auto split: option.split simp add: lossless_iff_set_pmf_None)
  done

lemma spmf_try_spmf:
  "spmf (TRY p ELSE q) x = spmf p x + pmf p None * spmf q x"
proof -
  have "ennreal (spmf (TRY p ELSE q) x) = \<integral>\<^sup>+ y. ennreal (spmf q x) * indicator {None} y + indicator {Some x} y \<partial>measure_pmf p"
    unfolding try_spmf_def ennreal_pmf_bind by(rule nn_integral_cong)(simp split: option.split split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (spmf q x) * indicator {None} y \<partial>measure_pmf p) + \<integral>\<^sup>+ y. indicator {Some x} y \<partial>measure_pmf p"
    by(simp add: nn_integral_add)
  also have "\<dots> = ennreal (spmf q x) * pmf p None + spmf p x" by(simp add: emeasure_pmf_single)
  finally show ?thesis by(simp flip: ennreal_plus ennreal_mult)
qed

lemma try_scale_spmf_same [simp]: "lossless_spmf p \<Longrightarrow> TRY scale_spmf k p ELSE p = p"
  by(rule spmf_eqI)(auto simp: spmf_try_spmf spmf_scale_spmf pmf_scale_spmf_None lossless_iff_pmf_None weight_spmf_conv_pmf_None min_def max_def field_simps)

lemma pmf_try_spmf_None [simp]: "pmf (TRY p ELSE q) None = pmf p None * pmf q None" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<integral> x. pmf q None * indicator {None} x \<partial>measure_pmf p"
    unfolding try_spmf_def pmf_bind by(rule Bochner_Integration.integral_cong)(simp_all split: option.split)
  also have "\<dots> = ?rhs" by(simp add: measure_pmf_single)
  finally show ?thesis .
qed

lemma try_bind_spmf_lossless2:
  "lossless_spmf q \<Longrightarrow> TRY (bind_spmf p f) ELSE q = TRY (p \<bind> (\<lambda>x. TRY (f x) ELSE q)) ELSE q"
by(rule spmf_eqI)(simp add: spmf_try_spmf pmf_bind_spmf_None spmf_bind field_simps measure_spmf.integrable_const_bound[where B=1] pmf_le_1 lossless_iff_pmf_None)

lemma try_bind_spmf_lossless2':
  fixes f :: "'a \<Rightarrow> 'b spmf" shows
  "\<lbrakk> NO_MATCH (\<lambda>x :: 'a. try_spmf (g x :: 'b spmf) (h x)) f; lossless_spmf q \<rbrakk>
  \<Longrightarrow> TRY (bind_spmf p f) ELSE q = TRY (p \<bind> (\<lambda>x :: 'a. TRY (f x) ELSE q)) ELSE q"
by(rule try_bind_spmf_lossless2)

lemma try_bind_assert_spmf:
  "TRY (assert_spmf b \<bind> f) ELSE q = (if b then TRY (f ()) ELSE q else q)"
by simp

subsection \<open>Miscellaneous\<close>

lemma assumes "rel_spmf (\<lambda>x y. bad1 x = bad2 y \<and> (\<not> bad2 y \<longrightarrow> A x \<longleftrightarrow> B y)) p q" (is "rel_spmf ?A _ _")
  shows fundamental_lemma_bad: "measure (measure_spmf p) {x. bad1 x} = measure (measure_spmf q) {y. bad2 y}" (is "?bad")
  and fundamental_lemma: "\<bar>measure (measure_spmf p) {x. A x} - measure (measure_spmf q) {y. B y}\<bar> \<le>
    measure (measure_spmf p) {x. bad1 x}" (is ?fundamental)
proof -
  have good: "rel_fun ?A (=) (\<lambda>x. A x \<and> \<not> bad1 x) (\<lambda>y. B y \<and> \<not> bad2 y)" by(auto simp: rel_fun_def)
  from assms have 1: "measure (measure_spmf p) {x. A x \<and> \<not> bad1 x} = measure (measure_spmf q) {y. B y \<and> \<not> bad2 y}"
    by(rule measure_spmf_parametric[THEN rel_funD, THEN rel_funD])(rule Collect_parametric[THEN rel_funD, OF good])

  have bad: "rel_fun ?A (=) bad1 bad2" by(simp add: rel_fun_def)
  show 2: ?bad using assms
    by(rule measure_spmf_parametric[THEN rel_funD, THEN rel_funD])(rule Collect_parametric[THEN rel_funD, OF bad])

  let ?\<mu>p = "measure (measure_spmf p)" and ?\<mu>q = "measure (measure_spmf q)"
  have "{x. A x \<and> bad1 x} \<union> {x. A x \<and> \<not> bad1 x} = {x. A x}"
    and "{y. B y \<and> bad2 y} \<union> {y. B y \<and> \<not> bad2 y} = {y. B y}" by auto
  then have "\<bar>?\<mu>p {x. A x} - ?\<mu>q {x. B x}\<bar> = \<bar>?\<mu>p ({x. A x \<and> bad1 x} \<union> {x. A x \<and> \<not> bad1 x}) - ?\<mu>q ({y. B y \<and> bad2 y} \<union> {y. B y \<and> \<not> bad2 y})\<bar>"
    by simp
  also have "\<dots> = \<bar>?\<mu>p {x. A x \<and> bad1 x} + ?\<mu>p {x. A x \<and> \<not> bad1 x} - ?\<mu>q {y. B y \<and> bad2 y} - ?\<mu>q {y. B y \<and> \<not> bad2 y}\<bar>"
    by(subst (1 2) measure_Union)(auto)
  also have "\<dots> = \<bar>?\<mu>p {x. A x \<and> bad1 x} - ?\<mu>q {y. B y \<and> bad2 y}\<bar>" using 1 by simp
  also have "\<dots> \<le> max (?\<mu>p {x. A x \<and> bad1 x}) (?\<mu>q {y. B y \<and> bad2 y})"
    by(rule abs_leI)(auto simp: max_def not_le, simp_all only: add_increasing measure_nonneg mult_2)
  also have "\<dots> \<le> max (?\<mu>p {x. bad1 x}) (?\<mu>q {y. bad2 y})"
    by(rule max.mono; rule measure_spmf.finite_measure_mono; auto)
  also note 2[symmetric]
  finally show ?fundamental by simp
qed

end
