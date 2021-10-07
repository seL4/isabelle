(*
  Title:    HOL/Analysis/Infinite_Set_Sum.thy
  Author:   Manuel Eberl, TU München

  A theory of sums over possible infinite sets. (Only works for absolute summability)
*)
section \<open>Sums over Infinite Sets\<close>

theory Infinite_Set_Sum
  imports Set_Integral Infinite_Sum
begin

text \<open>Conflicting notation from \<^theory>\<open>HOL-Analysis.Infinite_Sum\<close>\<close>
no_notation Infinite_Sum.abs_summable_on (infixr "abs'_summable'_on" 46)

(* TODO Move *)
lemma sets_eq_countable:
  assumes "countable A" "space M = A" "\<And>x. x \<in> A \<Longrightarrow> {x} \<in> sets M"
  shows   "sets M = Pow A"
proof (intro equalityI subsetI)
  fix X assume "X \<in> Pow A"
  hence "(\<Union>x\<in>X. {x}) \<in> sets M"
    by (intro sets.countable_UN' countable_subset[OF _ assms(1)]) (auto intro!: assms(3))
  also have "(\<Union>x\<in>X. {x}) = X" by auto
  finally show "X \<in> sets M" .
next
  fix X assume "X \<in> sets M"
  from sets.sets_into_space[OF this] and assms
    show "X \<in> Pow A" by simp
qed

lemma measure_eqI_countable':
  assumes spaces: "space M = A" "space N = A"
  assumes sets: "\<And>x. x \<in> A \<Longrightarrow> {x} \<in> sets M" "\<And>x. x \<in> A \<Longrightarrow> {x} \<in> sets N"
  assumes A: "countable A"
  assumes eq: "\<And>a. a \<in> A \<Longrightarrow> emeasure M {a} = emeasure N {a}"
  shows "M = N"
proof (rule measure_eqI_countable)
  show "sets M = Pow A"
    by (intro sets_eq_countable assms)
  show "sets N = Pow A"
    by (intro sets_eq_countable assms)
qed fact+

lemma count_space_PiM_finite:
  fixes B :: "'a \<Rightarrow> 'b set"
  assumes "finite A" "\<And>i. countable (B i)"
  shows   "PiM A (\<lambda>i. count_space (B i)) = count_space (PiE A B)"
proof (rule measure_eqI_countable')
  show "space (PiM A (\<lambda>i. count_space (B i))) = PiE A B"
    by (simp add: space_PiM)
  show "space (count_space (PiE A B)) = PiE A B" by simp
next
  fix f assume f: "f \<in> PiE A B"
  hence "PiE A (\<lambda>x. {f x}) \<in> sets (Pi\<^sub>M A (\<lambda>i. count_space (B i)))"
    by (intro sets_PiM_I_finite assms) auto
  also from f have "PiE A (\<lambda>x. {f x}) = {f}"
    by (intro PiE_singleton) (auto simp: PiE_def)
  finally show "{f} \<in> sets (Pi\<^sub>M A (\<lambda>i. count_space (B i)))" .
next
  interpret product_sigma_finite "(\<lambda>i. count_space (B i))"
    by (intro product_sigma_finite.intro sigma_finite_measure_count_space_countable assms)
  thm sigma_finite_measure_count_space
  fix f assume f: "f \<in> PiE A B"
  hence "{f} = PiE A (\<lambda>x. {f x})"
    by (intro PiE_singleton [symmetric]) (auto simp: PiE_def)
  also have "emeasure (Pi\<^sub>M A (\<lambda>i. count_space (B i))) \<dots> =
               (\<Prod>i\<in>A. emeasure (count_space (B i)) {f i})"
    using f assms by (subst emeasure_PiM) auto
  also have "\<dots> = (\<Prod>i\<in>A. 1)"
    by (intro prod.cong refl, subst emeasure_count_space_finite) (use f in auto)
  also have "\<dots> = emeasure (count_space (PiE A B)) {f}"
    using f by (subst emeasure_count_space_finite) auto
  finally show "emeasure (Pi\<^sub>M A (\<lambda>i. count_space (B i))) {f} =
                  emeasure (count_space (Pi\<^sub>E A B)) {f}" .
qed (simp_all add: countable_PiE assms)



definition\<^marker>\<open>tag important\<close> abs_summable_on ::
    "('a \<Rightarrow> 'b :: {banach, second_countable_topology}) \<Rightarrow> 'a set \<Rightarrow> bool"
    (infix "abs'_summable'_on" 50)
 where
   "f abs_summable_on A \<longleftrightarrow> integrable (count_space A) f"


definition\<^marker>\<open>tag important\<close> infsetsum ::
    "('a \<Rightarrow> 'b :: {banach, second_countable_topology}) \<Rightarrow> 'a set \<Rightarrow> 'b"
 where
   "infsetsum f A = lebesgue_integral (count_space A) f"

syntax (ASCII)
  "_infsetsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::{banach, second_countable_topology}"
  ("(3INFSETSUM _:_./ _)" [0, 51, 10] 10)
syntax
  "_infsetsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::{banach, second_countable_topology}"
  ("(2\<Sum>\<^sub>a_\<in>_./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>\<^sub>ai\<in>A. b" \<rightleftharpoons> "CONST infsetsum (\<lambda>i. b) A"

syntax (ASCII)
  "_uinfsetsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::{banach, second_countable_topology}"
  ("(3INFSETSUM _:_./ _)" [0, 51, 10] 10)
syntax
  "_uinfsetsum" :: "pttrn \<Rightarrow> 'b \<Rightarrow> 'b::{banach, second_countable_topology}"
  ("(2\<Sum>\<^sub>a_./ _)" [0, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>\<^sub>ai. b" \<rightleftharpoons> "CONST infsetsum (\<lambda>i. b) (CONST UNIV)"

syntax (ASCII)
  "_qinfsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a::{banach, second_countable_topology}"
  ("(3INFSETSUM _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qinfsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a::{banach, second_countable_topology}"
  ("(2\<Sum>\<^sub>a_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>\<^sub>ax|P. t" => "CONST infsetsum (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun sum_tr' [Abs (x, Tx, t), Const (\<^const_syntax>\<open>Collect\<close>, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const \<^syntax_const>\<open>_qinfsetsum\<close> $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | sum_tr' _ = raise Match;
in [(\<^const_syntax>\<open>infsetsum\<close>, K sum_tr')] end
\<close>


lemma restrict_count_space_subset:
  "A \<subseteq> B \<Longrightarrow> restrict_space (count_space B) A = count_space A"
  by (subst restrict_count_space) (simp_all add: Int_absorb2)

lemma abs_summable_on_restrict:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, second_countable_topology}"
  assumes "A \<subseteq> B"
  shows   "f abs_summable_on A \<longleftrightarrow> (\<lambda>x. indicator A x *\<^sub>R f x) abs_summable_on B"
proof -
  have "count_space A = restrict_space (count_space B) A"
    by (rule restrict_count_space_subset [symmetric]) fact+
  also have "integrable \<dots> f \<longleftrightarrow> set_integrable (count_space B) A f"
    by (simp add: integrable_restrict_space set_integrable_def)
  finally show ?thesis
    unfolding abs_summable_on_def set_integrable_def .
qed

lemma abs_summable_on_altdef: "f abs_summable_on A \<longleftrightarrow> set_integrable (count_space UNIV) A f"
  unfolding abs_summable_on_def set_integrable_def
  by (metis (no_types) inf_top.right_neutral integrable_restrict_space restrict_count_space sets_UNIV)

lemma abs_summable_on_altdef':
  "A \<subseteq> B \<Longrightarrow> f abs_summable_on A \<longleftrightarrow> set_integrable (count_space B) A f"
  unfolding abs_summable_on_def set_integrable_def
  by (metis (no_types) Pow_iff abs_summable_on_def inf.orderE integrable_restrict_space restrict_count_space_subset sets_count_space space_count_space)

lemma abs_summable_on_norm_iff [simp]:
  "(\<lambda>x. norm (f x)) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
  by (simp add: abs_summable_on_def integrable_norm_iff)

lemma abs_summable_on_normI: "f abs_summable_on A \<Longrightarrow> (\<lambda>x. norm (f x)) abs_summable_on A"
  by simp

lemma abs_summable_complex_of_real [simp]: "(\<lambda>n. complex_of_real (f n)) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
  by (simp add: abs_summable_on_def complex_of_real_integrable_eq)

lemma abs_summable_on_comparison_test:
  assumes "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> norm (g x)"
  shows   "f abs_summable_on A"
  using assms Bochner_Integration.integrable_bound[of "count_space A" g f]
  unfolding abs_summable_on_def by (auto simp: AE_count_space)

lemma abs_summable_on_comparison_test':
  assumes "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> g x"
  shows   "f abs_summable_on A"
proof (rule abs_summable_on_comparison_test[OF assms(1), of f])
  fix x assume "x \<in> A"
  with assms(2) have "norm (f x) \<le> g x" .
  also have "\<dots> \<le> norm (g x)" by simp
  finally show "norm (f x) \<le> norm (g x)" .
qed

lemma abs_summable_on_cong [cong]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> A = B \<Longrightarrow> (f abs_summable_on A) \<longleftrightarrow> (g abs_summable_on B)"
  unfolding abs_summable_on_def by (intro integrable_cong) auto

lemma abs_summable_on_cong_neutral:
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x = 0"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> g x = 0"
  assumes "\<And>x. x \<in> A \<inter> B \<Longrightarrow> f x = g x"
  shows   "f abs_summable_on A \<longleftrightarrow> g abs_summable_on B"
  unfolding abs_summable_on_altdef set_integrable_def using assms
  by (intro Bochner_Integration.integrable_cong refl)
     (auto simp: indicator_def split: if_splits)

lemma abs_summable_on_restrict':
  fixes f :: "'a \<Rightarrow> 'b :: {banach, second_countable_topology}"
  assumes "A \<subseteq> B"
  shows   "f abs_summable_on A \<longleftrightarrow> (\<lambda>x. if x \<in> A then f x else 0) abs_summable_on B"
  by (subst abs_summable_on_restrict[OF assms]) (intro abs_summable_on_cong, auto)

lemma abs_summable_on_nat_iff:
  "f abs_summable_on (A :: nat set) \<longleftrightarrow> summable (\<lambda>n. if n \<in> A then norm (f n) else 0)"
proof -
  have "f abs_summable_on A \<longleftrightarrow> summable (\<lambda>x. norm (if x \<in> A then f x else 0))"
    by (subst abs_summable_on_restrict'[of _ UNIV])
       (simp_all add: abs_summable_on_def integrable_count_space_nat_iff)
  also have "(\<lambda>x. norm (if x \<in> A then f x else 0)) = (\<lambda>x. if x \<in> A then norm (f x) else 0)"
    by auto
  finally show ?thesis .
qed

lemma abs_summable_on_nat_iff':
  "f abs_summable_on (UNIV :: nat set) \<longleftrightarrow> summable (\<lambda>n. norm (f n))"
  by (subst abs_summable_on_nat_iff) auto

lemma nat_abs_summable_on_comparison_test:
  fixes f :: "nat \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes "g abs_summable_on I"
  assumes "\<And>n. \<lbrakk>n\<ge>N; n \<in> I\<rbrakk> \<Longrightarrow> norm (f n) \<le> g n"
  shows   "f abs_summable_on I"
  using assms by (fastforce simp add: abs_summable_on_nat_iff intro: summable_comparison_test')

lemma abs_summable_comparison_test_ev:
  assumes "g abs_summable_on I"
  assumes "eventually (\<lambda>x. x \<in> I \<longrightarrow> norm (f x) \<le> g x) sequentially"
  shows   "f abs_summable_on I"
  by (metis (no_types, lifting) nat_abs_summable_on_comparison_test eventually_at_top_linorder assms)

lemma abs_summable_on_Cauchy:
  "f abs_summable_on (UNIV :: nat set) \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n. (\<Sum>x = m..<n. norm (f x)) < e)"
  by (simp add: abs_summable_on_nat_iff' summable_Cauchy sum_nonneg)

lemma abs_summable_on_finite [simp]: "finite A \<Longrightarrow> f abs_summable_on A"
  unfolding abs_summable_on_def by (rule integrable_count_space)

lemma abs_summable_on_empty [simp, intro]: "f abs_summable_on {}"
  by simp

lemma abs_summable_on_subset:
  assumes "f abs_summable_on B" and "A \<subseteq> B"
  shows   "f abs_summable_on A"
  unfolding abs_summable_on_altdef
  by (rule set_integrable_subset) (insert assms, auto simp: abs_summable_on_altdef)

lemma abs_summable_on_union [intro]:
  assumes "f abs_summable_on A" and "f abs_summable_on B"
  shows   "f abs_summable_on (A \<union> B)"
  using assms unfolding abs_summable_on_altdef by (intro set_integrable_Un) auto

lemma abs_summable_on_insert_iff [simp]:
  "f abs_summable_on insert x A \<longleftrightarrow> f abs_summable_on A"
proof safe
  assume "f abs_summable_on insert x A"
  thus "f abs_summable_on A"
    by (rule abs_summable_on_subset) auto
next
  assume "f abs_summable_on A"
  from abs_summable_on_union[OF this, of "{x}"]
    show "f abs_summable_on insert x A" by simp
qed

lemma abs_summable_sum:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B"
  shows   "(\<lambda>y. \<Sum>x\<in>A. f x y) abs_summable_on B"
  using assms unfolding abs_summable_on_def by (intro Bochner_Integration.integrable_sum)

lemma abs_summable_Re: "f abs_summable_on A \<Longrightarrow> (\<lambda>x. Re (f x)) abs_summable_on A"
  by (simp add: abs_summable_on_def)

lemma abs_summable_Im: "f abs_summable_on A \<Longrightarrow> (\<lambda>x. Im (f x)) abs_summable_on A"
  by (simp add: abs_summable_on_def)

lemma abs_summable_on_finite_diff:
  assumes "f abs_summable_on A" "A \<subseteq> B" "finite (B - A)"
  shows   "f abs_summable_on B"
proof -
  have "f abs_summable_on (A \<union> (B - A))"
    by (intro abs_summable_on_union assms abs_summable_on_finite)
  also from assms have "A \<union> (B - A) = B" by blast
  finally show ?thesis .
qed

lemma abs_summable_on_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "(\<lambda>x. f (g x)) abs_summable_on A \<longleftrightarrow> f abs_summable_on B"
proof -
  have *: "count_space B = distr (count_space A) (count_space B) g"
    by (rule distr_bij_count_space [symmetric]) fact
  show ?thesis unfolding abs_summable_on_def
    by (subst *, subst integrable_distr_eq[of _ _ "count_space B"])
       (insert assms, auto simp: bij_betw_def)
qed

lemma abs_summable_on_reindex:
  assumes "(\<lambda>x. f (g x)) abs_summable_on A"
  shows   "f abs_summable_on (g ` A)"
proof -
  define g' where "g' = inv_into A g"
  from assms have "(\<lambda>x. f (g x)) abs_summable_on (g' ` g ` A)"
    by (rule abs_summable_on_subset) (auto simp: g'_def inv_into_into)
  also have "?this \<longleftrightarrow> (\<lambda>x. f (g (g' x))) abs_summable_on (g ` A)" unfolding g'_def
    by (intro abs_summable_on_reindex_bij_betw [symmetric] inj_on_imp_bij_betw inj_on_inv_into) auto
  also have "\<dots> \<longleftrightarrow> f abs_summable_on (g ` A)"
    by (intro abs_summable_on_cong refl) (auto simp: g'_def f_inv_into_f)
  finally show ?thesis .
qed

lemma abs_summable_on_reindex_iff:
  "inj_on g A \<Longrightarrow> (\<lambda>x. f (g x)) abs_summable_on A \<longleftrightarrow> f abs_summable_on (g ` A)"
  by (intro abs_summable_on_reindex_bij_betw inj_on_imp_bij_betw)

lemma abs_summable_on_Sigma_project2:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes "f abs_summable_on (Sigma A B)" "x \<in> A"
  shows   "(\<lambda>y. f (x, y)) abs_summable_on (B x)"
proof -
  from assms(2) have "f abs_summable_on (Sigma {x} B)"
    by (intro abs_summable_on_subset [OF assms(1)]) auto
  also have "?this \<longleftrightarrow> (\<lambda>z. f (x, snd z)) abs_summable_on (Sigma {x} B)"
    by (rule abs_summable_on_cong) auto
  finally have "(\<lambda>y. f (x, y)) abs_summable_on (snd ` Sigma {x} B)"
    by (rule abs_summable_on_reindex)
  also have "snd ` Sigma {x} B = B x"
    using assms by (auto simp: image_iff)
  finally show ?thesis .
qed

lemma abs_summable_on_Times_swap:
  "f abs_summable_on A \<times> B \<longleftrightarrow> (\<lambda>(x,y). f (y,x)) abs_summable_on B \<times> A"
proof -
  have bij: "bij_betw (\<lambda>(x,y). (y,x)) (B \<times> A) (A \<times> B)"
    by (auto simp: bij_betw_def inj_on_def)
  show ?thesis
    by (subst abs_summable_on_reindex_bij_betw[OF bij, of f, symmetric])
       (simp_all add: case_prod_unfold)
qed

lemma abs_summable_on_0 [simp, intro]: "(\<lambda>_. 0) abs_summable_on A"
  by (simp add: abs_summable_on_def)

lemma abs_summable_on_uminus [intro]:
  "f abs_summable_on A \<Longrightarrow> (\<lambda>x. -f x) abs_summable_on A"
  unfolding abs_summable_on_def by (rule Bochner_Integration.integrable_minus)

lemma abs_summable_on_add [intro]:
  assumes "f abs_summable_on A" and "g abs_summable_on A"
  shows   "(\<lambda>x. f x + g x) abs_summable_on A"
  using assms unfolding abs_summable_on_def by (rule Bochner_Integration.integrable_add)

lemma abs_summable_on_diff [intro]:
  assumes "f abs_summable_on A" and "g abs_summable_on A"
  shows   "(\<lambda>x. f x - g x) abs_summable_on A"
  using assms unfolding abs_summable_on_def by (rule Bochner_Integration.integrable_diff)

lemma abs_summable_on_scaleR_left [intro]:
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>R c) abs_summable_on A"
  using assms unfolding abs_summable_on_def by (intro Bochner_Integration.integrable_scaleR_left)

lemma abs_summable_on_scaleR_right [intro]:
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>R f x) abs_summable_on A"
  using assms unfolding abs_summable_on_def by (intro Bochner_Integration.integrable_scaleR_right)

lemma abs_summable_on_cmult_right [intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology}"
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c * f x) abs_summable_on A"
  using assms unfolding abs_summable_on_def by (intro Bochner_Integration.integrable_mult_right)

lemma abs_summable_on_cmult_left [intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology}"
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x * c) abs_summable_on A"
  using assms unfolding abs_summable_on_def by (intro Bochner_Integration.integrable_mult_left)

lemma abs_summable_on_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field,banach,second_countable_topology}"
  assumes finite: "finite A" and countable: "\<And>x. x \<in> A \<Longrightarrow> countable (B x)"
  assumes summable: "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows   "(\<lambda>g. \<Prod>x\<in>A. f x (g x)) abs_summable_on PiE A B"
proof -
  define B' where "B' = (\<lambda>x. if x \<in> A then B x else {})"
  from assms have [simp]: "countable (B' x)" for x
    by (auto simp: B'_def)
  then interpret product_sigma_finite "count_space \<circ> B'"
    unfolding o_def by (intro product_sigma_finite.intro sigma_finite_measure_count_space_countable)
  from assms have "integrable (PiM A (count_space \<circ> B')) (\<lambda>g. \<Prod>x\<in>A. f x (g x))"
    by (intro product_integrable_prod) (auto simp: abs_summable_on_def B'_def)
  also have "PiM A (count_space \<circ> B') = count_space (PiE A B')"
    unfolding o_def using finite by (intro count_space_PiM_finite) simp_all
  also have "PiE A B' = PiE A B" by (intro PiE_cong) (simp_all add: B'_def)
  finally show ?thesis by (simp add: abs_summable_on_def)
qed



lemma not_summable_infsetsum_eq:
  "\<not>f abs_summable_on A \<Longrightarrow> infsetsum f A = 0"
  by (simp add: abs_summable_on_def infsetsum_def not_integrable_integral_eq)

lemma infsetsum_altdef:
  "infsetsum f A = set_lebesgue_integral (count_space UNIV) A f"
  unfolding set_lebesgue_integral_def
  by (subst integral_restrict_space [symmetric])
     (auto simp: restrict_count_space_subset infsetsum_def)

lemma infsetsum_altdef':
  "A \<subseteq> B \<Longrightarrow> infsetsum f A = set_lebesgue_integral (count_space B) A f"
  unfolding set_lebesgue_integral_def
  by (subst integral_restrict_space [symmetric])
     (auto simp: restrict_count_space_subset infsetsum_def)

lemma nn_integral_conv_infsetsum:
  assumes "f abs_summable_on A" "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  shows   "nn_integral (count_space A) f = ennreal (infsetsum f A)"
  using assms unfolding infsetsum_def abs_summable_on_def
  by (subst nn_integral_eq_integral) auto

lemma infsetsum_conv_nn_integral:
  assumes "nn_integral (count_space A) f \<noteq> \<infinity>" "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  shows   "infsetsum f A = enn2real (nn_integral (count_space A) f)"
  unfolding infsetsum_def using assms
  by (subst integral_eq_nn_integral) auto

lemma infsetsum_cong [cong]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> A = B \<Longrightarrow> infsetsum f A = infsetsum g B"
  unfolding infsetsum_def by (intro Bochner_Integration.integral_cong) auto

lemma infsetsum_0 [simp]: "infsetsum (\<lambda>_. 0) A = 0"
  by (simp add: infsetsum_def)

lemma infsetsum_all_0: "(\<And>x. x \<in> A \<Longrightarrow> f x = 0) \<Longrightarrow> infsetsum f A = 0"
  by simp

lemma infsetsum_nonneg: "(\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (0::real)) \<Longrightarrow> infsetsum f A \<ge> 0"
  unfolding infsetsum_def by (rule Bochner_Integration.integral_nonneg) auto

lemma sum_infsetsum:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B"
  shows   "(\<Sum>x\<in>A. \<Sum>\<^sub>ay\<in>B. f x y) = (\<Sum>\<^sub>ay\<in>B. \<Sum>x\<in>A. f x y)"
  using assms by (simp add: infsetsum_def abs_summable_on_def Bochner_Integration.integral_sum)

lemma Re_infsetsum: "f abs_summable_on A \<Longrightarrow> Re (infsetsum f A) = (\<Sum>\<^sub>ax\<in>A. Re (f x))"
  by (simp add: infsetsum_def abs_summable_on_def)

lemma Im_infsetsum: "f abs_summable_on A \<Longrightarrow> Im (infsetsum f A) = (\<Sum>\<^sub>ax\<in>A. Im (f x))"
  by (simp add: infsetsum_def abs_summable_on_def)

lemma infsetsum_of_real:
  shows "infsetsum (\<lambda>x. of_real (f x)
           :: 'a :: {real_normed_algebra_1,banach,second_countable_topology,real_inner}) A =
             of_real (infsetsum f A)"
  unfolding infsetsum_def
  by (rule integral_bounded_linear'[OF bounded_linear_of_real bounded_linear_inner_left[of 1]]) auto

lemma infsetsum_finite [simp]: "finite A \<Longrightarrow> infsetsum f A = (\<Sum>x\<in>A. f x)"
  by (simp add: infsetsum_def lebesgue_integral_count_space_finite)

lemma infsetsum_nat:
  assumes "f abs_summable_on A"
  shows   "infsetsum f A = (\<Sum>n. if n \<in> A then f n else 0)"
proof -
  from assms have "infsetsum f A = (\<Sum>n. indicator A n *\<^sub>R f n)"
    unfolding infsetsum_altdef abs_summable_on_altdef set_lebesgue_integral_def set_integrable_def
 by (subst integral_count_space_nat) auto
  also have "(\<lambda>n. indicator A n *\<^sub>R f n) = (\<lambda>n. if n \<in> A then f n else 0)"
    by auto
  finally show ?thesis .
qed

lemma infsetsum_nat':
  assumes "f abs_summable_on UNIV"
  shows   "infsetsum f UNIV = (\<Sum>n. f n)"
  using assms by (subst infsetsum_nat) auto

lemma sums_infsetsum_nat:
  assumes "f abs_summable_on A"
  shows   "(\<lambda>n. if n \<in> A then f n else 0) sums infsetsum f A"
proof -
  from assms have "summable (\<lambda>n. if n \<in> A then norm (f n) else 0)"
    by (simp add: abs_summable_on_nat_iff)
  also have "(\<lambda>n. if n \<in> A then norm (f n) else 0) = (\<lambda>n. norm (if n \<in> A then f n else 0))"
    by auto
  finally have "summable (\<lambda>n. if n \<in> A then f n else 0)"
    by (rule summable_norm_cancel)
  with assms show ?thesis
    by (auto simp: sums_iff infsetsum_nat)
qed

lemma sums_infsetsum_nat':
  assumes "f abs_summable_on UNIV"
  shows   "f sums infsetsum f UNIV"
  using sums_infsetsum_nat [OF assms] by simp

lemma infsetsum_Un_disjoint:
  assumes "f abs_summable_on A" "f abs_summable_on B" "A \<inter> B = {}"
  shows   "infsetsum f (A \<union> B) = infsetsum f A + infsetsum f B"
  using assms unfolding infsetsum_altdef abs_summable_on_altdef
  by (subst set_integral_Un) auto

lemma infsetsum_Diff:
  assumes "f abs_summable_on B" "A \<subseteq> B"
  shows   "infsetsum f (B - A) = infsetsum f B - infsetsum f A"
proof -
  have "infsetsum f ((B - A) \<union> A) = infsetsum f (B - A) + infsetsum f A"
    using assms(2) by (intro infsetsum_Un_disjoint abs_summable_on_subset[OF assms(1)]) auto
  also from assms(2) have "(B - A) \<union> A = B"
    by auto
  ultimately show ?thesis
    by (simp add: algebra_simps)
qed

lemma infsetsum_Un_Int:
  assumes "f abs_summable_on (A \<union> B)"
  shows   "infsetsum f (A \<union> B) = infsetsum f A + infsetsum f B - infsetsum f (A \<inter> B)"
proof -
  have "A \<union> B = A \<union> (B - A \<inter> B)"
    by auto
  also have "infsetsum f \<dots> = infsetsum f A + infsetsum f (B - A \<inter> B)"
    by (intro infsetsum_Un_disjoint abs_summable_on_subset[OF assms]) auto
  also have "infsetsum f (B - A \<inter> B) = infsetsum f B - infsetsum f (A \<inter> B)"
    by (intro infsetsum_Diff abs_summable_on_subset[OF assms]) auto
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma infsetsum_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infsetsum (\<lambda>x. f (g x)) A = infsetsum f B"
proof -
  have *: "count_space B = distr (count_space A) (count_space B) g"
    by (rule distr_bij_count_space [symmetric]) fact
  show ?thesis unfolding infsetsum_def
    by (subst *, subst integral_distr[of _ _ "count_space B"])
       (insert assms, auto simp: bij_betw_def)
qed

theorem infsetsum_reindex:
  assumes "inj_on g A"
  shows   "infsetsum f (g ` A) = infsetsum (\<lambda>x. f (g x)) A"
  by (intro infsetsum_reindex_bij_betw [symmetric] inj_on_imp_bij_betw assms)

lemma infsetsum_cong_neutral:
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x = 0"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> g x = 0"
  assumes "\<And>x. x \<in> A \<inter> B \<Longrightarrow> f x = g x"
  shows   "infsetsum f A = infsetsum g B"
  unfolding infsetsum_altdef set_lebesgue_integral_def using assms
  by (intro Bochner_Integration.integral_cong refl)
     (auto simp: indicator_def split: if_splits)

lemma infsetsum_mono_neutral:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x \<le> 0"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> g x \<ge> 0"
  shows   "infsetsum f A \<le> infsetsum g B"
  using assms unfolding infsetsum_altdef set_lebesgue_integral_def abs_summable_on_altdef set_integrable_def
  by (intro Bochner_Integration.integral_mono) (auto simp: indicator_def)

lemma infsetsum_mono_neutral_left:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  assumes "A \<subseteq> B"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> g x \<ge> 0"
  shows   "infsetsum f A \<le> infsetsum g B"
  using \<open>A \<subseteq> B\<close> by (intro infsetsum_mono_neutral assms) auto

lemma infsetsum_mono_neutral_right:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  assumes "B \<subseteq> A"
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x \<le> 0"
  shows   "infsetsum f A \<le> infsetsum g B"
  using \<open>B \<subseteq> A\<close> by (intro infsetsum_mono_neutral assms) auto

lemma infsetsum_mono:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f abs_summable_on A" and "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsetsum f A \<le> infsetsum g A"
  by (intro infsetsum_mono_neutral assms) auto

lemma norm_infsetsum_bound:
  "norm (infsetsum f A) \<le> infsetsum (\<lambda>x. norm (f x)) A"
  unfolding abs_summable_on_def infsetsum_def
  by (rule Bochner_Integration.integral_norm_bound)

theorem infsetsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes [simp]: "countable A" and "\<And>i. countable (B i)"
  assumes summable: "f abs_summable_on (Sigma A B)"
  shows   "infsetsum f (Sigma A B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) (B x)) A"
proof -
  define B' where "B' = (\<Union>i\<in>A. B i)"
  have [simp]: "countable B'"
    unfolding B'_def by (intro countable_UN assms)
  interpret pair_sigma_finite "count_space A" "count_space B'"
    by (intro pair_sigma_finite.intro sigma_finite_measure_count_space_countable) fact+

  have "integrable (count_space (A \<times> B')) (\<lambda>z. indicator (Sigma A B) z *\<^sub>R f z)"
    using summable
    by (metis (mono_tags, lifting) abs_summable_on_altdef abs_summable_on_def integrable_cong integrable_mult_indicator set_integrable_def sets_UNIV)
  also have "?this \<longleftrightarrow> integrable (count_space A \<Otimes>\<^sub>M count_space B') (\<lambda>(x, y). indicator (B x) y *\<^sub>R f (x, y))"
    by (intro Bochner_Integration.integrable_cong)
       (auto simp: pair_measure_countable indicator_def split: if_splits)
  finally have integrable: \<dots> .

  have "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) (B x)) A =
          (\<integral>x. infsetsum (\<lambda>y. f (x, y)) (B x) \<partial>count_space A)"
    unfolding infsetsum_def by simp
  also have "\<dots> = (\<integral>x. \<integral>y. indicator (B x) y *\<^sub>R f (x, y) \<partial>count_space B' \<partial>count_space A)"
  proof (rule Bochner_Integration.integral_cong [OF refl])
    show "\<And>x. x \<in> space (count_space A) \<Longrightarrow>
         (\<Sum>\<^sub>ay\<in>B x. f (x, y)) = LINT y|count_space B'. indicat_real (B x) y *\<^sub>R f (x, y)"
      using infsetsum_altdef'[of _ B']
      unfolding set_lebesgue_integral_def B'_def
      by auto
  qed
  also have "\<dots> = (\<integral>(x,y). indicator (B x) y *\<^sub>R f (x, y) \<partial>(count_space A \<Otimes>\<^sub>M count_space B'))"
    by (subst integral_fst [OF integrable]) auto
  also have "\<dots> = (\<integral>z. indicator (Sigma A B) z *\<^sub>R f z \<partial>count_space (A \<times> B'))"
    by (intro Bochner_Integration.integral_cong)
       (auto simp: pair_measure_countable indicator_def split: if_splits)
  also have "\<dots> = infsetsum f (Sigma A B)"
    unfolding set_lebesgue_integral_def [symmetric]
    by (rule infsetsum_altdef' [symmetric]) (auto simp: B'_def)
  finally show ?thesis ..
qed

lemma infsetsum_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes [simp]: "countable A" and "\<And>i. countable (B i)"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (Sigma A B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) (B x)) A = infsetsum (\<lambda>(x,y). f x y) (Sigma A B)"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times:
  fixes A :: "'a set" and B :: "'b set"
  assumes [simp]: "countable A" and "countable B"
  assumes summable: "f abs_summable_on (A \<times> B)"
  shows   "infsetsum f (A \<times> B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) B) A"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times':
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes [simp]: "countable A" and [simp]: "countable B"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (A \<times> B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
  using assms by (subst infsetsum_Times) auto

lemma infsetsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes [simp]: "countable A" and [simp]: "countable B"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on A \<times> B"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
proof -
  from summable have summable': "(\<lambda>(x,y). f y x) abs_summable_on B \<times> A"
    by (subst abs_summable_on_Times_swap) auto
  have bij: "bij_betw (\<lambda>(x, y). (y, x)) (B \<times> A) (A \<times> B)"
    by (auto simp: bij_betw_def inj_on_def)
  have "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
    using summable by (subst infsetsum_Times) auto
  also have "\<dots> = infsetsum (\<lambda>(x,y). f y x) (B \<times> A)"
    by (subst infsetsum_reindex_bij_betw[OF bij, of "\<lambda>(x,y). f x y", symmetric])
       (simp_all add: case_prod_unfold)
  also have "\<dots> = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
    using summable' by (subst infsetsum_Times) auto
  finally show ?thesis .
qed

theorem abs_summable_on_Sigma_iff:
  assumes [simp]: "countable A" and "\<And>x. x \<in> A \<Longrightarrow> countable (B x)"
  shows   "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"
proof safe
  define B' where "B' = (\<Union>x\<in>A. B x)"
  have [simp]: "countable B'"
    unfolding B'_def using assms by auto
  interpret pair_sigma_finite "count_space A" "count_space B'"
    by (intro pair_sigma_finite.intro sigma_finite_measure_count_space_countable) fact+
  {
    assume *: "f abs_summable_on Sigma A B"
    thus "(\<lambda>y. f (x, y)) abs_summable_on B x" if "x \<in> A" for x
      using that by (rule abs_summable_on_Sigma_project2)

    have "set_integrable (count_space (A \<times> B')) (Sigma A B) (\<lambda>z. norm (f z))"
      using abs_summable_on_normI[OF *]
      by (subst abs_summable_on_altdef' [symmetric]) (auto simp: B'_def)
    also have "count_space (A \<times> B') = count_space A \<Otimes>\<^sub>M count_space B'"
      by (simp add: pair_measure_countable)
    finally have "integrable (count_space A)
                    (\<lambda>x. lebesgue_integral (count_space B')
                      (\<lambda>y. indicator (Sigma A B) (x, y) *\<^sub>R norm (f (x, y))))"
      unfolding set_integrable_def by (rule integrable_fst')
    also have "?this \<longleftrightarrow> integrable (count_space A)
                    (\<lambda>x. lebesgue_integral (count_space B')
                      (\<lambda>y. indicator (B x) y *\<^sub>R norm (f (x, y))))"
      by (intro integrable_cong refl) (simp_all add: indicator_def)
    also have "\<dots> \<longleftrightarrow> integrable (count_space A) (\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x))"
      unfolding set_lebesgue_integral_def [symmetric]
      by (intro integrable_cong refl infsetsum_altdef' [symmetric]) (auto simp: B'_def)
    also have "\<dots> \<longleftrightarrow> (\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A"
      by (simp add: abs_summable_on_def)
    finally show \<dots> .
  }
  {
    assume *: "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
    assume "(\<lambda>x. \<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) abs_summable_on A"
    also have "?this \<longleftrightarrow> (\<lambda>x. \<integral>y\<in>B x. norm (f (x, y)) \<partial>count_space B') abs_summable_on A"
      by (intro abs_summable_on_cong refl infsetsum_altdef') (auto simp: B'_def)
    also have "\<dots> \<longleftrightarrow> (\<lambda>x. \<integral>y. indicator (Sigma A B) (x, y) *\<^sub>R norm (f (x, y)) \<partial>count_space B')
                        abs_summable_on A" (is "_ \<longleftrightarrow> ?h abs_summable_on _")
      unfolding set_lebesgue_integral_def
      by (intro abs_summable_on_cong) (auto simp: indicator_def)
    also have "\<dots> \<longleftrightarrow> integrable (count_space A) ?h"
      by (simp add: abs_summable_on_def)
    finally have **: \<dots> .

    have "integrable (count_space A \<Otimes>\<^sub>M count_space B') (\<lambda>z. indicator (Sigma A B) z *\<^sub>R f z)"
    proof (rule Fubini_integrable, goal_cases)
      case 3
      {
        fix x assume x: "x \<in> A"
        with * have "(\<lambda>y. f (x, y)) abs_summable_on B x"
          by blast
        also have "?this \<longleftrightarrow> integrable (count_space B')
                      (\<lambda>y. indicator (B x) y *\<^sub>R f (x, y))"
          unfolding set_integrable_def [symmetric]
         using x by (intro abs_summable_on_altdef') (auto simp: B'_def)
        also have "(\<lambda>y. indicator (B x) y *\<^sub>R f (x, y)) =
                     (\<lambda>y. indicator (Sigma A B) (x, y) *\<^sub>R f (x, y))"
          using x by (auto simp: indicator_def)
        finally have "integrable (count_space B')
                        (\<lambda>y. indicator (Sigma A B) (x, y) *\<^sub>R f (x, y))" .
      }
      thus ?case by (auto simp: AE_count_space)
    qed (insert **, auto simp: pair_measure_countable)
    moreover have "count_space A \<Otimes>\<^sub>M count_space B' = count_space (A \<times> B')"
      by (simp add: pair_measure_countable)
    moreover have "set_integrable (count_space (A \<times> B')) (Sigma A B) f \<longleftrightarrow>
                 f abs_summable_on Sigma A B"
      by (rule abs_summable_on_altdef' [symmetric]) (auto simp: B'_def)
    ultimately show "f abs_summable_on Sigma A B"
      by (simp add: set_integrable_def)
  }
qed

lemma abs_summable_on_Sigma_project1:
  assumes "(\<lambda>(x,y). f x y) abs_summable_on Sigma A B"
  assumes [simp]: "countable A" and "\<And>x. x \<in> A \<Longrightarrow> countable (B x)"
  shows   "(\<lambda>x. infsetsum (\<lambda>y. norm (f x y)) (B x)) abs_summable_on A"
  using assms by (subst (asm) abs_summable_on_Sigma_iff) auto

lemma abs_summable_on_Sigma_project1':
  assumes "(\<lambda>(x,y). f x y) abs_summable_on Sigma A B"
  assumes [simp]: "countable A" and "\<And>x. x \<in> A \<Longrightarrow> countable (B x)"
  shows   "(\<lambda>x. infsetsum (\<lambda>y. f x y) (B x)) abs_summable_on A"
  by (intro abs_summable_on_comparison_test' [OF abs_summable_on_Sigma_project1[OF assms]]
        norm_infsetsum_bound)

theorem infsetsum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field,banach,second_countable_topology}"
  assumes finite: "finite A" and countable: "\<And>x. x \<in> A \<Longrightarrow> countable (B x)"
  assumes summable: "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows   "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
proof -
  define B' where "B' = (\<lambda>x. if x \<in> A then B x else {})"
  from assms have [simp]: "countable (B' x)" for x
    by (auto simp: B'_def)
  then interpret product_sigma_finite "count_space \<circ> B'"
    unfolding o_def by (intro product_sigma_finite.intro sigma_finite_measure_count_space_countable)
  have "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) =
          (\<integral>g. (\<Prod>x\<in>A. f x (g x)) \<partial>count_space (PiE A B))"
    by (simp add: infsetsum_def)
  also have "PiE A B = PiE A B'"
    by (intro PiE_cong) (simp_all add: B'_def)
  hence "count_space (PiE A B) = count_space (PiE A B')"
    by simp
  also have "\<dots> = PiM A (count_space \<circ> B')"
    unfolding o_def using finite by (intro count_space_PiM_finite [symmetric]) simp_all
  also have "(\<integral>g. (\<Prod>x\<in>A. f x (g x)) \<partial>\<dots>) = (\<Prod>x\<in>A. infsetsum (f x) (B' x))"
    by (subst product_integral_prod)
       (insert summable finite, simp_all add: infsetsum_def B'_def abs_summable_on_def)
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
    by (intro prod.cong refl) (simp_all add: B'_def)
  finally show ?thesis .
qed

lemma infsetsum_uminus: "infsetsum (\<lambda>x. -f x) A = -infsetsum f A"
  unfolding infsetsum_def abs_summable_on_def
  by (rule Bochner_Integration.integral_minus)

lemma infsetsum_add:
  assumes "f abs_summable_on A" and "g abs_summable_on A"
  shows   "infsetsum (\<lambda>x. f x + g x) A = infsetsum f A + infsetsum g A"
  using assms unfolding infsetsum_def abs_summable_on_def
  by (rule Bochner_Integration.integral_add)

lemma infsetsum_diff:
  assumes "f abs_summable_on A" and "g abs_summable_on A"
  shows   "infsetsum (\<lambda>x. f x - g x) A = infsetsum f A - infsetsum g A"
  using assms unfolding infsetsum_def abs_summable_on_def
  by (rule Bochner_Integration.integral_diff)

lemma infsetsum_scaleR_left:
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "infsetsum (\<lambda>x. f x *\<^sub>R c) A = infsetsum f A *\<^sub>R c"
  using assms unfolding infsetsum_def abs_summable_on_def
  by (rule Bochner_Integration.integral_scaleR_left)

lemma infsetsum_scaleR_right:
  "infsetsum (\<lambda>x. c *\<^sub>R f x) A = c *\<^sub>R infsetsum f A"
  unfolding infsetsum_def abs_summable_on_def
  by (subst Bochner_Integration.integral_scaleR_right) auto

lemma infsetsum_cmult_left:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology}"
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "infsetsum (\<lambda>x. f x * c) A = infsetsum f A * c"
  using assms unfolding infsetsum_def abs_summable_on_def
  by (rule Bochner_Integration.integral_mult_left)

lemma infsetsum_cmult_right:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology}"
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "infsetsum (\<lambda>x. c * f x) A = c * infsetsum f A"
  using assms unfolding infsetsum_def abs_summable_on_def
  by (rule Bochner_Integration.integral_mult_right)

lemma infsetsum_cdiv:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_field, second_countable_topology}"
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "infsetsum (\<lambda>x. f x / c) A = infsetsum f A / c"
  using assms unfolding infsetsum_def abs_summable_on_def by auto


(* TODO Generalise with bounded_linear *)

lemma
  fixes f :: "'a \<Rightarrow> 'c :: {banach, real_normed_field, second_countable_topology}"
  assumes [simp]: "countable A" and [simp]: "countable B"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  shows   abs_summable_on_product: "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    and   infsetsum_product: "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) =
                                infsetsum f A * infsetsum g B"
proof -
  from assms show "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    by (subst abs_summable_on_Sigma_iff)
       (auto intro!: abs_summable_on_cmult_right simp: norm_mult infsetsum_cmult_right)
  with assms show "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) = infsetsum f A * infsetsum g B"
    by (subst infsetsum_Sigma)
       (auto simp: infsetsum_cmult_left infsetsum_cmult_right)
qed

lemma abs_summable_finite_sumsI:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
  shows "f abs_summable_on S"
proof -
  have main: "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B" if \<open>B \<ge> 0\<close> and \<open>S \<noteq> {}\<close>
  proof -
    define M normf where "M = count_space S" and "normf x = ennreal (norm (f x))" for x
    have "sum normf F \<le> ennreal B"
      if "finite F" and "F \<subseteq> S" and
        "\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> (\<Sum>i\<in>F. ennreal (norm (f i))) \<le> ennreal B" and
        "ennreal 0 \<le> ennreal B" for F
      using that unfolding normf_def[symmetric] by simp
    hence normf_B: "finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum normf F \<le> ennreal B" for F
      using assms[THEN ennreal_leI]
      by auto
    have "integral\<^sup>S M g \<le> B" if "simple_function M g" and "g \<le> normf" for g 
    proof -
      define gS where "gS = g ` S"
      have "finite gS"
        using that unfolding gS_def M_def simple_function_count_space by simp
      have "gS \<noteq> {}" unfolding gS_def using \<open>S \<noteq> {}\<close> by auto
      define part where "part r = g -` {r} \<inter> S" for r
      have r_finite: "r < \<infinity>" if "r : gS" for r 
        using \<open>g \<le> normf\<close> that unfolding gS_def le_fun_def normf_def apply auto
        using ennreal_less_top neq_top_trans top.not_eq_extremum by blast
      define B' where "B' r = (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)" for r
      have B'fin: "B' r < \<infinity>" for r
      proof -
        have "B' r \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)"
          unfolding B'_def
          by (metis (mono_tags, lifting) SUP_least SUP_upper)
        also have "\<dots> \<le> B"
          using normf_B unfolding part_def
          by (metis (no_types, lifting) Int_subset_iff SUP_least mem_Collect_eq)
        also have "\<dots> < \<infinity>"
          by simp
        finally show ?thesis by simp
      qed
      have sumB': "sum B' gS \<le> ennreal B + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        define N \<epsilon>N where "N = card gS" and "\<epsilon>N = \<epsilon> / N"
        have "N > 0" 
          unfolding N_def using \<open>gS\<noteq>{}\<close> \<open>finite gS\<close>
          by (simp add: card_gt_0_iff)
        from \<epsilon>N_def that have "\<epsilon>N > 0"
          by (simp add: ennreal_of_nat_eq_real_of_nat ennreal_zero_less_divide)
        have c1: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and> finite y \<and> y \<subseteq> part r"
          if "B' r = 0" for r
          using that by auto
        have c2: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and> finite y \<and> y \<subseteq> part r" if "B' r \<noteq> 0" for r
        proof-
          have "B' r - \<epsilon>N < B' r"
            using B'fin \<open>0 < \<epsilon>N\<close> ennreal_between that by fastforce
          have "B' r - \<epsilon>N < Sup (sum normf ` {F. finite F \<and> F \<subseteq> part r}) \<Longrightarrow>
               \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and> finite F \<and> F \<subseteq> part r"
            by (metis (no_types, lifting) leD le_cases less_SUP_iff mem_Collect_eq)
          hence "B' r - \<epsilon>N < B' r \<Longrightarrow> \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and> finite F \<and> F \<subseteq> part r"
            by (subst (asm) (2) B'_def)
          then obtain F where "B' r - \<epsilon>N \<le> sum normf F" and "finite F" and "F \<subseteq> part r"
            using \<open>B' r - \<epsilon>N < B' r\<close> by auto  
          thus "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r"
            by (metis add.commute ennreal_minus_le_iff)
        qed
        have "\<forall>x. \<exists>y. B' x \<le> sum normf y + \<epsilon>N \<and>
            finite y \<and> y \<subseteq> part x"
          using c1 c2
          by blast 
        hence "\<exists>F. \<forall>x. B' x \<le> sum normf (F x) + \<epsilon>N \<and> finite (F x) \<and> F x \<subseteq> part x"
          by metis 
        then obtain F where F: "sum normf (F r) + \<epsilon>N \<ge> B' r" and Ffin: "finite (F r)" and Fpartr: "F r \<subseteq> part r" for r
          using atomize_elim by auto
        have w1: "finite gS"
          by (simp add: \<open>finite gS\<close>)          
        have w2: "\<forall>i\<in>gS. finite (F i)"
          by (simp add: Ffin)          
        have False
          if "\<And>r. F r \<subseteq> g -` {r} \<and> F r \<subseteq> S"
            and "i \<in> gS" and "j \<in> gS" and "i \<noteq> j" and "x \<in> F i" and "x \<in> F j"
          for i j x
          by (metis subsetD that(1) that(4) that(5) that(6) vimage_singleton_eq)          
        hence w3: "\<forall>i\<in>gS. \<forall>j\<in>gS. i \<noteq> j \<longrightarrow> F i \<inter> F j = {}"
          using Fpartr[unfolded part_def] by auto          
        have w4: "sum normf (\<Union> (F ` gS)) + \<epsilon> = sum normf (\<Union> (F ` gS)) + \<epsilon>"
          by simp
        have "sum B' gS \<le> (\<Sum>r\<in>gS. sum normf (F r) + \<epsilon>N)"
          using F by (simp add: sum_mono)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (\<Sum>r\<in>gS. \<epsilon>N)"
          by (simp add: sum.distrib)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (card gS * \<epsilon>N)"
          by auto
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + \<epsilon>"
          unfolding \<epsilon>N_def N_def[symmetric] using \<open>N>0\<close> 
          by (simp add: ennreal_times_divide mult.commute mult_divide_eq_ennreal)
        also have "\<dots> = sum normf (\<Union> (F ` gS)) + \<epsilon>" 
          using w1 w2 w3 w4
          by (subst sum.UNION_disjoint[symmetric])
        also have "\<dots> \<le> B + \<epsilon>"
          using \<open>finite gS\<close> normf_B add_right_mono Ffin Fpartr unfolding part_def
          by (simp add: \<open>gS \<noteq> {}\<close> cSUP_least)          
        finally show ?thesis
          by auto
      qed
      hence sumB': "sum B' gS \<le> B"
        using ennreal_le_epsilon ennreal_less_zero_iff by blast
      have "\<forall>r. \<exists>y. r \<in> gS \<longrightarrow> B' r = ennreal y"
        using B'fin less_top_ennreal by auto
      hence "\<exists>B''. \<forall>r. r \<in> gS \<longrightarrow> B' r = ennreal (B'' r)"
        by (rule_tac choice) 
      then obtain B'' where B'': "B' r = ennreal (B'' r)" if "r \<in> gS" for r
        by atomize_elim 
      have cases[case_names zero finite infinite]: "P" if "r=0 \<Longrightarrow> P" and "finite (part r) \<Longrightarrow> P"
        and "infinite (part r) \<Longrightarrow> r\<noteq>0 \<Longrightarrow> P" for P r
        using that by metis
      have emeasure_B': "r * emeasure M (part r) \<le> B' r" if "r : gS" for r
      proof (cases rule:cases[of r])
        case zero
        thus ?thesis by simp
      next
        case finite
        have s1: "sum g F \<le> sum normf F"
          if "F \<in> {F. finite F \<and> F \<subseteq> part r}"
          for F
          using \<open>g \<le> normf\<close> 
          by (simp add: le_fun_def sum_mono)

        have "r * of_nat (card (part r)) = r * (\<Sum>x\<in>part r. 1)" by simp
        also have "\<dots> = (\<Sum>x\<in>part r. r)"
          using mult.commute by auto
        also have "\<dots> = (\<Sum>x\<in>part r. g x)"
          unfolding part_def by auto
        also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum g F)"
          using finite
          by (simp add: Sup_upper)
        also have "\<dots> \<le> B' r"        
          unfolding B'_def
          using s1 SUP_subset_mono by blast
        finally have "r * of_nat (card (part r)) \<le> B' r" by assumption
        thus ?thesis
          unfolding M_def
          using part_def finite by auto
      next
        case infinite
        from r_finite[OF \<open>r : gS\<close>] obtain r' where r': "r = ennreal r'"
          using ennreal_cases by auto
        with infinite have "r' > 0"
          using ennreal_less_zero_iff not_gr_zero by blast
        obtain N::nat where N:"N > B / r'" and "real N > 0" apply atomize_elim
          using reals_Archimedean2
          by (metis less_trans linorder_neqE_linordered_idom)
        obtain F where "finite F" and "card F = N" and "F \<subseteq> part r"
          using infinite(1) infinite_arbitrarily_large by blast
        from \<open>F \<subseteq> part r\<close> have "F \<subseteq> S" unfolding part_def by simp
        have "B < r * N"
          unfolding r' ennreal_of_nat_eq_real_of_nat
          using N \<open>0 < r'\<close> \<open>B \<ge> 0\<close> r'
          by (metis enn2real_ennreal enn2real_less_iff ennreal_less_top ennreal_mult' less_le mult_less_cancel_left_pos nonzero_mult_div_cancel_left times_divide_eq_right)
        also have "r * N = (\<Sum>x\<in>F. r)"
          using \<open>card F = N\<close> by (simp add: mult.commute)
        also have "(\<Sum>x\<in>F. r) = (\<Sum>x\<in>F. g x)"
          using \<open>F \<subseteq> part r\<close>  part_def sum.cong subsetD by fastforce
        also have "(\<Sum>x\<in>F. g x) \<le> (\<Sum>x\<in>F. ennreal (norm (f x)))"
          by (metis (mono_tags, lifting) \<open>g \<le> normf\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> le_fun_def 
              sum_mono)
        also have "(\<Sum>x\<in>F. ennreal (norm (f x))) \<le> B"
          using \<open>F \<subseteq> S\<close> \<open>finite F\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> normf_B by blast 
        finally have "B < B" by auto
        thus ?thesis by simp
      qed

      have "integral\<^sup>S M g = (\<Sum>r \<in> gS. r * emeasure M (part r))"
        unfolding simple_integral_def gS_def M_def part_def by simp
      also have "\<dots> \<le> (\<Sum>r \<in> gS. B' r)"
        by (simp add: emeasure_B' sum_mono)
      also have "\<dots> \<le> B"
        using sumB' by blast
      finally show ?thesis by assumption
    qed
    hence int_leq_B: "integral\<^sup>N M normf \<le> B"
      unfolding nn_integral_def by (metis (no_types, lifting) SUP_least mem_Collect_eq)
    hence "integral\<^sup>N M normf < \<infinity>"
      using le_less_trans by fastforce
    hence "integrable M f"
      unfolding M_def normf_def by (rule integrableI_bounded[rotated], simp)
    hence v1: "f abs_summable_on S"
      unfolding abs_summable_on_def M_def by simp  

    have "(\<lambda>x. norm (f x)) abs_summable_on S"
      using v1 Infinite_Set_Sum.abs_summable_on_norm_iff[where A = S and f = f]
      by auto
    moreover have "0 \<le> norm (f x)"
      if "x \<in> S" for x
      by simp    
    moreover have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>count_space S) \<le> ennreal B"
      using M_def \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> int_leq_B by auto    
    ultimately have "ennreal (\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> ennreal B"
      by (simp add: nn_integral_conv_infsetsum)    
    hence v2: "(\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> B"
      by (subst ennreal_le_iff[symmetric], simp add: assms \<open>B \<ge> 0\<close>)
    show ?thesis
      using v1 v2 by auto
  qed
  then show "f abs_summable_on S"
    by (metis abs_summable_on_finite assms empty_subsetI finite.emptyI sum_clauses(1))
qed


lemma infsetsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
proof -
  have sum_F_A: "sum f F \<le> infsetsum f A" 
    if "F \<in> {F. finite F \<and> F \<subseteq> A}" 
    for F
  proof-
    from that have "finite F" and "F \<subseteq> A" by auto
    from \<open>finite F\<close> have "sum f F = infsetsum f F" by auto
    also have "\<dots> \<le> infsetsum f A"
    proof (rule infsetsum_mono_neutral_left)
      show "f abs_summable_on F"
        by (simp add: \<open>finite F\<close>)        
      show "f abs_summable_on A"
        by (simp add: local.summable)        
      show "f x \<le> f x"
        if "x \<in> F"
        for x :: 'a
        by simp 
      show "F \<subseteq> A"
        by (simp add: \<open>F \<subseteq> A\<close>)        
      show "0 \<le> f x"
        if "x \<in> A - F"
        for x :: 'a
        using that fnn by auto 
    qed
    finally show ?thesis by assumption
  qed 
  hence geq: "ennreal (infsetsum f A) \<ge> (SUP F\<in>{G. finite G \<and> G \<subseteq> A}. (ennreal (sum f F)))"
    by (meson SUP_least ennreal_leI)

  define fe where "fe x = ennreal (f x)" for x

  have sum_f_int: "infsetsum f A = \<integral>\<^sup>+ x. fe x \<partial>(count_space A)"
    unfolding infsetsum_def fe_def
  proof (rule nn_integral_eq_integral [symmetric])
    show "integrable (count_space A) f"
      using abs_summable_on_def local.summable by blast      
    show "AE x in count_space A. 0 \<le> f x"
      using fnn by auto      
  qed
  also have "\<dots> = (SUP g \<in> {g. finite (g`A) \<and> g \<le> fe}. integral\<^sup>S (count_space A) g)"
    unfolding nn_integral_def simple_function_count_space by simp
  also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
  proof (rule Sup_least)
    fix x assume "x \<in> integral\<^sup>S (count_space A) ` {g. finite (g ` A) \<and> g \<le> fe}"
    then obtain g where xg: "x = integral\<^sup>S (count_space A) g" and fin_gA: "finite (g`A)" 
      and g_fe: "g \<le> fe" by auto
    define F where "F = {z:A. g z \<noteq> 0}"
    hence "F \<subseteq> A" by simp

    have fin: "finite {z:A. g z = t}" if "t \<noteq> 0" for t
    proof (rule ccontr)
      assume inf: "infinite {z:A. g z = t}"
      hence tgA: "t \<in> g ` A"
        by (metis (mono_tags, lifting) image_eqI not_finite_existsD)
      have "x = (\<Sum>x \<in> g ` A. x * emeasure (count_space A) (g -` {x} \<inter> A))"
        unfolding xg simple_integral_def space_count_space by simp
      also have "\<dots> \<ge> (\<Sum>x \<in> {t}. x * emeasure (count_space A) (g -` {x} \<inter> A))" (is "_ \<ge> \<dots>")
      proof (rule sum_mono2)
        show "finite (g ` A)"
          by (simp add: fin_gA)          
        show "{t} \<subseteq> g ` A"
          by (simp add: tgA)          
        show "0 \<le> b * emeasure (count_space A) (g -` {b} \<inter> A)"
          if "b \<in> g ` A - {t}"
          for b :: ennreal
          using that
          by simp
      qed
      also have "\<dots> = t * emeasure (count_space A) (g -` {t} \<inter> A)"
        by auto
      also have "\<dots> = t * \<infinity>"
      proof (subst emeasure_count_space_infinite)
        show "g -` {t} \<inter> A \<subseteq> A"
          by simp             
        have "{a \<in> A. g a = t} = {a \<in> g -` {t}. a \<in> A}"
          by auto
        thus "infinite (g -` {t} \<inter> A)"
          by (metis (full_types) Int_def inf) 
        show "t * \<infinity> = t * \<infinity>"
          by simp
      qed
      also have "\<dots> = \<infinity>" using \<open>t \<noteq> 0\<close>
        by (simp add: ennreal_mult_eq_top_iff)
      finally have x_inf: "x = \<infinity>"
        using neq_top_trans by auto
      have "x = integral\<^sup>S (count_space A) g" by (fact xg)
      also have "\<dots> = integral\<^sup>N (count_space A) g"
        by (simp add: fin_gA nn_integral_eq_simple_integral)
      also have "\<dots> \<le> integral\<^sup>N (count_space A) fe"
        using g_fe
        by (simp add: le_funD nn_integral_mono)
      also have "\<dots> < \<infinity>"
        by (metis sum_f_int ennreal_less_top infinity_ennreal_def) 
      finally have x_fin: "x < \<infinity>" by simp
      from x_inf x_fin show False by simp
    qed
    have F: "F = (\<Union>t\<in>g`A-{0}. {z\<in>A. g z = t})"
      unfolding F_def by auto
    hence "finite F"
      unfolding F using fin_gA fin by auto
    have "x = integral\<^sup>N (count_space A) g"
      unfolding xg
      by (simp add: fin_gA nn_integral_eq_simple_integral)
    also have "\<dots> = set_nn_integral (count_space UNIV) A g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = set_nn_integral (count_space UNIV) F g"
    proof -
      have "\<forall>a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) = g a * (if a \<in> A then 1 else 0)"
        by auto
      hence "(\<integral>\<^sup>+ a. g a * (if a \<in> A then 1 else 0) \<partial>count_space UNIV)
           = (\<integral>\<^sup>+ a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) \<partial>count_space UNIV)"
        by presburger
      thus ?thesis unfolding F_def indicator_def
        using mult.right_neutral mult_zero_right nn_integral_cong
        by (simp add: of_bool_def) 
    qed
    also have "\<dots> = integral\<^sup>N (count_space F) g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = sum g F" 
      using \<open>finite F\<close> by (rule nn_integral_count_space_finite)
    also have "sum g F \<le> sum fe F"
      using g_fe unfolding le_fun_def
      by (simp add: sum_mono) 
    also have "\<dots> \<le> (SUP F \<in> {G. finite G \<and> G \<subseteq> A}. (sum fe F))"
      using \<open>finite F\<close> \<open>F\<subseteq>A\<close>
      by (simp add: SUP_upper)
    also have "\<dots> = (SUP F \<in> {F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    proof (rule SUP_cong [OF refl])
      have "finite x \<Longrightarrow> x \<subseteq> A \<Longrightarrow> (\<Sum>x\<in>x. ennreal (f x)) = ennreal (sum f x)"
        for x
        by (metis fnn subsetCE sum_ennreal)
      thus "sum fe x = ennreal (sum f x)"
        if "x \<in> {G. finite G \<and> G \<subseteq> A}"
        for x :: "'a set"
        using that unfolding fe_def by auto      
    qed 
    finally show "x \<le> \<dots>" by simp
  qed
  finally have leq: "ennreal (infsetsum f A) \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    by assumption
  from leq geq show ?thesis by simp
qed

lemma infsetsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
proof -
  have "ereal (infsetsum f A) = enn2ereal (ennreal (infsetsum f A))"
    by (simp add: fnn infsetsum_nonneg)
  also have "\<dots> = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
    apply (subst infsetsum_nonneg_is_SUPREMUM_ennreal)
    using fnn by (auto simp add: local.summable)      
  also have "\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
  proof (simp add: image_def Sup_ennreal.rep_eq)
    have "0 \<le> Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x = ennreal (sum f xa)) \<and>
                     y = enn2ereal x}"
      by (metis (mono_tags, lifting) Sup_upper empty_subsetI ennreal_0 finite.emptyI
          mem_Collect_eq sum.empty zero_ennreal.rep_eq)
    moreover have "Sup {y. \<exists>x. (\<exists>y. finite y \<and> y \<subseteq> A \<and> x = ennreal (sum f y)) \<and>
                y = enn2ereal x} = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      using enn2ereal_ennreal fnn in_mono sum_nonneg Collect_cong
      by smt
    ultimately show "max 0 (Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x
                                       = ennreal (sum f xa)) \<and> y = enn2ereal x})
         = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      by linarith
  qed   
  finally show ?thesis
    by simp
qed


text \<open>The following theorem relates \<^const>\<open>Infinite_Set_Sum.abs_summable_on\<close> with \<^const>\<open>Infinite_Sum.abs_summable_on\<close>.
  Note that while this theorem expresses an equivalence, the notion on the lhs is more general
  nonetheless because it applies to a wider range of types. (The rhs requires second-countable
  Banach spaces while the lhs is well-defined on arbitrary real vector spaces.)\<close>

lemma abs_summable_equivalent: \<open>Infinite_Sum.abs_summable_on f A \<longleftrightarrow> f abs_summable_on A\<close>
proof (rule iffI)
  define n where \<open>n x = norm (f x)\<close> for x
  assume \<open>n summable_on A\<close>
  then have \<open>sum n F \<le> infsum n A\<close> if \<open>finite F\<close> and \<open>F\<subseteq>A\<close> for F
    using that by (auto simp flip: infsum_finite simp: n_def[abs_def] intro!: infsum_mono_neutral)
    
  then show \<open>f abs_summable_on A\<close>
    by (auto intro!: abs_summable_finite_sumsI simp: n_def)
next
  define n where \<open>n x = norm (f x)\<close> for x
  assume \<open>f abs_summable_on A\<close>
  then have \<open>n abs_summable_on A\<close>
    by (simp add: \<open>f abs_summable_on A\<close> n_def)
  then have \<open>sum n F \<le> infsetsum n A\<close> if \<open>finite F\<close> and \<open>F\<subseteq>A\<close> for F
    using that by (auto simp flip: infsetsum_finite simp: n_def[abs_def] intro!: infsetsum_mono_neutral)
  then show \<open>n summable_on A\<close>
    apply (rule_tac pos_summable_on)
    by (auto simp add: n_def bdd_above_def)
qed

lemma infsetsum_infsum:
  assumes "f abs_summable_on A"
  shows "infsetsum f A = infsum f A"
proof -
  have conv_sum_norm[simp]: "(\<lambda>x. norm (f x)) summable_on A"
    using abs_summable_equivalent assms by blast
  have "norm (infsetsum f A - infsum f A) \<le> \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof -
    define \<delta> where "\<delta> = \<epsilon>/2"
    with that have [simp]: "\<delta> > 0" by simp
    obtain F1 where F1A: "F1 \<subseteq> A" and finF1: "finite F1" and leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F1) \<le> \<delta>"
    proof -
      have sum_SUP: "ereal (infsetsum (\<lambda>x. norm (f x)) A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum (\<lambda>x. norm (f x)) F))"
        (is "_ = ?SUP")
        apply (rule infsetsum_nonneg_is_SUPREMUM_ereal)
        using assms by auto

      have "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x))) - ereal \<delta>
            < (SUP i\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>i. norm (f x)))"
        using \<open>\<delta>>0\<close>
        by (metis diff_strict_left_mono diff_zero ereal_less_eq(3) ereal_minus(1) not_le sum_SUP)
      then obtain F where "F\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (sum (\<lambda>x. norm (f x)) F) > ?SUP - ereal (\<delta>)"
        by (meson less_SUP_iff)
        
      hence "sum (\<lambda>x. norm (f x)) F > infsetsum (\<lambda>x. norm (f x)) A -  (\<delta>)"
        unfolding sum_SUP[symmetric] by auto
      hence "\<delta> > infsetsum (\<lambda>x. norm (f x)) (A-F)"
      proof (subst infsetsum_Diff)
        show "(\<lambda>x. norm (f x)) abs_summable_on A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that
          by (simp add: assms) 
        show "F \<subseteq> A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by blast 
        show "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - (\<Sum>\<^sub>ax\<in>F. norm (f x)) < \<delta>"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by auto 
      qed
      thus ?thesis using that 
        apply atomize_elim
        using \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> less_imp_le by blast
    qed
    obtain F2 where F2A: "F2 \<subseteq> A" and finF2: "finite F2"
      and dist: "dist (sum (\<lambda>x. norm (f x)) F2) (infsum (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      apply atomize_elim
      by (metis \<open>0 < \<delta>\<close> conv_sum_norm infsum_finite_approximation)
    have  leq_eps': "infsum (\<lambda>x. norm (f x)) (A-F2) \<le> \<delta>"
      apply (subst infsum_Diff)
      using finF2 F2A dist by (auto simp: dist_norm)
    define F where "F = F1 \<union> F2"
    have FA: "F \<subseteq> A" and finF: "finite F" 
      unfolding F_def using F1A F2A finF1 finF2 by auto

    have "(\<Sum>\<^sub>ax\<in>A - (F1 \<union> F2). norm (f x)) \<le> (\<Sum>\<^sub>ax\<in>A - F1. norm (f x))"
      apply (rule infsetsum_mono_neutral_left)
      using abs_summable_on_subset assms by fastforce+
    hence leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def
      using leq_eps by linarith
    have "infsum (\<lambda>x. norm (f x)) (A - (F1 \<union> F2))
          \<le> infsum (\<lambda>x. norm (f x)) (A - F2)"
      apply (rule infsum_mono_neutral)
      using finF by (auto simp add: finF2 summable_on_cofin_subset F_def)
    hence leq_eps': "infsum (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def 
      by (rule order.trans[OF _ leq_eps'])
    have "norm (infsetsum f A - infsetsum f F) = norm (infsetsum f (A-F))"
      apply (subst infsetsum_Diff [symmetric])
      by (auto simp: FA assms)
    also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F)"
      using norm_infsetsum_bound by blast
    also have "\<dots> \<le> \<delta>"
      using leq_eps by simp
    finally have diff1: "norm (infsetsum f A - infsetsum f F) \<le> \<delta>"
      by assumption
    have "norm (infsum f A - infsum f F) = norm (infsum f (A-F))"
      apply (subst infsum_Diff [symmetric])
      by (auto simp: assms abs_summable_summable finF FA)
    also have "\<dots> \<le> infsum (\<lambda>x. norm (f x)) (A-F)"
      by (simp add: finF summable_on_cofin_subset norm_infsum_bound)
    also have "\<dots> \<le> \<delta>"
      using leq_eps' by simp
    finally have diff2: "norm (infsum f A - infsum f F) \<le> \<delta>"
      by assumption

    have x1: "infsetsum f F = infsum f F"
      using finF by simp
    have "norm (infsetsum f A - infsum f A) \<le> norm (infsetsum f A - infsetsum f F) + norm (infsum f A - infsum f F)"
      apply (rule_tac norm_diff_triangle_le)
       apply auto
      by (simp_all add: x1 norm_minus_commute)
    also have "\<dots> \<le> \<epsilon>"
      using diff1 diff2 \<delta>_def by linarith
    finally show ?thesis
      by assumption
  qed
  hence "norm (infsetsum f A - infsum f A) = 0"
    by (meson antisym_conv1 dense_ge norm_not_less_zero)
  thus ?thesis
    by auto
qed

end
