(*  
  Title:    HOL/Analysis/Infinite_Set_Sum.thy
  Author:   Manuel Eberl, TU München

  A theory of sums over possible infinite sets. (Only works for absolute summability)
*)
section \<open>Sums over Infinite Sets\<close>

theory Infinite_Set_Sum
  imports Set_Integral
begin

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

lemma PiE_singleton: 
  assumes "f \<in> extensional A"
  shows   "PiE A (\<lambda>x. {f x}) = {f}"
proof -
  {
    fix g assume "g \<in> PiE A (\<lambda>x. {f x})"
    hence "g x = f x" for x
      using assms by (cases "x \<in> A") (auto simp: extensional_def)
    hence "g = f" by (simp add: fun_eq_iff)
  }
  thus ?thesis using assms by (auto simp: extensional_def)
qed

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



definition%important abs_summable_on ::
    "('a \<Rightarrow> 'b :: {banach, second_countable_topology}) \<Rightarrow> 'a set \<Rightarrow> bool" 
    (infix "abs'_summable'_on" 50)
 where
   "f abs_summable_on A \<longleftrightarrow> integrable (count_space A) f"


definition%important infsetsum ::
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
  fun sum_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qinfsetsum"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | sum_tr' _ = raise Match;
in [(@{const_syntax infsetsum}, K sum_tr')] end
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
  by (metis (no_types) Pow_iff abs_summable_on_def inf.orderE integrable_restrict_space restrict_count_space_subset set_integrable_def sets_count_space space_count_space)

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

end
