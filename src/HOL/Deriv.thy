(*  Title:      HOL/Deriv.thy
    Author:     Jacques D. Fleuriot, University of Cambridge, 1998
    Author:     Brian Huffman
    Author:     Lawrence C Paulson, 2004
    Author:     Benjamin Porter, 2005
*)

section \<open>Differentiation\<close>

theory Deriv
  imports Limits
begin

subsection \<open>Frechet derivative\<close>

definition has_derivative :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> 'a filter \<Rightarrow> bool"  (infix "(has'_derivative)" 50)
  where "(f has_derivative f') F \<longleftrightarrow>
    bounded_linear f' \<and>
    ((\<lambda>y. ((f y - f (Lim F (\<lambda>x. x))) - f' (y - Lim F (\<lambda>x. x))) /\<^sub>R norm (y - Lim F (\<lambda>x. x))) \<longlongrightarrow> 0) F"

text \<open>
  Usually the filter \<^term>\<open>F\<close> is \<^term>\<open>at x within s\<close>.  \<^term>\<open>(f has_derivative D)
  (at x within s)\<close> means: \<^term>\<open>D\<close> is the derivative of function \<^term>\<open>f\<close> at point \<^term>\<open>x\<close>
  within the set \<^term>\<open>s\<close>. Where \<^term>\<open>s\<close> is used to express left or right sided derivatives. In
  most cases \<^term>\<open>s\<close> is either a variable or \<^term>\<open>UNIV\<close>.
\<close>

text \<open>These are the only cases we'll care about, probably.\<close>

lemma has_derivative_within: "(f has_derivative f') (at x within s) \<longleftrightarrow>
    bounded_linear f' \<and> ((\<lambda>y. (1 / norm(y - x)) *\<^sub>R (f y - (f x + f' (y - x)))) \<longlongrightarrow> 0) (at x within s)"
  unfolding has_derivative_def tendsto_iff
  by (subst eventually_Lim_ident_at) (auto simp add: field_simps)

lemma has_derivative_eq_rhs: "(f has_derivative f') F \<Longrightarrow> f' = g' \<Longrightarrow> (f has_derivative g') F"
  by simp

definition has_field_derivative :: "('a::real_normed_field \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a filter \<Rightarrow> bool"
    (infix "(has'_field'_derivative)" 50)
  where "(f has_field_derivative D) F \<longleftrightarrow> (f has_derivative (*) D) F"

lemma DERIV_cong: "(f has_field_derivative X) F \<Longrightarrow> X = Y \<Longrightarrow> (f has_field_derivative Y) F"
  by simp

definition has_vector_derivative :: "(real \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> real filter \<Rightarrow> bool"
    (infix "has'_vector'_derivative" 50)
  where "(f has_vector_derivative f') net \<longleftrightarrow> (f has_derivative (\<lambda>x. x *\<^sub>R f')) net"

lemma has_vector_derivative_eq_rhs:
  "(f has_vector_derivative X) F \<Longrightarrow> X = Y \<Longrightarrow> (f has_vector_derivative Y) F"
  by simp

named_theorems derivative_intros "structural introduction rules for derivatives"
setup \<open>
  let
    val eq_thms = @{thms has_derivative_eq_rhs DERIV_cong has_vector_derivative_eq_rhs}
    fun eq_rule thm = get_first (try (fn eq_thm => eq_thm OF [thm])) eq_thms
  in
    Global_Theory.add_thms_dynamic
      (\<^binding>\<open>derivative_eq_intros\<close>,
        fn context =>
          Named_Theorems.get (Context.proof_of context) \<^named_theorems>\<open>derivative_intros\<close>
          |> map_filter eq_rule)
  end
\<close>

text \<open>
  The following syntax is only used as a legacy syntax.
\<close>
abbreviation (input)
  FDERIV :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  ("(FDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "FDERIV f x :> f' \<equiv> (f has_derivative f') (at x)"

lemma has_derivative_bounded_linear: "(f has_derivative f') F \<Longrightarrow> bounded_linear f'"
  by (simp add: has_derivative_def)

lemma has_derivative_linear: "(f has_derivative f') F \<Longrightarrow> linear f'"
  using bounded_linear.linear[OF has_derivative_bounded_linear] .

lemma has_derivative_ident[derivative_intros, simp]: "((\<lambda>x. x) has_derivative (\<lambda>x. x)) F"
  by (simp add: has_derivative_def)

lemma has_derivative_id [derivative_intros, simp]: "(id has_derivative id) (at a)"
  by (metis eq_id_iff has_derivative_ident)

lemma has_derivative_const[derivative_intros, simp]: "((\<lambda>x. c) has_derivative (\<lambda>x. 0)) F"
  by (simp add: has_derivative_def)

lemma (in bounded_linear) bounded_linear: "bounded_linear f" ..

lemma (in bounded_linear) has_derivative:
  "(g has_derivative g') F \<Longrightarrow> ((\<lambda>x. f (g x)) has_derivative (\<lambda>x. f (g' x))) F"
  unfolding has_derivative_def
  by (auto simp add: bounded_linear_compose [OF bounded_linear] scaleR diff dest: tendsto)

lemmas has_derivative_scaleR_right [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_linear_scaleR_right]

lemmas has_derivative_scaleR_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_linear_scaleR_left]

lemmas has_derivative_mult_right [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_linear_mult_right]

lemmas has_derivative_mult_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_linear_mult_left]

lemmas has_derivative_of_real[derivative_intros, simp] = 
  bounded_linear.has_derivative[OF bounded_linear_of_real] 

lemma has_derivative_add[simp, derivative_intros]:
  assumes f: "(f has_derivative f') F"
    and g: "(g has_derivative g') F"
  shows "((\<lambda>x. f x + g x) has_derivative (\<lambda>x. f' x + g' x)) F"
  unfolding has_derivative_def
proof safe
  let ?x = "Lim F (\<lambda>x. x)"
  let ?D = "\<lambda>f f' y. ((f y - f ?x) - f' (y - ?x)) /\<^sub>R norm (y - ?x)"
  have "((\<lambda>x. ?D f f' x + ?D g g' x) \<longlongrightarrow> (0 + 0)) F"
    using f g by (intro tendsto_add) (auto simp: has_derivative_def)
  then show "(?D (\<lambda>x. f x + g x) (\<lambda>x. f' x + g' x) \<longlongrightarrow> 0) F"
    by (simp add: field_simps scaleR_add_right scaleR_diff_right)
qed (blast intro: bounded_linear_add f g has_derivative_bounded_linear)

lemma has_derivative_sum[simp, derivative_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i has_derivative f' i) F) \<Longrightarrow>
    ((\<lambda>x. \<Sum>i\<in>I. f i x) has_derivative (\<lambda>x. \<Sum>i\<in>I. f' i x)) F"
  by (induct I rule: infinite_finite_induct) simp_all

lemma has_derivative_minus[simp, derivative_intros]:
  "(f has_derivative f') F \<Longrightarrow> ((\<lambda>x. - f x) has_derivative (\<lambda>x. - f' x)) F"
  using has_derivative_scaleR_right[of f f' F "-1"] by simp

lemma has_derivative_diff[simp, derivative_intros]:
  "(f has_derivative f') F \<Longrightarrow> (g has_derivative g') F \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_derivative (\<lambda>x. f' x - g' x)) F"
  by (simp only: diff_conv_add_uminus has_derivative_add has_derivative_minus)

lemma has_derivative_at_within:
  "(f has_derivative f') (at x within s) \<longleftrightarrow>
    (bounded_linear f' \<and> ((\<lambda>y. ((f y - f x) - f' (y - x)) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within s))"
proof (cases "at x within s = bot")
  case True
  then show ?thesis
    by (metis (no_types, lifting) has_derivative_within tendsto_bot)
next
  case False
  then show ?thesis
  by (simp add: Lim_ident_at has_derivative_def)
qed

lemma has_derivative_iff_norm:
  "(f has_derivative f') (at x within s) \<longleftrightarrow>
    bounded_linear f' \<and> ((\<lambda>y. norm ((f y - f x) - f' (y - x)) / norm (y - x)) \<longlongrightarrow> 0) (at x within s)"
  using tendsto_norm_zero_iff[of _ "at x within s", where 'b="'b", symmetric]
  by (simp add: has_derivative_at_within divide_inverse ac_simps)

lemma has_derivative_at:
  "(f has_derivative D) (at x) \<longleftrightarrow>
    (bounded_linear D \<and> (\<lambda>h. norm (f (x + h) - f x - D h) / norm h) \<midarrow>0\<rightarrow> 0)"
  by (simp add: has_derivative_iff_norm LIM_offset_zero_iff)

lemma field_has_derivative_at:
  fixes x :: "'a::real_normed_field"
  shows "(f has_derivative (*) D) (at x) \<longleftrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow> D" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<lambda>h. norm (f (x + h) - f x - D * h) / norm h) \<midarrow>0 \<rightarrow> 0"
    by (simp add: bounded_linear_mult_right has_derivative_at)
  also have "... = (\<lambda>y. norm ((f (x + y) - f x - D * y) / y)) \<midarrow>0\<rightarrow> 0"
    by (simp cong: LIM_cong flip: nonzero_norm_divide)
  also have "... = (\<lambda>y. norm ((f (x + y) - f x) / y - D / y * y)) \<midarrow>0\<rightarrow> 0"
    by (simp only: diff_divide_distrib times_divide_eq_left [symmetric])
  also have "... = ?rhs"
    by (simp add: tendsto_norm_zero_iff LIM_zero_iff cong: LIM_cong)
  finally show ?thesis .
qed

lemma has_derivative_iff_Ex:
  "(f has_derivative f') (at x) \<longleftrightarrow>
    bounded_linear f' \<and> (\<exists>e. (\<forall>h. f (x+h) = f x + f' h + e h) \<and> ((\<lambda>h. norm (e h) / norm h) \<longlongrightarrow> 0) (at 0))"
  unfolding has_derivative_at by force

lemma has_derivative_at_within_iff_Ex:
  assumes "x \<in> S" "open S"
  shows "(f has_derivative f') (at x within S) \<longleftrightarrow>
         bounded_linear f' \<and> (\<exists>e. (\<forall>h. x+h \<in> S \<longrightarrow> f (x+h) = f x + f' h + e h) \<and> ((\<lambda>h. norm (e h) / norm h) \<longlongrightarrow> 0) (at 0))"
    (is "?lhs = ?rhs")
proof safe
  show "bounded_linear f'"
    if "(f has_derivative f') (at x within S)"
    using has_derivative_bounded_linear that by blast
  show "\<exists>e. (\<forall>h. x + h \<in> S \<longrightarrow> f (x + h) = f x + f' h + e h) \<and> (\<lambda>h. norm (e h) / norm h) \<midarrow>0\<rightarrow> 0"
    if "(f has_derivative f') (at x within S)"
    by (metis (full_types) assms that has_derivative_iff_Ex at_within_open)
  show "(f has_derivative f') (at x within S)"
    if "bounded_linear f'"
      and eq [rule_format]: "\<forall>h. x + h \<in> S \<longrightarrow> f (x + h) = f x + f' h + e h"
      and 0: "(\<lambda>h. norm (e (h::'a)::'b) / norm h) \<midarrow>0\<rightarrow> 0"
    for e 
  proof -
    have 1: "f y - f x = f' (y-x) + e (y-x)" if "y \<in> S" for y
      using eq [of "y-x"] that by simp
    have 2: "((\<lambda>y. norm (e (y-x)) / norm (y - x)) \<longlongrightarrow> 0) (at x within S)"
      by (simp add: "0" assms tendsto_offset_zero_iff)
    have "((\<lambda>y. norm (f y - f x - f' (y - x)) / norm (y - x)) \<longlongrightarrow> 0) (at x within S)"
      by (simp add: Lim_cong_within 1 2)
    then show ?thesis
      by (simp add: has_derivative_iff_norm \<open>bounded_linear f'\<close>)
  qed
qed

lemma has_derivativeI:
  "bounded_linear f' \<Longrightarrow>
    ((\<lambda>y. ((f y - f x) - f' (y - x)) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within s) \<Longrightarrow>
    (f has_derivative f') (at x within s)"
  by (simp add: has_derivative_at_within)

lemma has_derivativeI_sandwich:
  assumes e: "0 < e"
    and bounded: "bounded_linear f'"
    and sandwich: "(\<And>y. y \<in> s \<Longrightarrow> y \<noteq> x \<Longrightarrow> dist y x < e \<Longrightarrow>
      norm ((f y - f x) - f' (y - x)) / norm (y - x) \<le> H y)"
    and "(H \<longlongrightarrow> 0) (at x within s)"
  shows "(f has_derivative f') (at x within s)"
  unfolding has_derivative_iff_norm
proof safe
  show "((\<lambda>y. norm (f y - f x - f' (y - x)) / norm (y - x)) \<longlongrightarrow> 0) (at x within s)"
  proof (rule tendsto_sandwich[where f="\<lambda>x. 0"])
    show "(H \<longlongrightarrow> 0) (at x within s)" by fact
    show "eventually (\<lambda>n. norm (f n - f x - f' (n - x)) / norm (n - x) \<le> H n) (at x within s)"
      unfolding eventually_at using e sandwich by auto
  qed (auto simp: le_divide_eq)
qed fact

lemma has_derivative_subset:
  "(f has_derivative f') (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (f has_derivative f') (at x within t)"
  by (auto simp add: has_derivative_iff_norm intro: tendsto_within_subset)

lemma has_derivative_within_singleton_iff:
  "(f has_derivative g) (at x within {x}) \<longleftrightarrow> bounded_linear g"
  by (auto intro!: has_derivativeI_sandwich[where e=1] has_derivative_bounded_linear)


subsubsection \<open>Limit transformation for derivatives\<close>

lemma has_derivative_transform_within:
  assumes "(f has_derivative f') (at x within s)"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x' \<in> s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "(g has_derivative f') (at x within s)"
  using assms
  unfolding has_derivative_within
  by (force simp add: intro: Lim_transform_within)

lemma has_derivative_transform_within_open:
  assumes "(f has_derivative f') (at x within t)"
    and "open s"
    and "x \<in> s"
    and "\<And>x. x\<in>s \<Longrightarrow> f x = g x"
  shows "(g has_derivative f') (at x within t)"
  using assms unfolding has_derivative_within
  by (force simp add: intro: Lim_transform_within_open)

lemma has_derivative_transform:
  assumes "x \<in> s" "\<And>x. x \<in> s \<Longrightarrow> g x = f x"
  assumes "(f has_derivative f') (at x within s)"
  shows "(g has_derivative f') (at x within s)"
  using assms
  by (intro has_derivative_transform_within[OF _ zero_less_one, where g=g]) auto

lemma has_derivative_transform_eventually:
  assumes "(f has_derivative f') (at x within s)"
    "(\<forall>\<^sub>F x' in at x within s. f x' = g x')"
  assumes "f x = g x" "x \<in> s"
  shows "(g has_derivative f') (at x within s)"
  using assms
proof -
  from assms(2,3) obtain d where "d > 0" "\<And>x'. x' \<in> s \<Longrightarrow> dist x' x < d \<Longrightarrow> f x' = g x'"
    by (force simp: eventually_at)
  from has_derivative_transform_within[OF assms(1) this(1) assms(4) this(2)]
  show ?thesis .
qed

lemma has_field_derivative_transform_within:
  assumes "(f has_field_derivative f') (at a within S)"
    and "0 < d"
    and "a \<in> S"
    and "\<And>x. \<lbrakk>x \<in> S; dist x a < d\<rbrakk> \<Longrightarrow> f x = g x"
  shows "(g has_field_derivative f') (at a within S)"
  using assms unfolding has_field_derivative_def
  by (metis has_derivative_transform_within)

lemma has_field_derivative_transform_within_open:
  assumes "(f has_field_derivative f') (at a)"
    and "open S" "a \<in> S"
    and "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "(g has_field_derivative f') (at a)"
  using assms unfolding has_field_derivative_def
  by (metis has_derivative_transform_within_open)


subsection \<open>Continuity\<close>

lemma has_derivative_continuous:
  assumes f: "(f has_derivative f') (at x within s)"
  shows "continuous (at x within s) f"
proof -
  from f interpret F: bounded_linear f'
    by (rule has_derivative_bounded_linear)
  note F.tendsto[tendsto_intros]
  let ?L = "\<lambda>f. (f \<longlongrightarrow> 0) (at x within s)"
  have "?L (\<lambda>y. norm ((f y - f x) - f' (y - x)) / norm (y - x))"
    using f unfolding has_derivative_iff_norm by blast
  then have "?L (\<lambda>y. norm ((f y - f x) - f' (y - x)) / norm (y - x) * norm (y - x))" (is ?m)
    by (rule tendsto_mult_zero) (auto intro!: tendsto_eq_intros)
  also have "?m \<longleftrightarrow> ?L (\<lambda>y. norm ((f y - f x) - f' (y - x)))"
    by (intro filterlim_cong) (simp_all add: eventually_at_filter)
  finally have "?L (\<lambda>y. (f y - f x) - f' (y - x))"
    by (rule tendsto_norm_zero_cancel)
  then have "?L (\<lambda>y. ((f y - f x) - f' (y - x)) + f' (y - x))"
    by (rule tendsto_eq_intros) (auto intro!: tendsto_eq_intros simp: F.zero)
  then have "?L (\<lambda>y. f y - f x)"
    by simp
  from tendsto_add[OF this tendsto_const, of "f x"] show ?thesis
    by (simp add: continuous_within)
qed


subsection \<open>Composition\<close>

lemma tendsto_at_iff_tendsto_nhds_within:
  "f x = y \<Longrightarrow> (f \<longlongrightarrow> y) (at x within s) \<longleftrightarrow> (f \<longlongrightarrow> y) (inf (nhds x) (principal s))"
  unfolding tendsto_def eventually_inf_principal eventually_at_filter
  by (intro ext all_cong imp_cong) (auto elim!: eventually_mono)

lemma has_derivative_in_compose:
  assumes f: "(f has_derivative f') (at x within s)"
    and g: "(g has_derivative g') (at (f x) within (f`s))"
  shows "((\<lambda>x. g (f x)) has_derivative (\<lambda>x. g' (f' x))) (at x within s)"
proof -
  from f interpret F: bounded_linear f'
    by (rule has_derivative_bounded_linear)
  from g interpret G: bounded_linear g'
    by (rule has_derivative_bounded_linear)
  from F.bounded obtain kF where kF: "\<And>x. norm (f' x) \<le> norm x * kF"
    by fast
  from G.bounded obtain kG where kG: "\<And>x. norm (g' x) \<le> norm x * kG"
    by fast
  note G.tendsto[tendsto_intros]

  let ?L = "\<lambda>f. (f \<longlongrightarrow> 0) (at x within s)"
  let ?D = "\<lambda>f f' x y. (f y - f x) - f' (y - x)"
  let ?N = "\<lambda>f f' x y. norm (?D f f' x y) / norm (y - x)"
  let ?gf = "\<lambda>x. g (f x)" and ?gf' = "\<lambda>x. g' (f' x)"
  define Nf where "Nf = ?N f f' x"
  define Ng where [abs_def]: "Ng y = ?N g g' (f x) (f y)" for y

  show ?thesis
  proof (rule has_derivativeI_sandwich[of 1])
    show "bounded_linear (\<lambda>x. g' (f' x))"
      using f g by (blast intro: bounded_linear_compose has_derivative_bounded_linear)
  next
    fix y :: 'a
    assume neq: "y \<noteq> x"
    have "?N ?gf ?gf' x y = norm (g' (?D f f' x y) + ?D g g' (f x) (f y)) / norm (y - x)"
      by (simp add: G.diff G.add field_simps)
    also have "\<dots> \<le> norm (g' (?D f f' x y)) / norm (y - x) + Ng y * (norm (f y - f x) / norm (y - x))"
      by (simp add: add_divide_distrib[symmetric] divide_right_mono norm_triangle_ineq G.zero Ng_def)
    also have "\<dots> \<le> Nf y * kG + Ng y * (Nf y + kF)"
    proof (intro add_mono mult_left_mono)
      have "norm (f y - f x) = norm (?D f f' x y + f' (y - x))"
        by simp
      also have "\<dots> \<le> norm (?D f f' x y) + norm (f' (y - x))"
        by (rule norm_triangle_ineq)
      also have "\<dots> \<le> norm (?D f f' x y) + norm (y - x) * kF"
        using kF by (intro add_mono) simp
      finally show "norm (f y - f x) / norm (y - x) \<le> Nf y + kF"
        by (simp add: neq Nf_def field_simps)
    qed (use kG in \<open>simp_all add: Ng_def Nf_def neq zero_le_divide_iff field_simps\<close>)
    finally show "?N ?gf ?gf' x y \<le> Nf y * kG + Ng y * (Nf y + kF)" .
  next
    have [tendsto_intros]: "?L Nf"
      using f unfolding has_derivative_iff_norm Nf_def ..
    from f have "(f \<longlongrightarrow> f x) (at x within s)"
      by (blast intro: has_derivative_continuous continuous_within[THEN iffD1])
    then have f': "LIM x at x within s. f x :> inf (nhds (f x)) (principal (f`s))"
      unfolding filterlim_def
      by (simp add: eventually_filtermap eventually_at_filter le_principal)

    have "((?N g  g' (f x)) \<longlongrightarrow> 0) (at (f x) within f`s)"
      using g unfolding has_derivative_iff_norm ..
    then have g': "((?N g  g' (f x)) \<longlongrightarrow> 0) (inf (nhds (f x)) (principal (f`s)))"
      by (rule tendsto_at_iff_tendsto_nhds_within[THEN iffD1, rotated]) simp

    have [tendsto_intros]: "?L Ng"
      unfolding Ng_def by (rule filterlim_compose[OF g' f'])
    show "((\<lambda>y. Nf y * kG + Ng y * (Nf y + kF)) \<longlongrightarrow> 0) (at x within s)"
      by (intro tendsto_eq_intros) auto
  qed simp
qed

lemma has_derivative_compose:
  "(f has_derivative f') (at x within s) \<Longrightarrow> (g has_derivative g') (at (f x)) \<Longrightarrow>
  ((\<lambda>x. g (f x)) has_derivative (\<lambda>x. g' (f' x))) (at x within s)"
  by (blast intro: has_derivative_in_compose has_derivative_subset)

lemma has_derivative_in_compose2:
  assumes "\<And>x. x \<in> t \<Longrightarrow> (g has_derivative g' x) (at x within t)"
  assumes "f ` s \<subseteq> t" "x \<in> s"
  assumes "(f has_derivative f') (at x within s)"
  shows "((\<lambda>x. g (f x)) has_derivative (\<lambda>y. g' (f x) (f' y))) (at x within s)"
  using assms
  by (auto intro: has_derivative_subset intro!: has_derivative_in_compose[of f f' x s g])

lemma (in bounded_bilinear) FDERIV:
  assumes f: "(f has_derivative f') (at x within s)" and g: "(g has_derivative g') (at x within s)"
  shows "((\<lambda>x. f x ** g x) has_derivative (\<lambda>h. f x ** g' h + f' h ** g x)) (at x within s)"
proof -
  from bounded_linear.bounded [OF has_derivative_bounded_linear [OF f]]
  obtain KF where norm_F: "\<And>x. norm (f' x) \<le> norm x * KF" by fast

  from pos_bounded obtain K
    where K: "0 < K" and norm_prod: "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    by fast
  let ?D = "\<lambda>f f' y. f y - f x - f' (y - x)"
  let ?N = "\<lambda>f f' y. norm (?D f f' y) / norm (y - x)"
  define Ng where "Ng = ?N g g'"
  define Nf where "Nf = ?N f f'"

  let ?fun1 = "\<lambda>y. norm (f y ** g y - f x ** g x - (f x ** g' (y - x) + f' (y - x) ** g x)) / norm (y - x)"
  let ?fun2 = "\<lambda>y. norm (f x) * Ng y * K + Nf y * norm (g y) * K + KF * norm (g y - g x) * K"
  let ?F = "at x within s"

  show ?thesis
  proof (rule has_derivativeI_sandwich[of 1])
    show "bounded_linear (\<lambda>h. f x ** g' h + f' h ** g x)"
      by (intro bounded_linear_add
        bounded_linear_compose [OF bounded_linear_right] bounded_linear_compose [OF bounded_linear_left]
        has_derivative_bounded_linear [OF g] has_derivative_bounded_linear [OF f])
  next
    from g have "(g \<longlongrightarrow> g x) ?F"
      by (intro continuous_within[THEN iffD1] has_derivative_continuous)
    moreover from f g have "(Nf \<longlongrightarrow> 0) ?F" "(Ng \<longlongrightarrow> 0) ?F"
      by (simp_all add: has_derivative_iff_norm Ng_def Nf_def)
    ultimately have "(?fun2 \<longlongrightarrow> norm (f x) * 0 * K + 0 * norm (g x) * K + KF * norm (0::'b) * K) ?F"
      by (intro tendsto_intros) (simp_all add: LIM_zero_iff)
    then show "(?fun2 \<longlongrightarrow> 0) ?F"
      by simp
  next
    fix y :: 'd
    assume "y \<noteq> x"
    have "?fun1 y =
        norm (f x ** ?D g g' y + ?D f f' y ** g y + f' (y - x) ** (g y - g x)) / norm (y - x)"
      by (simp add: diff_left diff_right add_left add_right field_simps)
    also have "\<dots> \<le> (norm (f x) * norm (?D g g' y) * K + norm (?D f f' y) * norm (g y) * K +
        norm (y - x) * KF * norm (g y - g x) * K) / norm (y - x)"
      by (intro divide_right_mono mult_mono'
                order_trans [OF norm_triangle_ineq add_mono]
                order_trans [OF norm_prod mult_right_mono]
                mult_nonneg_nonneg order_refl norm_ge_zero norm_F
                K [THEN order_less_imp_le])
    also have "\<dots> = ?fun2 y"
      by (simp add: add_divide_distrib Ng_def Nf_def)
    finally show "?fun1 y \<le> ?fun2 y" .
  qed simp
qed

lemmas has_derivative_mult[simp, derivative_intros] = bounded_bilinear.FDERIV[OF bounded_bilinear_mult]
lemmas has_derivative_scaleR[simp, derivative_intros] = bounded_bilinear.FDERIV[OF bounded_bilinear_scaleR]

lemma has_derivative_prod[simp, derivative_intros]:
  fixes f :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_field"
  shows "(\<And>i. i \<in> I \<Longrightarrow> (f i has_derivative f' i) (at x within S)) \<Longrightarrow>
    ((\<lambda>x. \<Prod>i\<in>I. f i x) has_derivative (\<lambda>y. \<Sum>i\<in>I. f' i y * (\<Prod>j\<in>I - {i}. f j x))) (at x within S)"
proof (induct I rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert i I)
  let ?P = "\<lambda>y. f i x * (\<Sum>i\<in>I. f' i y * (\<Prod>j\<in>I - {i}. f j x)) + (f' i y) * (\<Prod>i\<in>I. f i x)"
  have "((\<lambda>x. f i x * (\<Prod>i\<in>I. f i x)) has_derivative ?P) (at x within S)"
    using insert by (intro has_derivative_mult) auto
  also have "?P = (\<lambda>y. \<Sum>i'\<in>insert i I. f' i' y * (\<Prod>j\<in>insert i I - {i'}. f j x))"
    using insert(1,2)
    by (auto simp add: sum_distrib_left insert_Diff_if intro!: ext sum.cong)
  finally show ?case
    using insert by simp
qed

lemma has_derivative_power[simp, derivative_intros]:
  fixes f :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_field"
  assumes f: "(f has_derivative f') (at x within S)"
  shows "((\<lambda>x. f x^n) has_derivative (\<lambda>y. of_nat n * f' y * f x^(n - 1))) (at x within S)"
  using has_derivative_prod[OF f, of "{..< n}"] by (simp add: prod_constant ac_simps)

lemma has_derivative_inverse':
  fixes x :: "'a::real_normed_div_algebra"
  assumes x: "x \<noteq> 0"
  shows "(inverse has_derivative (\<lambda>h. - (inverse x * h * inverse x))) (at x within S)"
    (is "(_ has_derivative ?f) _")
proof (rule has_derivativeI_sandwich)
  show "bounded_linear (\<lambda>h. - (inverse x * h * inverse x))"
    by (simp add: bounded_linear_minus bounded_linear_mult_const bounded_linear_mult_right)
  show "0 < norm x" using x by simp
  have "(inverse \<longlongrightarrow> inverse x) (at x within S)"
    using tendsto_inverse tendsto_ident_at x by auto
  then show "((\<lambda>y. norm (inverse y - inverse x) * norm (inverse x)) \<longlongrightarrow> 0) (at x within S)"
    by (simp add: LIM_zero_iff tendsto_mult_left_zero tendsto_norm_zero)
next
  fix y :: 'a
  assume h: "y \<noteq> x" "dist y x < norm x"
  then have "y \<noteq> 0" by auto
  have "norm (inverse y - inverse x - ?f (y -x)) / norm (y - x) 
        = norm (- (inverse y * (y - x) * inverse x - inverse x * (y - x) * inverse x)) /
                norm (y - x)"
    by (simp add: \<open>y \<noteq> 0\<close> inverse_diff_inverse x)
  also have "... = norm ((inverse y - inverse x) * (y - x) * inverse x) / norm (y - x)"
    by (simp add: left_diff_distrib norm_minus_commute)
  also have "\<dots> \<le> norm (inverse y - inverse x) * norm (y - x) * norm (inverse x) / norm (y - x)"
    by (simp add: norm_mult)
  also have "\<dots> = norm (inverse y - inverse x) * norm (inverse x)"
    by simp
  finally show "norm (inverse y - inverse x - ?f (y -x)) / norm (y - x) \<le>
    norm (inverse y - inverse x) * norm (inverse x)" .
qed

lemma has_derivative_inverse[simp, derivative_intros]:
  fixes f :: "_ \<Rightarrow> 'a::real_normed_div_algebra"
  assumes x:  "f x \<noteq> 0"
    and f: "(f has_derivative f') (at x within S)"
  shows "((\<lambda>x. inverse (f x)) has_derivative (\<lambda>h. - (inverse (f x) * f' h * inverse (f x))))
    (at x within S)"
  using has_derivative_compose[OF f has_derivative_inverse', OF x] .

lemma has_derivative_divide[simp, derivative_intros]:
  fixes f :: "_ \<Rightarrow> 'a::real_normed_div_algebra"
  assumes f: "(f has_derivative f') (at x within S)"
    and g: "(g has_derivative g') (at x within S)"
  assumes x: "g x \<noteq> 0"
  shows "((\<lambda>x. f x / g x) has_derivative
                (\<lambda>h. - f x * (inverse (g x) * g' h * inverse (g x)) + f' h / g x)) (at x within S)"
  using has_derivative_mult[OF f has_derivative_inverse[OF x g]]
  by (simp add: field_simps)

lemma has_derivative_power_int':
  fixes x :: "'a::real_normed_field"
  assumes x: "x \<noteq> 0"
  shows "((\<lambda>x. power_int x n) has_derivative (\<lambda>y. y * (of_int n * power_int x (n - 1)))) (at x within S)"
proof (cases n rule: int_cases4)
  case (nonneg n)
  thus ?thesis using x
    by (cases "n = 0") (auto intro!: derivative_eq_intros simp: field_simps power_int_diff fun_eq_iff
                             simp flip: power_Suc)
next
  case (neg n)
  thus ?thesis using x
    by (auto intro!: derivative_eq_intros simp: field_simps power_int_diff power_int_minus
             simp flip: power_Suc power_Suc2 power_add)
qed

lemma has_derivative_power_int[simp, derivative_intros]:
  fixes f :: "_ \<Rightarrow> 'a::real_normed_field"
  assumes x:  "f x \<noteq> 0"
    and f: "(f has_derivative f') (at x within S)"
  shows "((\<lambda>x. power_int (f x) n) has_derivative (\<lambda>h. f' h * (of_int n * power_int (f x) (n - 1))))
           (at x within S)"
  using has_derivative_compose[OF f has_derivative_power_int', OF x] .


text \<open>Conventional form requires mult-AC laws. Types real and complex only.\<close>

lemma has_derivative_divide'[derivative_intros]:
  fixes f :: "_ \<Rightarrow> 'a::real_normed_field"
  assumes f: "(f has_derivative f') (at x within S)"
    and g: "(g has_derivative g') (at x within S)"
    and x: "g x \<noteq> 0"
  shows "((\<lambda>x. f x / g x) has_derivative (\<lambda>h. (f' h * g x - f x * g' h) / (g x * g x))) (at x within S)"
proof -
  have "f' h / g x - f x * (inverse (g x) * g' h * inverse (g x)) =
      (f' h * g x - f x * g' h) / (g x * g x)" for h
    by (simp add: field_simps x)
  then show ?thesis
    using has_derivative_divide [OF f g] x
    by simp
qed


subsection \<open>Uniqueness\<close>

text \<open>
This can not generally shown for \<^const>\<open>has_derivative\<close>, as we need to approach the point from
all directions. There is a proof in \<open>Analysis\<close> for \<open>euclidean_space\<close>.
\<close>

lemma has_derivative_at2: "(f has_derivative f') (at x) \<longleftrightarrow>
    bounded_linear f' \<and> ((\<lambda>y. (1 / (norm(y - x))) *\<^sub>R (f y - (f x + f' (y - x)))) \<longlongrightarrow> 0) (at x)"
  using has_derivative_within [of f f' x UNIV]
  by simp

lemma has_derivative_zero_unique:
  assumes "((\<lambda>x. 0) has_derivative F) (at x)"
  shows "F = (\<lambda>h. 0)"
proof -
  interpret F: bounded_linear F
    using assms by (rule has_derivative_bounded_linear)
  let ?r = "\<lambda>h. norm (F h) / norm h"
  have *: "?r \<midarrow>0\<rightarrow> 0"
    using assms unfolding has_derivative_at by simp
  show "F = (\<lambda>h. 0)"
  proof
    show "F h = 0" for h
    proof (rule ccontr)
      assume **: "\<not> ?thesis"
      then have h: "h \<noteq> 0"
        by (auto simp add: F.zero)
      with ** have "0 < ?r h"
        by simp
      from LIM_D [OF * this] obtain S
        where S: "0 < S" and r: "\<And>x. x \<noteq> 0 \<Longrightarrow> norm x < S \<Longrightarrow> ?r x < ?r h"
        by auto
      from dense [OF S] obtain t where t: "0 < t \<and> t < S" ..
      let ?x = "scaleR (t / norm h) h"
      have "?x \<noteq> 0" and "norm ?x < S"
        using t h by simp_all
      then have "?r ?x < ?r h"
        by (rule r)
      then show False
        using t h by (simp add: F.scaleR)
    qed
  qed
qed

lemma has_derivative_unique:
  assumes "(f has_derivative F) (at x)"
    and "(f has_derivative F') (at x)"
  shows "F = F'"
proof -
  have "((\<lambda>x. 0) has_derivative (\<lambda>h. F h - F' h)) (at x)"
    using has_derivative_diff [OF assms] by simp
  then have "(\<lambda>h. F h - F' h) = (\<lambda>h. 0)"
    by (rule has_derivative_zero_unique)
  then show "F = F'"
    unfolding fun_eq_iff right_minus_eq .
qed

lemma has_derivative_Uniq: "\<exists>\<^sub>\<le>\<^sub>1F. (f has_derivative F) (at x)"
  by (simp add: Uniq_def has_derivative_unique)


subsection \<open>Differentiability predicate\<close>

definition differentiable :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
    (infix "differentiable" 50)
  where "f differentiable F \<longleftrightarrow> (\<exists>D. (f has_derivative D) F)"

lemma differentiable_subset:
  "f differentiable (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow> f differentiable (at x within t)"
  unfolding differentiable_def by (blast intro: has_derivative_subset)

lemmas differentiable_within_subset = differentiable_subset

lemma differentiable_ident [simp, derivative_intros]: "(\<lambda>x. x) differentiable F"
  unfolding differentiable_def by (blast intro: has_derivative_ident)

lemma differentiable_const [simp, derivative_intros]: "(\<lambda>z. a) differentiable F"
  unfolding differentiable_def by (blast intro: has_derivative_const)

lemma differentiable_in_compose:
  "f differentiable (at (g x) within (g`s)) \<Longrightarrow> g differentiable (at x within s) \<Longrightarrow>
    (\<lambda>x. f (g x)) differentiable (at x within s)"
  unfolding differentiable_def by (blast intro: has_derivative_in_compose)

lemma differentiable_compose:
  "f differentiable (at (g x)) \<Longrightarrow> g differentiable (at x within s) \<Longrightarrow>
    (\<lambda>x. f (g x)) differentiable (at x within s)"
  by (blast intro: differentiable_in_compose differentiable_subset)

lemma differentiable_add [simp, derivative_intros]:
  "f differentiable F \<Longrightarrow> g differentiable F \<Longrightarrow> (\<lambda>x. f x + g x) differentiable F"
  unfolding differentiable_def by (blast intro: has_derivative_add)

lemma differentiable_sum[simp, derivative_intros]:
  assumes "finite s" "\<forall>a\<in>s. (f a) differentiable net"
  shows "(\<lambda>x. sum (\<lambda>a. f a x) s) differentiable net"
proof -
  from bchoice[OF assms(2)[unfolded differentiable_def]]
  show ?thesis
    by (auto intro!: has_derivative_sum simp: differentiable_def)
qed

lemma differentiable_minus [simp, derivative_intros]:
  "f differentiable F \<Longrightarrow> (\<lambda>x. - f x) differentiable F"
  unfolding differentiable_def by (blast intro: has_derivative_minus)

lemma differentiable_diff [simp, derivative_intros]:
  "f differentiable F \<Longrightarrow> g differentiable F \<Longrightarrow> (\<lambda>x. f x - g x) differentiable F"
  unfolding differentiable_def by (blast intro: has_derivative_diff)

lemma differentiable_mult [simp, derivative_intros]:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "f differentiable (at x within s) \<Longrightarrow> g differentiable (at x within s) \<Longrightarrow>
    (\<lambda>x. f x * g x) differentiable (at x within s)"
  unfolding differentiable_def by (blast intro: has_derivative_mult)

lemma differentiable_cmult_left_iff [simp]:
  fixes c::"'a::real_normed_field" 
  shows "(\<lambda>t. c * q t) differentiable at t \<longleftrightarrow> c = 0 \<or> (\<lambda>t. q t) differentiable at t" (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  {assume "c \<noteq> 0"
    then have "q differentiable at t"
      using differentiable_mult [OF differentiable_const L, of concl: "1/c"] by auto
  } then show ?rhs
    by auto
qed auto

lemma differentiable_cmult_right_iff [simp]:
  fixes c::"'a::real_normed_field" 
  shows "(\<lambda>t. q t * c) differentiable at t \<longleftrightarrow> c = 0 \<or> (\<lambda>t. q t) differentiable at t" (is "?lhs = ?rhs")
  by (simp add: mult.commute flip: differentiable_cmult_left_iff)

lemma differentiable_inverse [simp, derivative_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_field"
  shows "f differentiable (at x within s) \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow>
    (\<lambda>x. inverse (f x)) differentiable (at x within s)"
  unfolding differentiable_def by (blast intro: has_derivative_inverse)

lemma differentiable_divide [simp, derivative_intros]:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_field"
  shows "f differentiable (at x within s) \<Longrightarrow> g differentiable (at x within s) \<Longrightarrow>
    g x \<noteq> 0 \<Longrightarrow> (\<lambda>x. f x / g x) differentiable (at x within s)"
  unfolding divide_inverse by simp

lemma differentiable_power [simp, derivative_intros]:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_field"
  shows "f differentiable (at x within s) \<Longrightarrow> (\<lambda>x. f x ^ n) differentiable (at x within s)"
  unfolding differentiable_def by (blast intro: has_derivative_power)

lemma differentiable_power_int [simp, derivative_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_field"
  shows "f differentiable (at x within s) \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow>
           (\<lambda>x. power_int (f x) n) differentiable (at x within s)"
  unfolding differentiable_def by (blast intro: has_derivative_power_int)

lemma differentiable_scaleR [simp, derivative_intros]:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable (at x within s) \<Longrightarrow>
    (\<lambda>x. f x *\<^sub>R g x) differentiable (at x within s)"
  unfolding differentiable_def by (blast intro: has_derivative_scaleR)

lemma has_derivative_imp_has_field_derivative:
  "(f has_derivative D) F \<Longrightarrow> (\<And>x. x * D' = D x) \<Longrightarrow> (f has_field_derivative D') F"
  unfolding has_field_derivative_def
  by (rule has_derivative_eq_rhs[of f D]) (simp_all add: fun_eq_iff mult.commute)

lemma has_field_derivative_imp_has_derivative:
  "(f has_field_derivative D) F \<Longrightarrow> (f has_derivative (*) D) F"
  by (simp add: has_field_derivative_def)

lemma DERIV_subset:
  "(f has_field_derivative f') (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (f has_field_derivative f') (at x within t)"
  by (simp add: has_field_derivative_def has_derivative_subset)

lemma has_field_derivative_at_within:
  "(f has_field_derivative f') (at x) \<Longrightarrow> (f has_field_derivative f') (at x within s)"
  using DERIV_subset by blast

abbreviation (input)
  DERIV :: "('a::real_normed_field \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    ("(DERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "DERIV f x :> D \<equiv> (f has_field_derivative D) (at x)"

abbreviation has_real_derivative :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real filter \<Rightarrow> bool"
    (infix "(has'_real'_derivative)" 50)
  where "(f has_real_derivative D) F \<equiv> (f has_field_derivative D) F"

lemma real_differentiable_def:
  "f differentiable at x within s \<longleftrightarrow> (\<exists>D. (f has_real_derivative D) (at x within s))"
proof safe
  assume "f differentiable at x within s"
  then obtain f' where *: "(f has_derivative f') (at x within s)"
    unfolding differentiable_def by auto
  then obtain c where "f' = ((*) c)"
    by (metis real_bounded_linear has_derivative_bounded_linear mult.commute fun_eq_iff)
  with * show "\<exists>D. (f has_real_derivative D) (at x within s)"
    unfolding has_field_derivative_def by auto
qed (auto simp: differentiable_def has_field_derivative_def)

lemma real_differentiableE [elim?]:
  assumes f: "f differentiable (at x within s)"
  obtains df where "(f has_real_derivative df) (at x within s)"
  using assms by (auto simp: real_differentiable_def)

lemma has_field_derivative_iff:
  "(f has_field_derivative D) (at x within S) \<longleftrightarrow>
    ((\<lambda>y. (f y - f x) / (y - x)) \<longlongrightarrow> D) (at x within S)"
proof -
  have "((\<lambda>y. norm (f y - f x - D * (y - x)) / norm (y - x)) \<longlongrightarrow> 0) (at x within S) 
      = ((\<lambda>y. (f y - f x) / (y - x) - D) \<longlongrightarrow> 0) (at x within S)"
    apply (subst tendsto_norm_zero_iff[symmetric], rule filterlim_cong)
      apply (simp_all add: eventually_at_filter field_simps nonzero_norm_divide)
    done
  then show ?thesis
    by (simp add: has_field_derivative_def has_derivative_iff_norm bounded_linear_mult_right LIM_zero_iff)
qed

lemma DERIV_def: "DERIV f x :> D \<longleftrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow> D"
  unfolding field_has_derivative_at has_field_derivative_def has_field_derivative_iff ..

lemma field_derivative_lim_unique:
  assumes f: "(f has_field_derivative df) (at z)"
      and s: "s \<longlonglongrightarrow> 0"  "\<And>n. s n \<noteq> 0" 
      and a: "(\<lambda>n. (f (z + s n) - f z) / s n) \<longlonglongrightarrow> a"
    shows "df = a"
proof (rule ccontr)
  assume "df \<noteq> a"
  obtain q where qpos: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> q \<epsilon> > 0" 
             and q: "\<And>\<epsilon> y. \<lbrakk>\<epsilon> > 0; y \<noteq> z; dist y z < q \<epsilon>\<rbrakk> \<Longrightarrow> dist ((f y - f z) / (y - z)) df < \<epsilon>"
    using f unfolding LIM_def has_field_derivative_iff by metis
  obtain NA where NA: "\<And>\<epsilon> n. \<lbrakk>\<epsilon> > 0; n \<ge> NA \<epsilon>\<rbrakk> \<Longrightarrow> dist ((f (z + s n) - f z) / s n) a < \<epsilon>" 
    using a unfolding LIMSEQ_def by metis
  obtain NB where NB: "\<And>\<epsilon> n. \<lbrakk>\<epsilon> > 0; n \<ge> NB \<epsilon>\<rbrakk> \<Longrightarrow> norm (s n) < \<epsilon>" 
    using s unfolding LIMSEQ_def by (metis norm_conv_dist)
  have df: "\<And>\<epsilon> n. \<epsilon> > 0 \<Longrightarrow> \<lbrakk>0 < \<epsilon>; norm (s n) < q \<epsilon>\<rbrakk> \<Longrightarrow> dist ((f (z + s n) - f z) / s n) df < \<epsilon>"
    using add_cancel_left_right add_diff_cancel_left' q s
    by (metis add_diff_cancel_right' dist_diff(1))
  define \<delta> where "\<delta> \<equiv> dist df a / 2"
  with \<open>df \<noteq> a\<close> have "\<delta> > 0" and \<delta>: "\<delta>+\<delta> \<le> dist df a"
    by auto
  define N where "N \<equiv> max (NA \<delta>) (NB (q \<delta>))"
  then have "norm (s N) < q \<delta>"
    by (simp add: NB \<open>\<delta> > 0\<close> qpos)
  then have "dist ((f (z + s N) - f z) / s N) df < \<delta>"
    by (simp add: \<open>0 < \<delta>\<close> df)
  moreover have "dist ((f (z + s N) - f z) / s N) a < \<delta>"
    using NA N_def \<open>0 < \<delta>\<close> by force
  ultimately have "dist df a < dist df a"
    by (smt (verit, ccfv_SIG) \<delta> dist_commute dist_triangle)
  then show False ..
qed

lemma mult_commute_abs: "(\<lambda>x. x * c) = (*) c"
  for c :: "'a::ab_semigroup_mult"
  by (simp add: fun_eq_iff mult.commute)

lemma DERIV_compose_FDERIV:
  fixes f::"real\<Rightarrow>real"
  assumes "DERIV f (g x) :> f'"
  assumes "(g has_derivative g') (at x within s)"
  shows "((\<lambda>x. f (g x)) has_derivative (\<lambda>x. g' x * f')) (at x within s)"
  using assms has_derivative_compose[of g g' x s f "(*) f'"]
  by (auto simp: has_field_derivative_def ac_simps)


subsection \<open>Vector derivative\<close>

lemma has_field_derivative_iff_has_vector_derivative:
  "(f has_field_derivative y) F \<longleftrightarrow> (f has_vector_derivative y) F"
  unfolding has_vector_derivative_def has_field_derivative_def real_scaleR_def mult_commute_abs ..

lemma has_field_derivative_subset:
  "(f has_field_derivative y) (at x within s) \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (f has_field_derivative y) (at x within t)"
  unfolding has_field_derivative_def by (rule has_derivative_subset)

lemma has_vector_derivative_const[simp, derivative_intros]: "((\<lambda>x. c) has_vector_derivative 0) net"
  by (auto simp: has_vector_derivative_def)

lemma has_vector_derivative_id[simp, derivative_intros]: "((\<lambda>x. x) has_vector_derivative 1) net"
  by (auto simp: has_vector_derivative_def)

lemma has_vector_derivative_minus[derivative_intros]:
  "(f has_vector_derivative f') net \<Longrightarrow> ((\<lambda>x. - f x) has_vector_derivative (- f')) net"
  by (auto simp: has_vector_derivative_def)

lemma has_vector_derivative_add[derivative_intros]:
  "(f has_vector_derivative f') net \<Longrightarrow> (g has_vector_derivative g') net \<Longrightarrow>
    ((\<lambda>x. f x + g x) has_vector_derivative (f' + g')) net"
  by (auto simp: has_vector_derivative_def scaleR_right_distrib)

lemma has_vector_derivative_sum[derivative_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i has_vector_derivative f' i) net) \<Longrightarrow>
    ((\<lambda>x. \<Sum>i\<in>I. f i x) has_vector_derivative (\<Sum>i\<in>I. f' i)) net"
  by (auto simp: has_vector_derivative_def fun_eq_iff scaleR_sum_right intro!: derivative_eq_intros)

lemma has_vector_derivative_diff[derivative_intros]:
  "(f has_vector_derivative f') net \<Longrightarrow> (g has_vector_derivative g') net \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_vector_derivative (f' - g')) net"
  by (auto simp: has_vector_derivative_def scaleR_diff_right)

lemma has_vector_derivative_add_const:
  "((\<lambda>t. g t + z) has_vector_derivative f') net = ((\<lambda>t. g t) has_vector_derivative f') net"
  apply (intro iffI)
   apply (force dest: has_vector_derivative_diff [where g = "\<lambda>t. z", OF _ has_vector_derivative_const])
  apply (force dest: has_vector_derivative_add [OF _ has_vector_derivative_const])
  done

lemma has_vector_derivative_diff_const:
  "((\<lambda>t. g t - z) has_vector_derivative f') net = ((\<lambda>t. g t) has_vector_derivative f') net"
  using has_vector_derivative_add_const [where z = "-z"]
  by simp

lemma (in bounded_linear) has_vector_derivative:
  assumes "(g has_vector_derivative g') F"
  shows "((\<lambda>x. f (g x)) has_vector_derivative f g') F"
  using has_derivative[OF assms[unfolded has_vector_derivative_def]]
  by (simp add: has_vector_derivative_def scaleR)

lemma (in bounded_bilinear) has_vector_derivative:
  assumes "(f has_vector_derivative f') (at x within s)"
    and "(g has_vector_derivative g') (at x within s)"
  shows "((\<lambda>x. f x ** g x) has_vector_derivative (f x ** g' + f' ** g x)) (at x within s)"
  using FDERIV[OF assms(1-2)[unfolded has_vector_derivative_def]]
  by (simp add: has_vector_derivative_def scaleR_right scaleR_left scaleR_right_distrib)

lemma has_vector_derivative_scaleR[derivative_intros]:
  "(f has_field_derivative f') (at x within s) \<Longrightarrow> (g has_vector_derivative g') (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x *\<^sub>R g x) has_vector_derivative (f x *\<^sub>R g' + f' *\<^sub>R g x)) (at x within s)"
  unfolding has_field_derivative_iff_has_vector_derivative
  by (rule bounded_bilinear.has_vector_derivative[OF bounded_bilinear_scaleR])

lemma has_vector_derivative_mult[derivative_intros]:
  "(f has_vector_derivative f') (at x within s) \<Longrightarrow> (g has_vector_derivative g') (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x * g x) has_vector_derivative (f x * g' + f' * g x)) (at x within s)"
  for f g :: "real \<Rightarrow> 'a::real_normed_algebra"
  by (rule bounded_bilinear.has_vector_derivative[OF bounded_bilinear_mult])

lemma has_vector_derivative_of_real[derivative_intros]:
  "(f has_field_derivative D) F \<Longrightarrow> ((\<lambda>x. of_real (f x)) has_vector_derivative (of_real D)) F"
  by (rule bounded_linear.has_vector_derivative[OF bounded_linear_of_real])
    (simp add: has_field_derivative_iff_has_vector_derivative)

lemma has_vector_derivative_real_field:
  "(f has_field_derivative f') (at (of_real a)) \<Longrightarrow> ((\<lambda>x. f (of_real x)) has_vector_derivative f') (at a within s)"
  using has_derivative_compose[of of_real of_real a _ f "(*) f'"] 
  by (simp add: scaleR_conv_of_real ac_simps has_vector_derivative_def has_field_derivative_def)

lemma has_vector_derivative_continuous:
  "(f has_vector_derivative D) (at x within s) \<Longrightarrow> continuous (at x within s) f"
  by (auto intro: has_derivative_continuous simp: has_vector_derivative_def)

lemma continuous_on_vector_derivative:
  "(\<And>x. x \<in> S \<Longrightarrow> (f has_vector_derivative f' x) (at x within S)) \<Longrightarrow> continuous_on S f"
  by (auto simp: continuous_on_eq_continuous_within intro!: has_vector_derivative_continuous)

lemma has_vector_derivative_mult_right[derivative_intros]:
  fixes a :: "'a::real_normed_algebra"
  shows "(f has_vector_derivative x) F \<Longrightarrow> ((\<lambda>x. a * f x) has_vector_derivative (a * x)) F"
  by (rule bounded_linear.has_vector_derivative[OF bounded_linear_mult_right])

lemma has_vector_derivative_mult_left[derivative_intros]:
  fixes a :: "'a::real_normed_algebra"
  shows "(f has_vector_derivative x) F \<Longrightarrow> ((\<lambda>x. f x * a) has_vector_derivative (x * a)) F"
  by (rule bounded_linear.has_vector_derivative[OF bounded_linear_mult_left])


subsection \<open>Derivatives\<close>

lemma DERIV_D: "DERIV f x :> D \<Longrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow> D"
  by (simp add: DERIV_def)

lemma has_field_derivativeD:
  "(f has_field_derivative D) (at x within S) \<Longrightarrow>
    ((\<lambda>y. (f y - f x) / (y - x)) \<longlongrightarrow> D) (at x within S)"
  by (simp add: has_field_derivative_iff)

lemma DERIV_const [simp, derivative_intros]: "((\<lambda>x. k) has_field_derivative 0) F"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_const]) auto

lemma DERIV_ident [simp, derivative_intros]: "((\<lambda>x. x) has_field_derivative 1) F"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_ident]) auto

lemma field_differentiable_add[derivative_intros]:
  "(f has_field_derivative f') F \<Longrightarrow> (g has_field_derivative g') F \<Longrightarrow>
    ((\<lambda>z. f z + g z) has_field_derivative f' + g') F"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_add])
     (auto simp: has_field_derivative_def field_simps mult_commute_abs)

corollary DERIV_add:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow> (g has_field_derivative E) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x + g x) has_field_derivative D + E) (at x within s)"
  by (rule field_differentiable_add)

lemma field_differentiable_minus[derivative_intros]:
  "(f has_field_derivative f') F \<Longrightarrow> ((\<lambda>z. - (f z)) has_field_derivative -f') F"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_minus])
     (auto simp: has_field_derivative_def field_simps mult_commute_abs)

corollary DERIV_minus:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    ((\<lambda>x. - f x) has_field_derivative -D) (at x within s)"
  by (rule field_differentiable_minus)

lemma field_differentiable_diff[derivative_intros]:
  "(f has_field_derivative f') F \<Longrightarrow>
    (g has_field_derivative g') F \<Longrightarrow> ((\<lambda>z. f z - g z) has_field_derivative f' - g') F"
  by (simp only: diff_conv_add_uminus field_differentiable_add field_differentiable_minus)

corollary DERIV_diff:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    (g has_field_derivative E) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_field_derivative D - E) (at x within s)"
  by (rule field_differentiable_diff)

lemma DERIV_continuous: "(f has_field_derivative D) (at x within s) \<Longrightarrow> continuous (at x within s) f"
  by (drule has_derivative_continuous[OF has_field_derivative_imp_has_derivative]) simp

corollary DERIV_isCont: "DERIV f x :> D \<Longrightarrow> isCont f x"
  by (rule DERIV_continuous)

lemma DERIV_atLeastAtMost_imp_continuous_on:
  assumes "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> \<exists>y. DERIV f x :> y"
  shows "continuous_on {a..b} f"
  by (meson DERIV_isCont assms atLeastAtMost_iff continuous_at_imp_continuous_at_within continuous_on_eq_continuous_within)

lemma DERIV_continuous_on:
  "(\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative (D x)) (at x within s)) \<Longrightarrow> continuous_on s f"
  unfolding continuous_on_eq_continuous_within
  by (intro continuous_at_imp_continuous_on ballI DERIV_continuous)

lemma DERIV_mult':
  "(f has_field_derivative D) (at x within s) \<Longrightarrow> (g has_field_derivative E) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x * g x) has_field_derivative f x * E + D * g x) (at x within s)"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_mult])
     (auto simp: field_simps mult_commute_abs dest: has_field_derivative_imp_has_derivative)

lemma DERIV_mult[derivative_intros]:
  "(f has_field_derivative Da) (at x within s) \<Longrightarrow> (g has_field_derivative Db) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x * g x) has_field_derivative Da * g x + Db * f x) (at x within s)"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_mult])
     (auto simp: field_simps dest: has_field_derivative_imp_has_derivative)

text \<open>Derivative of linear multiplication\<close>

lemma DERIV_cmult:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    ((\<lambda>x. c * f x) has_field_derivative c * D) (at x within s)"
  by (drule DERIV_mult' [OF DERIV_const]) simp

lemma DERIV_cmult_right:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x * c) has_field_derivative D * c) (at x within s)"
  using DERIV_cmult by (auto simp add: ac_simps)

lemma DERIV_cmult_Id [simp]: "((*) c has_field_derivative c) (at x within s)"
  using DERIV_ident [THEN DERIV_cmult, where c = c and x = x] by simp

lemma DERIV_cdivide:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x / c) has_field_derivative D / c) (at x within s)"
  using DERIV_cmult_right[of f D x s "1 / c"] by simp

lemma DERIV_unique: "DERIV f x :> D \<Longrightarrow> DERIV f x :> E \<Longrightarrow> D = E"
  unfolding DERIV_def by (rule LIM_unique)

lemma DERIV_Uniq: "\<exists>\<^sub>\<le>\<^sub>1D. DERIV f x :> D"
  by (simp add: DERIV_unique Uniq_def)

lemma DERIV_sum[derivative_intros]:
  "(\<And> n. n \<in> S \<Longrightarrow> ((\<lambda>x. f x n) has_field_derivative (f' x n)) F) \<Longrightarrow>
    ((\<lambda>x. sum (f x) S) has_field_derivative sum (f' x) S) F"
  by (rule has_derivative_imp_has_field_derivative [OF has_derivative_sum])
     (auto simp: sum_distrib_left mult_commute_abs dest: has_field_derivative_imp_has_derivative)

lemma DERIV_inverse'[derivative_intros]:
  assumes "(f has_field_derivative D) (at x within s)"
    and "f x \<noteq> 0"
  shows "((\<lambda>x. inverse (f x)) has_field_derivative - (inverse (f x) * D * inverse (f x)))
    (at x within s)"
proof -
  have "(f has_derivative (\<lambda>x. x * D)) = (f has_derivative (*) D)"
    by (rule arg_cong [of "\<lambda>x. x * D"]) (simp add: fun_eq_iff)
  with assms have "(f has_derivative (\<lambda>x. x * D)) (at x within s)"
    by (auto dest!: has_field_derivative_imp_has_derivative)
  then show ?thesis using \<open>f x \<noteq> 0\<close>
    by (auto intro: has_derivative_imp_has_field_derivative has_derivative_inverse)
qed

text \<open>Power of \<open>-1\<close>\<close>

lemma DERIV_inverse:
  "x \<noteq> 0 \<Longrightarrow> ((\<lambda>x. inverse(x)) has_field_derivative - (inverse x ^ Suc (Suc 0))) (at x within s)"
  by (drule DERIV_inverse' [OF DERIV_ident]) simp

text \<open>Derivative of inverse\<close>

lemma DERIV_inverse_fun:
  "(f has_field_derivative d) (at x within s) \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow>
    ((\<lambda>x. inverse (f x)) has_field_derivative (- (d * inverse(f x ^ Suc (Suc 0))))) (at x within s)"
  by (drule (1) DERIV_inverse') (simp add: ac_simps nonzero_inverse_mult_distrib)

text \<open>Derivative of quotient\<close>

lemma DERIV_divide[derivative_intros]:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    (g has_field_derivative E) (at x within s) \<Longrightarrow> g x \<noteq> 0 \<Longrightarrow>
    ((\<lambda>x. f x / g x) has_field_derivative (D * g x - f x * E) / (g x * g x)) (at x within s)"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_divide])
     (auto dest: has_field_derivative_imp_has_derivative simp: field_simps)

lemma DERIV_quotient:
  "(f has_field_derivative d) (at x within s) \<Longrightarrow>
    (g has_field_derivative e) (at x within s)\<Longrightarrow> g x \<noteq> 0 \<Longrightarrow>
    ((\<lambda>y. f y / g y) has_field_derivative (d * g x - (e * f x)) / (g x ^ Suc (Suc 0))) (at x within s)"
  by (drule (2) DERIV_divide) (simp add: mult.commute)

lemma DERIV_power_Suc:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x ^ Suc n) has_field_derivative (1 + of_nat n) * (D * f x ^ n)) (at x within s)"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_power])
     (auto simp: has_field_derivative_def)

lemma DERIV_power[derivative_intros]:
  "(f has_field_derivative D) (at x within s) \<Longrightarrow>
    ((\<lambda>x. f x ^ n) has_field_derivative of_nat n * (D * f x ^ (n - Suc 0))) (at x within s)"
  by (rule has_derivative_imp_has_field_derivative[OF has_derivative_power])
     (auto simp: has_field_derivative_def)

lemma DERIV_pow: "((\<lambda>x. x ^ n) has_field_derivative real n * (x ^ (n - Suc 0))) (at x within s)"
  using DERIV_power [OF DERIV_ident] by simp

lemma DERIV_power_int [derivative_intros]:
  assumes [derivative_intros]: "(f has_field_derivative d) (at x within s)" and [simp]: "f x \<noteq> 0"
  shows   "((\<lambda>x. power_int (f x) n) has_field_derivative
             (of_int n * power_int (f x) (n - 1) * d)) (at x within s)"
proof (cases n rule: int_cases4)
  case (nonneg n)
  thus ?thesis 
    by (cases "n = 0")
       (auto intro!: derivative_eq_intros simp: field_simps power_int_diff
             simp flip: power_Suc power_Suc2 power_add)
next
  case (neg n)
  thus ?thesis
    by (auto intro!: derivative_eq_intros simp: field_simps power_int_diff power_int_minus
             simp flip: power_Suc power_Suc2 power_add)
qed

lemma DERIV_chain': "(f has_field_derivative D) (at x within s) \<Longrightarrow> DERIV g (f x) :> E \<Longrightarrow>
  ((\<lambda>x. g (f x)) has_field_derivative E * D) (at x within s)"
  using has_derivative_compose[of f "(*) D" x s g "(*) E"]
  by (simp only: has_field_derivative_def mult_commute_abs ac_simps)

corollary DERIV_chain2: "DERIV f (g x) :> Da \<Longrightarrow> (g has_field_derivative Db) (at x within s) \<Longrightarrow>
  ((\<lambda>x. f (g x)) has_field_derivative Da * Db) (at x within s)"
  by (rule DERIV_chain')

text \<open>Standard version\<close>

lemma DERIV_chain:
  "DERIV f (g x) :> Da \<Longrightarrow> (g has_field_derivative Db) (at x within s) \<Longrightarrow>
    (f \<circ> g has_field_derivative Da * Db) (at x within s)"
  by (drule (1) DERIV_chain', simp add: o_def mult.commute)

lemma DERIV_image_chain:
  "(f has_field_derivative Da) (at (g x) within (g ` s)) \<Longrightarrow>
    (g has_field_derivative Db) (at x within s) \<Longrightarrow>
    (f \<circ> g has_field_derivative Da * Db) (at x within s)"
  using has_derivative_in_compose [of g "(*) Db" x s f "(*) Da "]
  by (simp add: has_field_derivative_def o_def mult_commute_abs ac_simps)

(*These two are from HOL Light: HAS_COMPLEX_DERIVATIVE_CHAIN*)
lemma DERIV_chain_s:
  assumes "(\<And>x. x \<in> s \<Longrightarrow> DERIV g x :> g'(x))"
    and "DERIV f x :> f'"
    and "f x \<in> s"
  shows "DERIV (\<lambda>x. g(f x)) x :> f' * g'(f x)"
  by (metis (full_types) DERIV_chain' mult.commute assms)

lemma DERIV_chain3: (*HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV*)
  assumes "(\<And>x. DERIV g x :> g'(x))"
    and "DERIV f x :> f'"
  shows "DERIV (\<lambda>x. g(f x)) x :> f' * g'(f x)"
  by (metis UNIV_I DERIV_chain_s [of UNIV] assms)

text \<open>Alternative definition for differentiability\<close>

lemma DERIV_LIM_iff:
  fixes f :: "'a::{real_normed_vector,inverse} \<Rightarrow> 'a"
  shows "((\<lambda>h. (f (a + h) - f a) / h) \<midarrow>0\<rightarrow> D) = ((\<lambda>x. (f x - f a) / (x - a)) \<midarrow>a\<rightarrow> D)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "(\<lambda>x. (f (a + (x + - a)) - f a) / (x + - a)) \<midarrow>0 - - a\<rightarrow> D"
    by (rule LIM_offset)
  then show ?rhs
    by simp
next
  assume ?rhs
  then have "(\<lambda>x. (f (x+a) - f a) / ((x+a) - a)) \<midarrow>a-a\<rightarrow> D"
    by (rule LIM_offset)
  then show ?lhs
    by (simp add: add.commute)
qed

lemma has_field_derivative_cong_ev:
  assumes "x = y"
    and *: "eventually (\<lambda>x. x \<in> S \<longrightarrow> f x = g x) (nhds x)"
    and "u = v" "S = t" "x \<in> S"
  shows "(f has_field_derivative u) (at x within S) = (g has_field_derivative v) (at y within t)"
  unfolding has_field_derivative_iff
proof (rule filterlim_cong)
  from assms have "f y = g y"
    by (auto simp: eventually_nhds)
  with * show "\<forall>\<^sub>F z in at x within S. (f z - f x) / (z - x) = (g z - g y) / (z - y)"
    unfolding eventually_at_filter
    by eventually_elim (auto simp: assms \<open>f y = g y\<close>)
qed (simp_all add: assms)

lemma has_field_derivative_cong_eventually:
  assumes "eventually (\<lambda>x. f x = g x) (at x within S)" "f x = g x"
  shows "(f has_field_derivative u) (at x within S) = (g has_field_derivative u) (at x within S)"
  unfolding has_field_derivative_iff
proof (rule tendsto_cong)
  show "\<forall>\<^sub>F y in at x within S. (f y - f x) / (y - x) = (g y - g x) / (y - x)"
    using assms by (auto elim: eventually_mono)
qed

lemma DERIV_cong_ev:
  "x = y \<Longrightarrow> eventually (\<lambda>x. f x = g x) (nhds x) \<Longrightarrow> u = v \<Longrightarrow>
    DERIV f x :> u \<longleftrightarrow> DERIV g y :> v"
  by (rule has_field_derivative_cong_ev) simp_all

lemma DERIV_mirror: "(DERIV f (- x) :> y) \<longleftrightarrow> (DERIV (\<lambda>x. f (- x)) x :> - y)"
  for f :: "real \<Rightarrow> real" and x y :: real
  by (simp add: DERIV_def filterlim_at_split filterlim_at_left_to_right
      tendsto_minus_cancel_left field_simps conj_commute)

lemma DERIV_shift:
  "(f has_field_derivative y) (at (x + z)) = ((\<lambda>x. f (x + z)) has_field_derivative y) (at x)"
  by (simp add: DERIV_def field_simps)

lemma DERIV_at_within_shift_lemma:
  assumes "(f has_field_derivative y) (at (z+x) within (+) z ` S)"
  shows "(f \<circ> (+)z has_field_derivative y) (at x within S)"
proof -
  have "((+)z has_field_derivative 1) (at x within S)"
    by (rule derivative_eq_intros | simp)+
  with assms DERIV_image_chain show ?thesis
    by (metis mult.right_neutral)
qed

lemma DERIV_at_within_shift:
  "(f has_field_derivative y) (at (z+x) within (+) z ` S) \<longleftrightarrow> 
   ((\<lambda>x. f (z+x)) has_field_derivative y) (at x within S)"   (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using DERIV_at_within_shift_lemma unfolding o_def by blast
next
  have [simp]: "(\<lambda>x. x - z) ` (+) z ` S = S"
    by force
  assume R: ?rhs
  have "(f \<circ> (+) z \<circ> (+) (- z) has_field_derivative y) (at (z + x) within (+) z ` S)"
    by (rule DERIV_at_within_shift_lemma) (use R in \<open>simp add: o_def\<close>)
  then show ?lhs
    by (simp add: o_def)
qed

lemma floor_has_real_derivative:
  fixes f :: "real \<Rightarrow> 'a::{floor_ceiling,order_topology}"
  assumes "isCont f x"
    and "f x \<notin> \<int>"
  shows "((\<lambda>x. floor (f x)) has_real_derivative 0) (at x)"
proof (subst DERIV_cong_ev[OF refl _ refl])
  show "((\<lambda>_. floor (f x)) has_real_derivative 0) (at x)"
    by simp
  have "\<forall>\<^sub>F y in at x. \<lfloor>f y\<rfloor> = \<lfloor>f x\<rfloor>"
    by (rule eventually_floor_eq[OF assms[unfolded continuous_at]])
  then show "\<forall>\<^sub>F y in nhds x. real_of_int \<lfloor>f y\<rfloor> = real_of_int \<lfloor>f x\<rfloor>"
    unfolding eventually_at_filter
    by eventually_elim auto
qed

lemmas has_derivative_floor[derivative_intros] =
  floor_has_real_derivative[THEN DERIV_compose_FDERIV]

lemma continuous_floor:
  fixes x::real
  shows "x \<notin> \<int> \<Longrightarrow> continuous (at x) (real_of_int \<circ> floor)"
  using floor_has_real_derivative [where f=id]
  by (auto simp: o_def has_field_derivative_def intro: has_derivative_continuous)

lemma continuous_frac:
  fixes x::real
  assumes "x \<notin> \<int>"
  shows "continuous (at x) frac"
proof -
  have "isCont (\<lambda>x. real_of_int \<lfloor>x\<rfloor>) x"
    using continuous_floor [OF assms] by (simp add: o_def)
  then have *: "continuous (at x) (\<lambda>x. x - real_of_int \<lfloor>x\<rfloor>)"
    by (intro continuous_intros)
  moreover have "\<forall>\<^sub>F x in nhds x. frac x = x - real_of_int \<lfloor>x\<rfloor>"
    by (simp add: frac_def)
  ultimately show ?thesis
    by (simp add: LIM_imp_LIM frac_def isCont_def)
qed

text \<open>Caratheodory formulation of derivative at a point\<close>

lemma CARAT_DERIV:
  "(DERIV f x :> l) \<longleftrightarrow> (\<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> isCont g x \<and> g x = l)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  show "\<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> isCont g x \<and> g x = l"
  proof (intro exI conjI)
    let ?g = "(\<lambda>z. if z = x then l else (f z - f x) / (z-x))"
    show "\<forall>z. f z - f x = ?g z * (z - x)"
      by simp
    show "isCont ?g x"
      using \<open>?lhs\<close> by (simp add: isCont_iff DERIV_def cong: LIM_equal [rule_format])
    show "?g x = l"
      by simp
  qed
next
  assume ?rhs
  then show ?lhs
    by (auto simp add: isCont_iff DERIV_def cong: LIM_cong)
qed


subsection \<open>Local extrema\<close>

text \<open>If \<^term>\<open>0 < f' x\<close> then \<^term>\<open>x\<close> is Locally Strictly Increasing At The Right.\<close>

lemma has_real_derivative_pos_inc_right:
  fixes f :: "real \<Rightarrow> real"
  assumes der: "(f has_real_derivative l) (at x within S)"
    and l: "0 < l"
  shows "\<exists>d > 0. \<forall>h > 0. x + h \<in> S \<longrightarrow> h < d \<longrightarrow> f x < f (x + h)"
  using assms
proof -
  from der [THEN has_field_derivativeD, THEN tendstoD, OF l, unfolded eventually_at]
  obtain s where s: "0 < s"
    and all: "\<And>xa. xa\<in>S \<Longrightarrow> xa \<noteq> x \<and> dist xa x < s \<longrightarrow> \<bar>(f xa - f x) / (xa - x) - l\<bar> < l"
    by (auto simp: dist_real_def)
  then show ?thesis
  proof (intro exI conjI strip)
    show "0 < s" by (rule s)
  next
    fix h :: real
    assume "0 < h" "h < s" "x + h \<in> S"
    with all [of "x + h"] show "f x < f (x+h)"
    proof (simp add: abs_if dist_real_def pos_less_divide_eq split: if_split_asm)
      assume "\<not> (f (x + h) - f x) / h < l" and h: "0 < h"
      with l have "0 < (f (x + h) - f x) / h"
        by arith
      then show "f x < f (x + h)"
        by (simp add: pos_less_divide_eq h)
    qed
  qed
qed

lemma DERIV_pos_inc_right:
  fixes f :: "real \<Rightarrow> real"
  assumes der: "DERIV f x :> l"
    and l: "0 < l"
  shows "\<exists>d > 0. \<forall>h > 0. h < d \<longrightarrow> f x < f (x + h)"
  using has_real_derivative_pos_inc_right[OF assms]
  by auto

lemma has_real_derivative_neg_dec_left:
  fixes f :: "real \<Rightarrow> real"
  assumes der: "(f has_real_derivative l) (at x within S)"
    and "l < 0"
  shows "\<exists>d > 0. \<forall>h > 0. x - h \<in> S \<longrightarrow> h < d \<longrightarrow> f x < f (x - h)"
proof -
  from \<open>l < 0\<close> have l: "- l > 0"
    by simp
  from der [THEN has_field_derivativeD, THEN tendstoD, OF l, unfolded eventually_at]
  obtain s where s: "0 < s"
    and all: "\<And>xa. xa\<in>S \<Longrightarrow> xa \<noteq> x \<and> dist xa x < s \<longrightarrow> \<bar>(f xa - f x) / (xa - x) - l\<bar> < - l"
    by (auto simp: dist_real_def)
  then show ?thesis
  proof (intro exI conjI strip)
    show "0 < s" by (rule s)
  next
    fix h :: real
    assume "0 < h" "h < s" "x - h \<in> S"
    with all [of "x - h"] show "f x < f (x-h)"
    proof (simp add: abs_if pos_less_divide_eq dist_real_def split: if_split_asm)
      assume "- ((f (x-h) - f x) / h) < l" and h: "0 < h"
      with l have "0 < (f (x-h) - f x) / h"
        by arith
      then show "f x < f (x - h)"
        by (simp add: pos_less_divide_eq h)
    qed
  qed
qed

lemma DERIV_neg_dec_left:
  fixes f :: "real \<Rightarrow> real"
  assumes der: "DERIV f x :> l"
    and l: "l < 0"
  shows "\<exists>d > 0. \<forall>h > 0. h < d \<longrightarrow> f x < f (x - h)"
  using has_real_derivative_neg_dec_left[OF assms]
  by auto

lemma has_real_derivative_pos_inc_left:
  fixes f :: "real \<Rightarrow> real"
  shows "(f has_real_derivative l) (at x within S) \<Longrightarrow> 0 < l \<Longrightarrow>
    \<exists>d>0. \<forall>h>0. x - h \<in> S \<longrightarrow> h < d \<longrightarrow> f (x - h) < f x"
  by (rule has_real_derivative_neg_dec_left [of "\<lambda>x. - f x" "-l" x S, simplified])
      (auto simp add: DERIV_minus)

lemma DERIV_pos_inc_left:
  fixes f :: "real \<Rightarrow> real"
  shows "DERIV f x :> l \<Longrightarrow> 0 < l \<Longrightarrow> \<exists>d > 0. \<forall>h > 0. h < d \<longrightarrow> f (x - h) < f x"
  using has_real_derivative_pos_inc_left
  by blast

lemma has_real_derivative_neg_dec_right:
  fixes f :: "real \<Rightarrow> real"
  shows "(f has_real_derivative l) (at x within S) \<Longrightarrow> l < 0 \<Longrightarrow>
    \<exists>d > 0. \<forall>h > 0. x + h \<in> S \<longrightarrow> h < d \<longrightarrow> f x > f (x + h)"
  by (rule has_real_derivative_pos_inc_right [of "\<lambda>x. - f x" "-l" x S, simplified])
      (auto simp add: DERIV_minus)

lemma DERIV_neg_dec_right:
  fixes f :: "real \<Rightarrow> real"
  shows "DERIV f x :> l \<Longrightarrow> l < 0 \<Longrightarrow> \<exists>d > 0. \<forall>h > 0. h < d \<longrightarrow> f x > f (x + h)"
  using has_real_derivative_neg_dec_right by blast

lemma DERIV_local_max:
  fixes f :: "real \<Rightarrow> real"
  assumes der: "DERIV f x :> l"
    and d: "0 < d"
    and le: "\<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> f y \<le> f x"
  shows "l = 0"
proof (cases rule: linorder_cases [of l 0])
  case equal
  then show ?thesis .
next
  case less
  from DERIV_neg_dec_left [OF der less]
  obtain d' where d': "0 < d'" and lt: "\<forall>h > 0. h < d' \<longrightarrow> f x < f (x - h)"
    by blast
  obtain e where "0 < e \<and> e < d \<and> e < d'"
    using field_lbound_gt_zero [OF d d']  ..
  with lt le [THEN spec [where x="x - e"]] show ?thesis
    by (auto simp add: abs_if)
next
  case greater
  from DERIV_pos_inc_right [OF der greater]
  obtain d' where d': "0 < d'" and lt: "\<forall>h > 0. h < d' \<longrightarrow> f x < f (x + h)"
    by blast
  obtain e where "0 < e \<and> e < d \<and> e < d'"
    using field_lbound_gt_zero [OF d d'] ..
  with lt le [THEN spec [where x="x + e"]] show ?thesis
    by (auto simp add: abs_if)
qed

text \<open>Similar theorem for a local minimum\<close>
lemma DERIV_local_min:
  fixes f :: "real \<Rightarrow> real"
  shows "DERIV f x :> l \<Longrightarrow> 0 < d \<Longrightarrow> \<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> f x \<le> f y \<Longrightarrow> l = 0"
  by (drule DERIV_minus [THEN DERIV_local_max]) auto


text\<open>In particular, if a function is locally flat\<close>
lemma DERIV_local_const:
  fixes f :: "real \<Rightarrow> real"
  shows "DERIV f x :> l \<Longrightarrow> 0 < d \<Longrightarrow> \<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> f x = f y \<Longrightarrow> l = 0"
  by (auto dest!: DERIV_local_max)


subsection \<open>Rolle's Theorem\<close>

text \<open>Lemma about introducing open ball in open interval\<close>
lemma lemma_interval_lt: 
  fixes a b x :: real
  assumes "a < x" "x < b"
  shows "\<exists>d. 0 < d \<and> (\<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> a < y \<and> y < b)"
  using linorder_linear [of "x - a" "b - x"]
proof 
  assume "x - a \<le> b - x"
  with assms show ?thesis
    by (rule_tac x = "x - a" in exI) auto
next
  assume "b - x \<le> x - a"
  with assms show ?thesis
    by (rule_tac x = "b - x" in exI) auto
qed

lemma lemma_interval: "a < x \<Longrightarrow> x < b \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b)"
  for a b x :: real
  by (force dest: lemma_interval_lt)

text \<open>Rolle's Theorem.
   If \<^term>\<open>f\<close> is defined and continuous on the closed interval
   \<open>[a,b]\<close> and differentiable on the open interval \<open>(a,b)\<close>,
   and \<^term>\<open>f a = f b\<close>,
   then there exists \<open>x0 \<in> (a,b)\<close> such that \<^term>\<open>f' x0 = 0\<close>\<close>
theorem Rolle_deriv:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and fab: "f a = f b"
    and contf: "continuous_on {a..b} f"
    and derf: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> (f has_derivative f' x) (at x)"
  shows "\<exists>z. a < z \<and> z < b \<and> f' z = (\<lambda>v. 0)"
proof -
  have le: "a \<le> b"
    using \<open>a < b\<close> by simp
    have "(a + b) / 2 \<in> {a..b}"
      using assms(1) by auto
    then have *: "{a..b} \<noteq> {}"
      by auto
  obtain x where x_max: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> f z \<le> f x" and "a \<le> x" "x \<le> b"
    using continuous_attains_sup[OF compact_Icc * contf]
    by (meson atLeastAtMost_iff)
  obtain x' where x'_min: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> f x' \<le> f z" and "a \<le> x'" "x' \<le> b"
    using continuous_attains_inf[OF compact_Icc * contf] by (meson atLeastAtMost_iff)
  consider "a < x" "x < b" | "x = a \<or> x = b"
    using \<open>a \<le> x\<close> \<open>x \<le> b\<close> by arith
  then show ?thesis
  proof cases
    case 1
    \<comment> \<open>\<^term>\<open>f\<close> attains its maximum within the interval\<close>
    then obtain l where der: "DERIV f x :> l"
      using derf differentiable_def real_differentiable_def by blast
    obtain d where d: "0 < d" and bound: "\<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
      using lemma_interval [OF 1] by blast
    then have bound': "\<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> f y \<le> f x"
      using x_max by blast
    \<comment> \<open>the derivative at a local maximum is zero\<close>
    have "l = 0"
      by (rule DERIV_local_max [OF der d bound'])
    with 1 der derf [of x] show ?thesis
      by (metis has_derivative_unique has_field_derivative_def mult_zero_left)
  next
    case 2
    then have fx: "f b = f x" by (auto simp add: fab)
    consider "a < x'" "x' < b" | "x' = a \<or> x' = b"
      using \<open>a \<le> x'\<close> \<open>x' \<le> b\<close> by arith
    then show ?thesis
    proof cases
      case 1
        \<comment> \<open>\<^term>\<open>f\<close> attains its minimum within the interval\<close>
      then obtain l where der: "DERIV f x' :> l"
        using derf differentiable_def real_differentiable_def by blast 
      from lemma_interval [OF 1]
      obtain d where d: "0<d" and bound: "\<forall>y. \<bar>x'-y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
        by blast
      then have bound': "\<forall>y. \<bar>x' - y\<bar> < d \<longrightarrow> f x' \<le> f y"
        using x'_min by blast
      have "l = 0" by (rule DERIV_local_min [OF der d bound'])
        \<comment> \<open>the derivative at a local minimum is zero\<close>
      then show ?thesis using 1 der derf [of x'] 
        by (metis has_derivative_unique has_field_derivative_def mult_zero_left)
    next
      case 2
        \<comment> \<open>\<^term>\<open>f\<close> is constant throughout the interval\<close>
      then have fx': "f b = f x'" by (auto simp: fab)
      from dense [OF \<open>a < b\<close>] obtain r where r: "a < r" "r < b" by blast
      obtain d where d: "0 < d" and bound: "\<forall>y. \<bar>r - y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
        using lemma_interval [OF r] by blast
      have eq_fb: "f z = f b" if "a \<le> z" and "z \<le> b" for z
      proof (rule order_antisym)
        show "f z \<le> f b" by (simp add: fx x_max that)
        show "f b \<le> f z" by (simp add: fx' x'_min that)
      qed
      have bound': "\<forall>y. \<bar>r - y\<bar> < d \<longrightarrow> f r = f y"
      proof (intro strip)
        fix y :: real
        assume lt: "\<bar>r - y\<bar> < d"
        then have "f y = f b" by (simp add: eq_fb bound)
        then show "f r = f y" by (simp add: eq_fb r order_less_imp_le)
      qed
      obtain l where der: "DERIV f r :> l"
        using derf differentiable_def r(1) r(2) real_differentiable_def by blast
      have "l = 0"
        by (rule DERIV_local_const [OF der d bound'])
        \<comment> \<open>the derivative of a constant function is zero\<close>
      with r der derf [of r] show ?thesis
        by (metis has_derivative_unique has_field_derivative_def mult_zero_left)
    qed
  qed
qed

corollary Rolle:
  fixes a b :: real
  assumes ab: "a < b" "f a = f b" "continuous_on {a..b} f"
    and dif [rule_format]: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> f differentiable (at x)"
  shows "\<exists>z. a < z \<and> z < b \<and> DERIV f z :> 0"
proof -
  obtain f' where f': "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> (f has_derivative f' x) (at x)"
    using dif unfolding differentiable_def by metis
  then have "\<exists>z. a < z \<and> z < b \<and> f' z = (\<lambda>v. 0)"
    by (metis Rolle_deriv [OF ab])
  then show ?thesis
    using f' has_derivative_imp_has_field_derivative by fastforce
qed

subsection \<open>Mean Value Theorem\<close>

theorem mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and contf: "continuous_on {a..b} f"
    and derf: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> (f has_derivative f' x) (at x)"
  obtains \<xi> where "a < \<xi>" "\<xi> < b" "f b - f a = (f' \<xi>) (b - a)"
proof -
  have "\<exists>x. a < x \<and> x < b \<and> (\<lambda>y. f' x y - (f b - f a) / (b - a) * y) = (\<lambda>v. 0)"
  proof (intro Rolle_deriv[OF \<open>a < b\<close>])
    fix x
    assume x: "a < x" "x < b"
    show "((\<lambda>x. f x - (f b - f a) / (b - a) * x) 
          has_derivative (\<lambda>y. f' x y - (f b - f a) / (b - a) * y)) (at x)"
      by (intro derivative_intros derf[OF x])
  qed (use assms in \<open>auto intro!: continuous_intros simp: field_simps\<close>)
  then obtain \<xi> where
    "a < \<xi>" "\<xi> < b" "(\<lambda>y. f' \<xi> y - (f b - f a) / (b - a) * y) = (\<lambda>v. 0)" 
    by metis
  then show ?thesis
    by (metis (no_types, opaque_lifting) that add.right_neutral add_diff_cancel_left' add_diff_eq \<open>a < b\<close>
                 less_irrefl nonzero_eq_divide_eq)
qed

theorem MVT:
  fixes a b :: real
  assumes lt: "a < b"
    and contf: "continuous_on {a..b} f"
    and dif: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> f differentiable (at x)"
  shows "\<exists>l z. a < z \<and> z < b \<and> DERIV f z :> l \<and> f b - f a = (b - a) * l"
proof -
  obtain f' :: "real \<Rightarrow> real \<Rightarrow> real"
    where derf: "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (f has_derivative f' x) (at x)"
    using dif unfolding differentiable_def by metis
  then obtain z where "a < z" "z < b" "f b - f a = (f' z) (b - a)"
    using mvt [OF lt contf] by blast
  then show ?thesis
    by (simp add: ac_simps)
      (metis derf dif has_derivative_unique has_field_derivative_imp_has_derivative real_differentiable_def)
qed

corollary MVT2:
  assumes "a < b" and der: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> DERIV f x :> f' x"
  shows "\<exists>z::real. a < z \<and> z < b \<and> (f b - f a = (b - a) * f' z)"
proof -
  have "\<exists>l z. a < z \<and>
           z < b \<and>
           (f has_real_derivative l) (at z) \<and>
           f b - f a = (b - a) * l"
  proof (rule MVT [OF \<open>a < b\<close>])
    show "continuous_on {a..b} f"
      by (meson DERIV_continuous atLeastAtMost_iff continuous_at_imp_continuous_on der) 
    show "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> f differentiable (at x)"
      using assms by (force dest: order_less_imp_le simp add: real_differentiable_def)
  qed
  with assms show ?thesis
    by (blast dest: DERIV_unique order_less_imp_le)
qed

lemma pos_deriv_imp_strict_mono:
  assumes "\<And>x. (f has_real_derivative f' x) (at x)"
  assumes "\<And>x. f' x > 0"
  shows   "strict_mono f"
proof (rule strict_monoI)
  fix x y :: real assume xy: "x < y"
  from assms and xy have "\<exists>z>x. z < y \<and> f y - f x = (y - x) * f' z"
    by (intro MVT2) (auto dest: connectedD_interval)
  then obtain z where z: "z > x" "z < y" "f y - f x = (y - x) * f' z" by blast
  note \<open>f y - f x = (y - x) * f' z\<close>
  also have "(y - x) * f' z > 0" using xy assms by (intro mult_pos_pos) auto
  finally show "f x < f y" by simp
qed

proposition  deriv_nonneg_imp_mono:
  assumes deriv: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes ab: "a \<le> b"
  shows "g a \<le> g b"
proof (cases "a < b")
  assume "a < b"
  from deriv have "\<And>x. \<lbrakk>x \<ge> a; x \<le> b\<rbrakk> \<Longrightarrow> (g has_real_derivative g' x) (at x)" by simp
  with MVT2[OF \<open>a < b\<close>] and deriv
    obtain \<xi> where \<xi>_ab: "\<xi> > a" "\<xi> < b" and g_ab: "g b - g a = (b - a) * g' \<xi>" by blast
  from \<xi>_ab ab nonneg have "(b - a) * g' \<xi> \<ge> 0" by simp
  with g_ab show ?thesis by simp
qed (insert ab, simp)


subsubsection \<open>A function is constant if its derivative is 0 over an interval.\<close>

lemma DERIV_isconst_end:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b" and contf: "continuous_on {a..b} f"
    and 0: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> DERIV f x :> 0"
  shows "f b = f a"
  using MVT [OF \<open>a < b\<close>] "0" DERIV_unique contf real_differentiable_def
  by (fastforce simp: algebra_simps)

lemma DERIV_isconst2:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b" and contf: "continuous_on {a..b} f" and derf: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> DERIV f x :> 0"
    and "a \<le> x" "x \<le> b"
shows "f x = f a"
proof (cases "a < x")
  case True
  have *: "continuous_on {a..x} f"
    using \<open>x \<le> b\<close> contf continuous_on_subset by fastforce
  show ?thesis
    by (rule DERIV_isconst_end [OF True *]) (use \<open>x \<le> b\<close> derf in auto)
qed (use \<open>a \<le> x\<close> in auto)

lemma DERIV_isconst3:
  fixes a b x y :: real
  assumes "a < b"
    and "x \<in> {a <..< b}"
    and "y \<in> {a <..< b}"
    and derivable: "\<And>x. x \<in> {a <..< b} \<Longrightarrow> DERIV f x :> 0"
  shows "f x = f y"
proof (cases "x = y")
  case False
  let ?a = "min x y"
  let ?b = "max x y"
  have *: "DERIV f z :> 0" if "?a \<le> z" "z \<le> ?b" for z
  proof -
    have "a < z" and "z < b"
      using that \<open>x \<in> {a <..< b}\<close> and \<open>y \<in> {a <..< b}\<close> by auto
    then have "z \<in> {a<..<b}" by auto
    then show "DERIV f z :> 0" by (rule derivable)
  qed
  have isCont: "continuous_on {?a..?b} f"
    by (meson * DERIV_continuous_on atLeastAtMost_iff has_field_derivative_at_within)
  have DERIV: "\<And>z. \<lbrakk>?a < z; z < ?b\<rbrakk> \<Longrightarrow> DERIV f z :> 0"
    using * by auto
  have "?a < ?b" using \<open>x \<noteq> y\<close> by auto
  from DERIV_isconst2[OF this isCont DERIV, of x] and DERIV_isconst2[OF this isCont DERIV, of y]
  show ?thesis by auto
qed auto

lemma DERIV_isconst_all:
  fixes f :: "real \<Rightarrow> real"
  shows "\<forall>x. DERIV f x :> 0 \<Longrightarrow> f x = f y"
  apply (rule linorder_cases [of x y])
  apply (metis DERIV_continuous DERIV_isconst_end continuous_at_imp_continuous_on)+
  done

lemma DERIV_const_ratio_const:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<noteq> b" and df: "\<And>x. DERIV f x :> k"
  shows "f b - f a = (b - a) * k"
proof (cases a b rule: linorder_cases)
  case less
  show ?thesis
    using MVT [OF less] df
    by (metis DERIV_continuous DERIV_unique continuous_at_imp_continuous_on real_differentiable_def)
next
  case greater
  have  "f a - f b = (a - b) * k"
    using MVT [OF greater] df
    by (metis DERIV_continuous DERIV_unique continuous_at_imp_continuous_on real_differentiable_def)
  then show ?thesis
    by (simp add: algebra_simps)
qed auto

lemma DERIV_const_ratio_const2:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<noteq> b" and df: "\<And>x. DERIV f x :> k"
  shows "(f b - f a) / (b - a) = k"
  using DERIV_const_ratio_const [OF assms] \<open>a \<noteq> b\<close> by auto

lemma real_average_minus_first [simp]: "(a + b) / 2 - a = (b - a) / 2"
  for a b :: real
  by simp

lemma real_average_minus_second [simp]: "(b + a) / 2 - a = (b - a) / 2"
  for a b :: real
  by simp

text \<open>Gallileo's "trick": average velocity = av. of end velocities.\<close>

lemma DERIV_const_average:
  fixes v :: "real \<Rightarrow> real"
    and a b :: real
  assumes neq: "a \<noteq> b"
    and der: "\<And>x. DERIV v x :> k"
  shows "v ((a + b) / 2) = (v a + v b) / 2"
proof (cases rule: linorder_cases [of a b])
  case equal
  with neq show ?thesis by simp
next
  case less
  have "(v b - v a) / (b - a) = k"
    by (rule DERIV_const_ratio_const2 [OF neq der])
  then have "(b - a) * ((v b - v a) / (b - a)) = (b - a) * k"
    by simp
  moreover have "(v ((a + b) / 2) - v a) / ((a + b) / 2 - a) = k"
    by (rule DERIV_const_ratio_const2 [OF _ der]) (simp add: neq)
  ultimately show ?thesis
    using neq by force
next
  case greater
  have "(v b - v a) / (b - a) = k"
    by (rule DERIV_const_ratio_const2 [OF neq der])
  then have "(b - a) * ((v b - v a) / (b - a)) = (b - a) * k"
    by simp
  moreover have " (v ((b + a) / 2) - v a) / ((b + a) / 2 - a) = k"
    by (rule DERIV_const_ratio_const2 [OF _ der]) (simp add: neq)
  ultimately show ?thesis
    using neq by (force simp add: add.commute)
qed

subsubsection\<open>A function with positive derivative is increasing\<close>
text \<open>A simple proof using the MVT, by Jeremy Avigad. And variants.\<close>
lemma DERIV_pos_imp_increasing_open:
  fixes a b :: real
    and f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>y. DERIV f x :> y \<and> y > 0)"
    and con: "continuous_on {a..b} f"
  shows "f a < f b"
proof (rule ccontr)
  assume f: "\<not> ?thesis"
  have "\<exists>l z. a < z \<and> z < b \<and> DERIV f z :> l \<and> f b - f a = (b - a) * l"
    by (rule MVT) (use assms real_differentiable_def in \<open>force+\<close>)
  then obtain l z where z: "a < z" "z < b" "DERIV f z :> l" and "f b - f a = (b - a) * l"
    by auto
  with assms f have "\<not> l > 0"
    by (metis linorder_not_le mult_le_0_iff diff_le_0_iff_le)
  with assms z show False
    by (metis DERIV_unique)
qed

lemma DERIV_pos_imp_increasing:
  fixes a b :: real and f :: "real \<Rightarrow> real"
  assumes "a < b"
    and der: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y > 0"
  shows "f a < f b"
  by (metis less_le_not_le DERIV_atLeastAtMost_imp_continuous_on DERIV_pos_imp_increasing_open [OF \<open>a < b\<close>] der)

lemma DERIV_nonneg_imp_nondecreasing:
  fixes a b :: real
    and f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y \<ge> 0"
  shows "f a \<le> f b"
proof (rule ccontr, cases "a = b")
  assume "\<not> ?thesis" and "a = b"
  then show False by auto
next
  assume *: "\<not> ?thesis"
  assume "a \<noteq> b"
  with \<open>a \<le> b\<close> have "a < b"
    by linarith
  moreover have "continuous_on {a..b} f"
    by (meson DERIV_isCont assms(2) atLeastAtMost_iff continuous_at_imp_continuous_on)
  ultimately have "\<exists>l z. a < z \<and> z < b \<and> DERIV f z :> l \<and> f b - f a = (b - a) * l"
    using assms MVT [OF \<open>a < b\<close>, of f] real_differentiable_def less_eq_real_def by blast
  then obtain l z where lz: "a < z" "z < b" "DERIV f z :> l" and **: "f b - f a = (b - a) * l"
    by auto
  with * have "a < b" "f b < f a" by auto
  with ** have "\<not> l \<ge> 0" by (auto simp add: not_le algebra_simps)
    (metis * add_le_cancel_right assms(1) less_eq_real_def mult_right_mono add_left_mono linear order_refl)
  with assms lz show False
    by (metis DERIV_unique order_less_imp_le)
qed

lemma DERIV_neg_imp_decreasing_open:
  fixes a b :: real
    and f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y < 0"
    and con: "continuous_on {a..b} f"
  shows "f a > f b"
proof -
  have "(\<lambda>x. -f x) a < (\<lambda>x. -f x) b"
  proof (rule DERIV_pos_imp_increasing_open [of a b])
    show "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> \<exists>y. ((\<lambda>x. - f x) has_real_derivative y) (at x) \<and> 0 < y"
      using assms
      by simp (metis field_differentiable_minus neg_0_less_iff_less)
    show "continuous_on {a..b} (\<lambda>x. - f x)"
      using con continuous_on_minus by blast
  qed (use assms in auto)
  then show ?thesis
    by simp
qed

lemma DERIV_neg_imp_decreasing:
  fixes a b :: real and f :: "real \<Rightarrow> real"
  assumes "a < b"
    and der: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y < 0"
  shows "f a > f b"
  by (metis less_le_not_le DERIV_atLeastAtMost_imp_continuous_on DERIV_neg_imp_decreasing_open [OF \<open>a < b\<close>] der)

lemma DERIV_nonpos_imp_nonincreasing:
  fixes a b :: real
    and f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y \<le> 0"
  shows "f a \<ge> f b"
proof -
  have "(\<lambda>x. -f x) a \<le> (\<lambda>x. -f x) b"
    using DERIV_nonneg_imp_nondecreasing [of a b "\<lambda>x. -f x"] assms DERIV_minus by fastforce
  then show ?thesis
    by simp
qed

lemma DERIV_pos_imp_increasing_at_bot:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<And>x. x \<le> b \<Longrightarrow> (\<exists>y. DERIV f x :> y \<and> y > 0)"
    and lim: "(f \<longlongrightarrow> flim) at_bot"
  shows "flim < f b"
proof -
  have "\<exists>N. \<forall>n\<le>N. f n \<le> f (b - 1)"
    by (rule_tac x="b - 2" in exI) (force intro: order.strict_implies_order DERIV_pos_imp_increasing assms)
  then have "flim \<le> f (b - 1)"
     by (auto simp: eventually_at_bot_linorder tendsto_upperbound [OF lim])
  also have "\<dots> < f b"
    by (force intro: DERIV_pos_imp_increasing [where f=f] assms)
  finally show ?thesis .
qed

lemma DERIV_neg_imp_decreasing_at_top:
  fixes f :: "real \<Rightarrow> real"
  assumes der: "\<And>x. x \<ge> b \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y < 0"
    and lim: "(f \<longlongrightarrow> flim) at_top"
  shows "flim < f b"
  apply (rule DERIV_pos_imp_increasing_at_bot [where f = "\<lambda>i. f (-i)" and b = "-b", simplified])
   apply (metis DERIV_mirror der le_minus_iff neg_0_less_iff_less)
  apply (metis filterlim_at_top_mirror lim)
  done

text \<open>Derivative of inverse function\<close>

lemma DERIV_inverse_function:
  fixes f g :: "real \<Rightarrow> real"
  assumes der: "DERIV f (g x) :> D"
    and neq: "D \<noteq> 0"
    and x: "a < x" "x < b"
    and inj: "\<And>y. \<lbrakk>a < y; y < b\<rbrakk> \<Longrightarrow> f (g y) = y"
    and cont: "isCont g x"
  shows "DERIV g x :> inverse D"
unfolding has_field_derivative_iff
proof (rule LIM_equal2)
  show "0 < min (x - a) (b - x)"
    using x by arith
next
  fix y
  assume "norm (y - x) < min (x - a) (b - x)"
  then have "a < y" and "y < b"
    by (simp_all add: abs_less_iff)
  then show "(g y - g x) / (y - x) = inverse ((f (g y) - x) / (g y - g x))"
    by (simp add: inj)
next
  have "(\<lambda>z. (f z - f (g x)) / (z - g x)) \<midarrow>g x\<rightarrow> D"
    by (rule der [unfolded has_field_derivative_iff])
  then have 1: "(\<lambda>z. (f z - x) / (z - g x)) \<midarrow>g x\<rightarrow> D"
    using inj x by simp
  have 2: "\<exists>d>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> g y \<noteq> g x"
  proof (rule exI, safe)
    show "0 < min (x - a) (b - x)"
      using x by simp
  next
    fix y
    assume "norm (y - x) < min (x - a) (b - x)"
    then have y: "a < y" "y < b"
      by (simp_all add: abs_less_iff)
    assume "g y = g x"
    then have "f (g y) = f (g x)" by simp
    then have "y = x" using inj y x by simp
    also assume "y \<noteq> x"
    finally show False by simp
  qed
  have "(\<lambda>y. (f (g y) - x) / (g y - g x)) \<midarrow>x\<rightarrow> D"
    using cont 1 2 by (rule isCont_LIM_compose2)
  then show "(\<lambda>y. inverse ((f (g y) - x) / (g y - g x))) \<midarrow>x\<rightarrow> inverse D"
    using neq by (rule tendsto_inverse)
qed

subsection \<open>Generalized Mean Value Theorem\<close>

theorem GMVT:
  fixes a b :: real
  assumes alb: "a < b"
    and fc: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x"
    and fd: "\<forall>x. a < x \<and> x < b \<longrightarrow> f differentiable (at x)"
    and gc: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont g x"
    and gd: "\<forall>x. a < x \<and> x < b \<longrightarrow> g differentiable (at x)"
  shows "\<exists>g'c f'c c.
    DERIV g c :> g'c \<and> DERIV f c :> f'c \<and> a < c \<and> c < b \<and> (f b - f a) * g'c = (g b - g a) * f'c"
proof -
  let ?h = "\<lambda>x. (f b - f a) * g x - (g b - g a) * f x"
  have "\<exists>l z. a < z \<and> z < b \<and> DERIV ?h z :> l \<and> ?h b - ?h a = (b - a) * l"
  proof (rule MVT)
    from assms show "a < b" by simp
    show "continuous_on {a..b} ?h"
      by (simp add: continuous_at_imp_continuous_on fc gc)
    show "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> ?h differentiable (at x)"
      using fd gd by simp
  qed
  then obtain l where l: "\<exists>z. a < z \<and> z < b \<and> DERIV ?h z :> l \<and> ?h b - ?h a = (b - a) * l" ..
  then obtain c where c: "a < c \<and> c < b \<and> DERIV ?h c :> l \<and> ?h b - ?h a = (b - a) * l" ..

  from c have cint: "a < c \<and> c < b" by auto
  then obtain g'c where g'c: "DERIV g c :> g'c"
    using gd real_differentiable_def by blast 
  from c have "a < c \<and> c < b" by auto
  then obtain f'c where f'c: "DERIV f c :> f'c"
    using fd real_differentiable_def by blast 

  from c have "DERIV ?h c :> l" by auto
  moreover have "DERIV ?h c :>  g'c * (f b - f a) - f'c * (g b - g a)"
    using g'c f'c by (auto intro!: derivative_eq_intros)
  ultimately have leq: "l =  g'c * (f b - f a) - f'c * (g b - g a)" by (rule DERIV_unique)

  have "?h b - ?h a = (b - a) * (g'c * (f b - f a) - f'c * (g b - g a))"
  proof -
    from c have "?h b - ?h a = (b - a) * l" by auto
    also from leq have "\<dots> = (b - a) * (g'c * (f b - f a) - f'c * (g b - g a))" by simp
    finally show ?thesis by simp
  qed
  moreover have "?h b - ?h a = 0"
  proof -
    have "?h b - ?h a =
      ((f b)*(g b) - (f a)*(g b) - (g b)*(f b) + (g a)*(f b)) -
      ((f b)*(g a) - (f a)*(g a) - (g b)*(f a) + (g a)*(f a))"
      by (simp add: algebra_simps)
    then show ?thesis  by auto
  qed
  ultimately have "(b - a) * (g'c * (f b - f a) - f'c * (g b - g a)) = 0" by auto
  with alb have "g'c * (f b - f a) - f'c * (g b - g a) = 0" by simp
  then have "g'c * (f b - f a) = f'c * (g b - g a)" by simp
  then have "(f b - f a) * g'c = (g b - g a) * f'c" by (simp add: ac_simps)
  with g'c f'c cint show ?thesis by auto
qed

lemma GMVT':
  fixes f g :: "real \<Rightarrow> real"
  assumes "a < b"
    and isCont_f: "\<And>z. a \<le> z \<Longrightarrow> z \<le> b \<Longrightarrow> isCont f z"
    and isCont_g: "\<And>z. a \<le> z \<Longrightarrow> z \<le> b \<Longrightarrow> isCont g z"
    and DERIV_g: "\<And>z. a < z \<Longrightarrow> z < b \<Longrightarrow> DERIV g z :> (g' z)"
    and DERIV_f: "\<And>z. a < z \<Longrightarrow> z < b \<Longrightarrow> DERIV f z :> (f' z)"
  shows "\<exists>c. a < c \<and> c < b \<and> (f b - f a) * g' c = (g b - g a) * f' c"
proof -
  have "\<exists>g'c f'c c. DERIV g c :> g'c \<and> DERIV f c :> f'c \<and>
      a < c \<and> c < b \<and> (f b - f a) * g'c = (g b - g a) * f'c"
    using assms by (intro GMVT) (force simp: real_differentiable_def)+
  then obtain c where "a < c" "c < b" "(f b - f a) * g' c = (g b - g a) * f' c"
    using DERIV_f DERIV_g by (force dest: DERIV_unique)
  then show ?thesis
    by auto
qed


subsection \<open>L'Hopitals rule\<close>

lemma isCont_If_ge:
  fixes a :: "'a :: linorder_topology"
  assumes "continuous (at_left a) g" and f: "(f \<longlongrightarrow> g a) (at_right a)"
  shows "isCont (\<lambda>x. if x \<le> a then g x else f x) a" (is "isCont ?gf a")
proof -
  have g: "(g \<longlongrightarrow> g a) (at_left a)"
    using assms continuous_within by blast
  show ?thesis
    unfolding isCont_def continuous_within
  proof (intro filterlim_split_at; simp)
    show "(?gf \<longlongrightarrow> g a) (at_left a)"
      by (subst filterlim_cong[OF refl refl, where g=g]) (simp_all add: eventually_at_filter less_le g)
    show "(?gf \<longlongrightarrow> g a) (at_right a)"
      by (subst filterlim_cong[OF refl refl, where g=f]) (simp_all add: eventually_at_filter less_le f)
  qed
qed

lemma lhopital_right_0:
  fixes f0 g0 :: "real \<Rightarrow> real"
  assumes f_0: "(f0 \<longlongrightarrow> 0) (at_right 0)"
    and g_0: "(g0 \<longlongrightarrow> 0) (at_right 0)"
    and ev:
      "eventually (\<lambda>x. g0 x \<noteq> 0) (at_right 0)"
      "eventually (\<lambda>x. g' x \<noteq> 0) (at_right 0)"
      "eventually (\<lambda>x. DERIV f0 x :> f' x) (at_right 0)"
      "eventually (\<lambda>x. DERIV g0 x :> g' x) (at_right 0)"
    and lim: "filterlim (\<lambda> x. (f' x / g' x)) F (at_right 0)"
  shows "filterlim (\<lambda> x. f0 x / g0 x) F (at_right 0)"
proof -
  define f where [abs_def]: "f x = (if x \<le> 0 then 0 else f0 x)" for x
  then have "f 0 = 0" by simp

  define g where [abs_def]: "g x = (if x \<le> 0 then 0 else g0 x)" for x
  then have "g 0 = 0" by simp

  have "eventually (\<lambda>x. g0 x \<noteq> 0 \<and> g' x \<noteq> 0 \<and>
      DERIV f0 x :> (f' x) \<and> DERIV g0 x :> (g' x)) (at_right 0)"
    using ev by eventually_elim auto
  then obtain a where [arith]: "0 < a"
    and g0_neq_0: "\<And>x. 0 < x \<Longrightarrow> x < a \<Longrightarrow> g0 x \<noteq> 0"
    and g'_neq_0: "\<And>x. 0 < x \<Longrightarrow> x < a \<Longrightarrow> g' x \<noteq> 0"
    and f0: "\<And>x. 0 < x \<Longrightarrow> x < a \<Longrightarrow> DERIV f0 x :> (f' x)"
    and g0: "\<And>x. 0 < x \<Longrightarrow> x < a \<Longrightarrow> DERIV g0 x :> (g' x)"
    unfolding eventually_at by (auto simp: dist_real_def)

  have g_neq_0: "\<And>x. 0 < x \<Longrightarrow> x < a \<Longrightarrow> g x \<noteq> 0"
    using g0_neq_0 by (simp add: g_def)

  have f: "DERIV f x :> (f' x)" if x: "0 < x" "x < a" for x
    using that
    by (intro DERIV_cong_ev[THEN iffD1, OF _ _ _ f0[OF x]])
      (auto simp: f_def eventually_nhds_metric dist_real_def intro!: exI[of _ x])

  have g: "DERIV g x :> (g' x)" if x: "0 < x" "x < a" for x
    using that
    by (intro DERIV_cong_ev[THEN iffD1, OF _ _ _ g0[OF x]])
         (auto simp: g_def eventually_nhds_metric dist_real_def intro!: exI[of _ x])

  have "isCont f 0"
    unfolding f_def by (intro isCont_If_ge f_0 continuous_const)

  have "isCont g 0"
    unfolding g_def by (intro isCont_If_ge g_0 continuous_const)

  have "\<exists>\<zeta>. \<forall>x\<in>{0 <..< a}. 0 < \<zeta> x \<and> \<zeta> x < x \<and> f x / g x = f' (\<zeta> x) / g' (\<zeta> x)"
  proof (rule bchoice, rule ballI)
    fix x
    assume "x \<in> {0 <..< a}"
    then have x[arith]: "0 < x" "x < a" by auto
    with g'_neq_0 g_neq_0 \<open>g 0 = 0\<close> have g': "\<And>x. 0 < x \<Longrightarrow> x < a  \<Longrightarrow> 0 \<noteq> g' x" "g 0 \<noteq> g x"
      by auto
    have "\<And>x. 0 \<le> x \<Longrightarrow> x < a \<Longrightarrow> isCont f x"
      using \<open>isCont f 0\<close> f by (auto intro: DERIV_isCont simp: le_less)
    moreover have "\<And>x. 0 \<le> x \<Longrightarrow> x < a \<Longrightarrow> isCont g x"
      using \<open>isCont g 0\<close> g by (auto intro: DERIV_isCont simp: le_less)
    ultimately have "\<exists>c. 0 < c \<and> c < x \<and> (f x - f 0) * g' c = (g x - g 0) * f' c"
      using f g \<open>x < a\<close> by (intro GMVT') auto
    then obtain c where *: "0 < c" "c < x" "(f x - f 0) * g' c = (g x - g 0) * f' c"
      by blast
    moreover
    from * g'(1)[of c] g'(2) have "(f x - f 0)  / (g x - g 0) = f' c / g' c"
      by (simp add: field_simps)
    ultimately show "\<exists>y. 0 < y \<and> y < x \<and> f x / g x = f' y / g' y"
      using \<open>f 0 = 0\<close> \<open>g 0 = 0\<close> by (auto intro!: exI[of _ c])
  qed
  then obtain \<zeta> where "\<forall>x\<in>{0 <..< a}. 0 < \<zeta> x \<and> \<zeta> x < x \<and> f x / g x = f' (\<zeta> x) / g' (\<zeta> x)" ..
  then have \<zeta>: "eventually (\<lambda>x. 0 < \<zeta> x \<and> \<zeta> x < x \<and> f x / g x = f' (\<zeta> x) / g' (\<zeta> x)) (at_right 0)"
    unfolding eventually_at by (intro exI[of _ a]) (auto simp: dist_real_def)
  moreover
  from \<zeta> have "eventually (\<lambda>x. norm (\<zeta> x) \<le> x) (at_right 0)"
    by eventually_elim auto
  then have "((\<lambda>x. norm (\<zeta> x)) \<longlongrightarrow> 0) (at_right 0)"
    by (rule_tac real_tendsto_sandwich[where f="\<lambda>x. 0" and h="\<lambda>x. x"]) auto
  then have "(\<zeta> \<longlongrightarrow> 0) (at_right 0)"
    by (rule tendsto_norm_zero_cancel)
  with \<zeta> have "filterlim \<zeta> (at_right 0) (at_right 0)"
    by (auto elim!: eventually_mono simp: filterlim_at)
  from this lim have "filterlim (\<lambda>t. f' (\<zeta> t) / g' (\<zeta> t)) F (at_right 0)"
    by (rule_tac filterlim_compose[of _ _ _ \<zeta>])
  ultimately have "filterlim (\<lambda>t. f t / g t) F (at_right 0)" (is ?P)
    by (rule_tac filterlim_cong[THEN iffD1, OF refl refl])
       (auto elim: eventually_mono)
  also have "?P \<longleftrightarrow> ?thesis"
    by (rule filterlim_cong) (auto simp: f_def g_def eventually_at_filter)
  finally show ?thesis .
qed

lemma lhopital_right:
  "(f \<longlongrightarrow> 0) (at_right x) \<Longrightarrow> (g \<longlongrightarrow> 0) (at_right x) \<Longrightarrow>
    eventually (\<lambda>x. g x \<noteq> 0) (at_right x) \<Longrightarrow>
    eventually (\<lambda>x. g' x \<noteq> 0) (at_right x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV f x :> f' x) (at_right x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV g x :> g' x) (at_right x) \<Longrightarrow>
    filterlim (\<lambda> x. (f' x / g' x)) F (at_right x) \<Longrightarrow>
  filterlim (\<lambda> x. f x / g x) F (at_right x)"
  for x :: real
  unfolding eventually_at_right_to_0[of _ x] filterlim_at_right_to_0[of _ _ x] DERIV_shift
  by (rule lhopital_right_0)

lemma lhopital_left:
  "(f \<longlongrightarrow> 0) (at_left x) \<Longrightarrow> (g \<longlongrightarrow> 0) (at_left x) \<Longrightarrow>
    eventually (\<lambda>x. g x \<noteq> 0) (at_left x) \<Longrightarrow>
    eventually (\<lambda>x. g' x \<noteq> 0) (at_left x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV f x :> f' x) (at_left x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV g x :> g' x) (at_left x) \<Longrightarrow>
    filterlim (\<lambda> x. (f' x / g' x)) F (at_left x) \<Longrightarrow>
  filterlim (\<lambda> x. f x / g x) F (at_left x)"
  for x :: real
  unfolding eventually_at_left_to_right filterlim_at_left_to_right DERIV_mirror
  by (rule lhopital_right[where f'="\<lambda>x. - f' (- x)"]) (auto simp: DERIV_mirror)

lemma lhopital:
  "(f \<longlongrightarrow> 0) (at x) \<Longrightarrow> (g \<longlongrightarrow> 0) (at x) \<Longrightarrow>
    eventually (\<lambda>x. g x \<noteq> 0) (at x) \<Longrightarrow>
    eventually (\<lambda>x. g' x \<noteq> 0) (at x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV f x :> f' x) (at x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV g x :> g' x) (at x) \<Longrightarrow>
    filterlim (\<lambda> x. (f' x / g' x)) F (at x) \<Longrightarrow>
  filterlim (\<lambda> x. f x / g x) F (at x)"
  for x :: real
  unfolding eventually_at_split filterlim_at_split
  by (auto intro!: lhopital_right[of f x g g' f'] lhopital_left[of f x g g' f'])


lemma lhopital_right_0_at_top:
  fixes f g :: "real \<Rightarrow> real"
  assumes g_0: "LIM x at_right 0. g x :> at_top"
    and ev:
      "eventually (\<lambda>x. g' x \<noteq> 0) (at_right 0)"
      "eventually (\<lambda>x. DERIV f x :> f' x) (at_right 0)"
      "eventually (\<lambda>x. DERIV g x :> g' x) (at_right 0)"
    and lim: "((\<lambda> x. (f' x / g' x)) \<longlongrightarrow> x) (at_right 0)"
  shows "((\<lambda> x. f x / g x) \<longlongrightarrow> x) (at_right 0)"
  unfolding tendsto_iff
proof safe
  fix e :: real
  assume "0 < e"
  with lim[unfolded tendsto_iff, rule_format, of "e / 4"]
  have "eventually (\<lambda>t. dist (f' t / g' t) x < e / 4) (at_right 0)"
    by simp
  from eventually_conj[OF eventually_conj[OF ev(1) ev(2)] eventually_conj[OF ev(3) this]]
  obtain a where [arith]: "0 < a"
    and g'_neq_0: "\<And>x. 0 < x \<Longrightarrow> x < a \<Longrightarrow> g' x \<noteq> 0"
    and f0: "\<And>x. 0 < x \<Longrightarrow> x \<le> a \<Longrightarrow> DERIV f x :> (f' x)"
    and g0: "\<And>x. 0 < x \<Longrightarrow> x \<le> a \<Longrightarrow> DERIV g x :> (g' x)"
    and Df: "\<And>t. 0 < t \<Longrightarrow> t < a \<Longrightarrow> dist (f' t / g' t) x < e / 4"
    unfolding eventually_at_le by (auto simp: dist_real_def)

  from Df have "eventually (\<lambda>t. t < a) (at_right 0)" "eventually (\<lambda>t::real. 0 < t) (at_right 0)"
    unfolding eventually_at by (auto intro!: exI[of _ a] simp: dist_real_def)

  moreover
  have "eventually (\<lambda>t. 0 < g t) (at_right 0)" "eventually (\<lambda>t. g a < g t) (at_right 0)"
    using g_0 by (auto elim: eventually_mono simp: filterlim_at_top_dense)

  moreover
  have inv_g: "((\<lambda>x. inverse (g x)) \<longlongrightarrow> 0) (at_right 0)"
    using tendsto_inverse_0 filterlim_mono[OF g_0 at_top_le_at_infinity order_refl]
    by (rule filterlim_compose)
  then have "((\<lambda>x. norm (1 - g a * inverse (g x))) \<longlongrightarrow> norm (1 - g a * 0)) (at_right 0)"
    by (intro tendsto_intros)
  then have "((\<lambda>x. norm (1 - g a / g x)) \<longlongrightarrow> 1) (at_right 0)"
    by (simp add: inverse_eq_divide)
  from this[unfolded tendsto_iff, rule_format, of 1]
  have "eventually (\<lambda>x. norm (1 - g a / g x) < 2) (at_right 0)"
    by (auto elim!: eventually_mono simp: dist_real_def)

  moreover
  from inv_g have "((\<lambda>t. norm ((f a - x * g a) * inverse (g t))) \<longlongrightarrow> norm ((f a - x * g a) * 0))
      (at_right 0)"
    by (intro tendsto_intros)
  then have "((\<lambda>t. norm (f a - x * g a) / norm (g t)) \<longlongrightarrow> 0) (at_right 0)"
    by (simp add: inverse_eq_divide)
  from this[unfolded tendsto_iff, rule_format, of "e / 2"] \<open>0 < e\<close>
  have "eventually (\<lambda>t. norm (f a - x * g a) / norm (g t) < e / 2) (at_right 0)"
    by (auto simp: dist_real_def)

  ultimately show "eventually (\<lambda>t. dist (f t / g t) x < e) (at_right 0)"
  proof eventually_elim
    fix t assume t[arith]: "0 < t" "t < a" "g a < g t" "0 < g t"
    assume ineq: "norm (1 - g a / g t) < 2" "norm (f a - x * g a) / norm (g t) < e / 2"

    have "\<exists>y. t < y \<and> y < a \<and> (g a - g t) * f' y = (f a - f t) * g' y"
      using f0 g0 t(1,2) by (intro GMVT') (force intro!: DERIV_isCont)+
    then obtain y where [arith]: "t < y" "y < a"
      and D_eq0: "(g a - g t) * f' y = (f a - f t) * g' y"
      by blast
    from D_eq0 have D_eq: "(f t - f a) / (g t - g a) = f' y / g' y"
      using \<open>g a < g t\<close> g'_neq_0[of y] by (auto simp add: field_simps)

    have *: "f t / g t - x = ((f t - f a) / (g t - g a) - x) * (1 - g a / g t) + (f a - x * g a) / g t"
      by (simp add: field_simps)
    have "norm (f t / g t - x) \<le>
        norm (((f t - f a) / (g t - g a) - x) * (1 - g a / g t)) + norm ((f a - x * g a) / g t)"
      unfolding * by (rule norm_triangle_ineq)
    also have "\<dots> = dist (f' y / g' y) x * norm (1 - g a / g t) + norm (f a - x * g a) / norm (g t)"
      by (simp add: abs_mult D_eq dist_real_def)
    also have "\<dots> < (e / 4) * 2 + e / 2"
      using ineq Df[of y] \<open>0 < e\<close> by (intro add_le_less_mono mult_mono) auto
    finally show "dist (f t / g t) x < e"
      by (simp add: dist_real_def)
  qed
qed

lemma lhopital_right_at_top:
  "LIM x at_right x. (g::real \<Rightarrow> real) x :> at_top \<Longrightarrow>
    eventually (\<lambda>x. g' x \<noteq> 0) (at_right x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV f x :> f' x) (at_right x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV g x :> g' x) (at_right x) \<Longrightarrow>
    ((\<lambda> x. (f' x / g' x)) \<longlongrightarrow> y) (at_right x) \<Longrightarrow>
    ((\<lambda> x. f x / g x) \<longlongrightarrow> y) (at_right x)"
  unfolding eventually_at_right_to_0[of _ x] filterlim_at_right_to_0[of _ _ x] DERIV_shift
  by (rule lhopital_right_0_at_top)

lemma lhopital_left_at_top:
  "LIM x at_left x. g x :> at_top \<Longrightarrow>
    eventually (\<lambda>x. g' x \<noteq> 0) (at_left x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV f x :> f' x) (at_left x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV g x :> g' x) (at_left x) \<Longrightarrow>
    ((\<lambda> x. (f' x / g' x)) \<longlongrightarrow> y) (at_left x) \<Longrightarrow>
    ((\<lambda> x. f x / g x) \<longlongrightarrow> y) (at_left x)"
  for x :: real
  unfolding eventually_at_left_to_right filterlim_at_left_to_right DERIV_mirror
  by (rule lhopital_right_at_top[where f'="\<lambda>x. - f' (- x)"]) (auto simp: DERIV_mirror)

lemma lhopital_at_top:
  "LIM x at x. (g::real \<Rightarrow> real) x :> at_top \<Longrightarrow>
    eventually (\<lambda>x. g' x \<noteq> 0) (at x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV f x :> f' x) (at x) \<Longrightarrow>
    eventually (\<lambda>x. DERIV g x :> g' x) (at x) \<Longrightarrow>
    ((\<lambda> x. (f' x / g' x)) \<longlongrightarrow> y) (at x) \<Longrightarrow>
    ((\<lambda> x. f x / g x) \<longlongrightarrow> y) (at x)"
  unfolding eventually_at_split filterlim_at_split
  by (auto intro!: lhopital_right_at_top[of g x g' f f'] lhopital_left_at_top[of g x g' f f'])

lemma lhospital_at_top_at_top:
  fixes f g :: "real \<Rightarrow> real"
  assumes g_0: "LIM x at_top. g x :> at_top"
    and g': "eventually (\<lambda>x. g' x \<noteq> 0) at_top"
    and Df: "eventually (\<lambda>x. DERIV f x :> f' x) at_top"
    and Dg: "eventually (\<lambda>x. DERIV g x :> g' x) at_top"
    and lim: "((\<lambda> x. (f' x / g' x)) \<longlongrightarrow> x) at_top"
  shows "((\<lambda> x. f x / g x) \<longlongrightarrow> x) at_top"
  unfolding filterlim_at_top_to_right
proof (rule lhopital_right_0_at_top)
  let ?F = "\<lambda>x. f (inverse x)"
  let ?G = "\<lambda>x. g (inverse x)"
  let ?R = "at_right (0::real)"
  let ?D = "\<lambda>f' x. f' (inverse x) * - (inverse x ^ Suc (Suc 0))"
  show "LIM x ?R. ?G x :> at_top"
    using g_0 unfolding filterlim_at_top_to_right .
  show "eventually (\<lambda>x. DERIV ?G x  :> ?D g' x) ?R"
    unfolding eventually_at_right_to_top
    using Dg eventually_ge_at_top[where c=1]
    by eventually_elim (rule derivative_eq_intros DERIV_chain'[where f=inverse] | simp)+
  show "eventually (\<lambda>x. DERIV ?F x  :> ?D f' x) ?R"
    unfolding eventually_at_right_to_top
    using Df eventually_ge_at_top[where c=1]
    by eventually_elim (rule derivative_eq_intros DERIV_chain'[where f=inverse] | simp)+
  show "eventually (\<lambda>x. ?D g' x \<noteq> 0) ?R"
    unfolding eventually_at_right_to_top
    using g' eventually_ge_at_top[where c=1]
    by eventually_elim auto
  show "((\<lambda>x. ?D f' x / ?D g' x) \<longlongrightarrow> x) ?R"
    unfolding filterlim_at_right_to_top
    apply (intro filterlim_cong[THEN iffD2, OF refl refl _ lim])
    using eventually_ge_at_top[where c=1]
    by eventually_elim simp
qed

lemma lhopital_right_at_top_at_top:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_0: "LIM x at_right a. f x :> at_top"
  assumes g_0: "LIM x at_right a. g x :> at_top"
    and ev:
      "eventually (\<lambda>x. DERIV f x :> f' x) (at_right a)"
      "eventually (\<lambda>x. DERIV g x :> g' x) (at_right a)"
    and lim: "filterlim (\<lambda> x. (f' x / g' x)) at_top (at_right a)"
  shows "filterlim (\<lambda> x. f x / g x) at_top (at_right a)"
proof -
  from lim have pos: "eventually (\<lambda>x. f' x / g' x > 0) (at_right a)"
    unfolding filterlim_at_top_dense by blast
  have "((\<lambda>x. g x / f x) \<longlongrightarrow> 0) (at_right a)"
  proof (rule lhopital_right_at_top)
    from pos show "eventually (\<lambda>x. f' x \<noteq> 0) (at_right a)" by eventually_elim auto
    from tendsto_inverse_0_at_top[OF lim]
      show "((\<lambda>x. g' x / f' x) \<longlongrightarrow> 0) (at_right a)" by simp
  qed fact+
  moreover from f_0 g_0 
    have "eventually (\<lambda>x. f x > 0) (at_right a)" "eventually (\<lambda>x. g x > 0) (at_right a)"
    unfolding filterlim_at_top_dense by blast+
  hence "eventually (\<lambda>x. g x / f x > 0) (at_right a)" by eventually_elim simp
  ultimately have "filterlim (\<lambda>x. inverse (g x / f x)) at_top (at_right a)"
    by (rule filterlim_inverse_at_top)
  thus ?thesis by simp
qed

lemma lhopital_right_at_top_at_bot:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_0: "LIM x at_right a. f x :> at_top"
  assumes g_0: "LIM x at_right a. g x :> at_bot"
    and ev:
      "eventually (\<lambda>x. DERIV f x :> f' x) (at_right a)"
      "eventually (\<lambda>x. DERIV g x :> g' x) (at_right a)"
    and lim: "filterlim (\<lambda> x. (f' x / g' x)) at_bot (at_right a)"
  shows "filterlim (\<lambda> x. f x / g x) at_bot (at_right a)"
proof -
  from ev(2) have ev': "eventually (\<lambda>x. DERIV (\<lambda>x. -g x) x :> -g' x) (at_right a)"
    by eventually_elim (auto intro: derivative_intros)
  have "filterlim (\<lambda>x. f x / (-g x)) at_top (at_right a)"
    by (rule lhopital_right_at_top_at_top[where f' = f' and g' = "\<lambda>x. -g' x"])
       (insert assms ev', auto simp: filterlim_uminus_at_bot)
  hence "filterlim (\<lambda>x. -(f x / g x)) at_top (at_right a)" by simp
  thus ?thesis by (simp add: filterlim_uminus_at_bot)
qed

lemma lhopital_left_at_top_at_top:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_0: "LIM x at_left a. f x :> at_top"
  assumes g_0: "LIM x at_left a. g x :> at_top"
    and ev:
      "eventually (\<lambda>x. DERIV f x :> f' x) (at_left a)"
      "eventually (\<lambda>x. DERIV g x :> g' x) (at_left a)"
    and lim: "filterlim (\<lambda> x. (f' x / g' x)) at_top (at_left a)"
  shows "filterlim (\<lambda> x. f x / g x) at_top (at_left a)"
  by (insert assms, unfold eventually_at_left_to_right filterlim_at_left_to_right DERIV_mirror,
      rule lhopital_right_at_top_at_top[where f'="\<lambda>x. - f' (- x)"]) 
     (insert assms, auto simp: DERIV_mirror)

lemma lhopital_left_at_top_at_bot:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_0: "LIM x at_left a. f x :> at_top"
  assumes g_0: "LIM x at_left a. g x :> at_bot"
    and ev:
      "eventually (\<lambda>x. DERIV f x :> f' x) (at_left a)"
      "eventually (\<lambda>x. DERIV g x :> g' x) (at_left a)"
    and lim: "filterlim (\<lambda> x. (f' x / g' x)) at_bot (at_left a)"
  shows "filterlim (\<lambda> x. f x / g x) at_bot (at_left a)"
  by (insert assms, unfold eventually_at_left_to_right filterlim_at_left_to_right DERIV_mirror,
      rule lhopital_right_at_top_at_bot[where f'="\<lambda>x. - f' (- x)"]) 
     (insert assms, auto simp: DERIV_mirror)

lemma lhopital_at_top_at_top:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_0: "LIM x at a. f x :> at_top"
  assumes g_0: "LIM x at a. g x :> at_top"
    and ev:
      "eventually (\<lambda>x. DERIV f x :> f' x) (at a)"
      "eventually (\<lambda>x. DERIV g x :> g' x) (at a)"
    and lim: "filterlim (\<lambda> x. (f' x / g' x)) at_top (at a)"
  shows "filterlim (\<lambda> x. f x / g x) at_top (at a)"
  using assms unfolding eventually_at_split filterlim_at_split
  by (auto intro!: lhopital_right_at_top_at_top[of f a g f' g'] 
                   lhopital_left_at_top_at_top[of f a g f' g'])

lemma lhopital_at_top_at_bot:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_0: "LIM x at a. f x :> at_top"
  assumes g_0: "LIM x at a. g x :> at_bot"
    and ev:
      "eventually (\<lambda>x. DERIV f x :> f' x) (at a)"
      "eventually (\<lambda>x. DERIV g x :> g' x) (at a)"
    and lim: "filterlim (\<lambda> x. (f' x / g' x)) at_bot (at a)"
  shows "filterlim (\<lambda> x. f x / g x) at_bot (at a)"
  using assms unfolding eventually_at_split filterlim_at_split
  by (auto intro!: lhopital_right_at_top_at_bot[of f a g f' g'] 
                   lhopital_left_at_top_at_bot[of f a g f' g'])

end
