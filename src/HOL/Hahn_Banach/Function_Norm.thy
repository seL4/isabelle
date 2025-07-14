(*  Title:      HOL/Hahn_Banach/Function_Norm.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>The norm of a function\<close>

theory Function_Norm
imports Normed_Space Function_Order
begin

subsection \<open>Continuous linear forms\<close>

text \<open>
  A linear form \<open>f\<close> on a normed vector space \<open>(V, \<parallel>\<cdot>\<parallel>)\<close> is \<^emph>\<open>continuous\<close>, iff
  it is bounded, i.e.
  \begin{center}
  \<open>\<exists>c \<in> R. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>\<close>
  \end{center}
  In our application no other functions than linear forms are considered, so
  we can define continuous linear forms as bounded linear forms:
\<close>

locale continuous = linearform +
  fixes norm :: "_ \<Rightarrow> real"    (\<open>\<parallel>_\<parallel>\<close>)
  assumes bounded: "\<exists>c. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>"

declare continuous.intro [intro?] continuous_axioms.intro [intro?]

lemma continuousI [intro]:
  fixes norm :: "_ \<Rightarrow> real"  (\<open>\<parallel>_\<parallel>\<close>)
  assumes "linearform V f"
  assumes r: "\<And>x. x \<in> V \<Longrightarrow> \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>"
  shows "continuous V f norm"
proof
  show "linearform V f" by fact
  from r have "\<exists>c. \<forall>x\<in>V. \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" by blast
  then show "continuous_axioms V f norm" ..
qed


subsection \<open>The norm of a linear form\<close>

text \<open>
  The least real number \<open>c\<close> for which holds
  \begin{center}
  \<open>\<forall>x \<in> V. \<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>\<close>
  \end{center}
  is called the \<^emph>\<open>norm\<close> of \<open>f\<close>.

  For non-trivial vector spaces \<open>V \<noteq> {0}\<close> the norm can be defined as
  \begin{center}
  \<open>\<parallel>f\<parallel> = \<sup>x \<noteq> 0. \<bar>f x\<bar> / \<parallel>x\<parallel>\<close>
  \end{center}

  For the case \<open>V = {0}\<close> the supremum would be taken from an empty set. Since
  \<open>\<real>\<close> is unbounded, there would be no supremum. To avoid this situation it
  must be guaranteed that there is an element in this set. This element must
  be \<open>{} \<ge> 0\<close> so that \<open>fn_norm\<close> has the norm properties. Furthermore it does
  not have to change the norm in all other cases, so it must be \<open>0\<close>, as all
  other elements are \<open>{} \<ge> 0\<close>.

  Thus we define the set \<open>B\<close> where the supremum is taken from as follows:
  \begin{center}
  \<open>{0} \<union> {\<bar>f x\<bar> / \<parallel>x\<parallel>. x \<noteq> 0 \<and> x \<in> F}\<close>
  \end{center}

  \<open>fn_norm\<close> is equal to the supremum of \<open>B\<close>, if the supremum exists (otherwise
  it is undefined).
\<close>

locale fn_norm =
  fixes norm :: "_ \<Rightarrow> real"    (\<open>\<parallel>_\<parallel>\<close>)
  fixes B defines "B V f \<equiv> {0} \<union> {\<bar>f x\<bar> / \<parallel>x\<parallel> | x. x \<noteq> 0 \<and> x \<in> V}"
  fixes fn_norm (\<open>\<parallel>_\<parallel>\<hyphen>_\<close> [0, 1000] 999)
  defines "\<parallel>f\<parallel>\<hyphen>V \<equiv> \<Squnion>(B V f)"

locale normed_vectorspace_with_fn_norm = normed_vectorspace + fn_norm

lemma (in fn_norm) B_not_empty [intro]: "0 \<in> B V f"
  by (simp add: B_def)

text \<open>
  The following lemma states that every continuous linear form on a normed
  space \<open>(V, \<parallel>\<cdot>\<parallel>)\<close> has a function norm.
\<close>

lemma (in normed_vectorspace_with_fn_norm) fn_norm_works:
  assumes "continuous V f norm"
  shows "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
proof -
  interpret continuous V f norm by fact
  txt \<open>The existence of the supremum is shown using the
    completeness of the reals. Completeness means, that every
    non-empty bounded set of reals has a supremum.\<close>
  have "\<exists>a. lub (B V f) a"
  proof (rule real_complete)
    txt \<open>First we have to show that \<open>B\<close> is non-empty:\<close>
    have "0 \<in> B V f" ..
    then show "\<exists>x. x \<in> B V f" ..

    txt \<open>Then we have to show that \<open>B\<close> is bounded:\<close>
    show "\<exists>c. \<forall>y \<in> B V f. y \<le> c"
    proof -
      txt \<open>We know that \<open>f\<close> is bounded by some value \<open>c\<close>.\<close>
      from bounded obtain c where c: "\<forall>x \<in> V. \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" ..

      txt \<open>To prove the thesis, we have to show that there is some \<open>b\<close>, such
        that \<open>y \<le> b\<close> for all \<open>y \<in> B\<close>. Due to the definition of \<open>B\<close> there are
        two cases.\<close>

      define b where "b = max c 0"
      have "\<forall>y \<in> B V f. y \<le> b"
      proof
        fix y assume y: "y \<in> B V f"
        show "y \<le> b"
        proof (cases "y = 0")
          case True
          then show ?thesis unfolding b_def by arith
        next
          txt \<open>The second case is \<open>y = \<bar>f x\<bar> / \<parallel>x\<parallel>\<close> for some
            \<open>x \<in> V\<close> with \<open>x \<noteq> 0\<close>.\<close>
          case False
          with y obtain x where y_rep: "y = \<bar>f x\<bar> * inverse \<parallel>x\<parallel>"
              and x: "x \<in> V" and neq: "x \<noteq> 0"
            by (auto simp add: B_def divide_inverse)
          from x neq have gt: "0 < \<parallel>x\<parallel>" ..

          txt \<open>The thesis follows by a short calculation using the
            fact that \<open>f\<close> is bounded.\<close>

          note y_rep
          also have "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<le> (c * \<parallel>x\<parallel>) * inverse \<parallel>x\<parallel>"
          proof (rule mult_right_mono)
            from c x show "\<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" ..
            from gt have "0 < inverse \<parallel>x\<parallel>"
              by (rule positive_imp_inverse_positive)
            then show "0 \<le> inverse \<parallel>x\<parallel>" by (rule order_less_imp_le)
          qed
          also have "\<dots> = c * (\<parallel>x\<parallel> * inverse \<parallel>x\<parallel>)"
            by (rule Groups.mult.assoc)
          also
          from gt have "\<parallel>x\<parallel> \<noteq> 0" by simp
          then have "\<parallel>x\<parallel> * inverse \<parallel>x\<parallel> = 1" by simp
          also have "c * 1 \<le> b" by (simp add: b_def)
          finally show "y \<le> b" .
        qed
      qed
      then show ?thesis ..
    qed
  qed
  then show ?thesis unfolding fn_norm_def by (rule the_lubI_ex)
qed

lemma (in normed_vectorspace_with_fn_norm) fn_norm_ub [intro?]:
  assumes "continuous V f norm"
  assumes b: "b \<in> B V f"
  shows "b \<le> \<parallel>f\<parallel>\<hyphen>V"
proof -
  interpret continuous V f norm by fact
  have "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
    using \<open>continuous V f norm\<close> by (rule fn_norm_works)
  from this and b show ?thesis ..
qed

lemma (in normed_vectorspace_with_fn_norm) fn_norm_leastB:
  assumes "continuous V f norm"
  assumes b: "\<And>b. b \<in> B V f \<Longrightarrow> b \<le> y"
  shows "\<parallel>f\<parallel>\<hyphen>V \<le> y"
proof -
  interpret continuous V f norm by fact
  have "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
    using \<open>continuous V f norm\<close> by (rule fn_norm_works)
  from this and b show ?thesis ..
qed

text \<open>The norm of a continuous function is always \<open>\<ge> 0\<close>.\<close>

lemma (in normed_vectorspace_with_fn_norm) fn_norm_ge_zero [iff]:
  assumes "continuous V f norm"
  shows "0 \<le> \<parallel>f\<parallel>\<hyphen>V"
proof -
  interpret continuous V f norm by fact
  txt \<open>The function norm is defined as the supremum of \<open>B\<close>.
    So it is \<open>\<ge> 0\<close> if all elements in \<open>B\<close> are \<open>\<ge>
    0\<close>, provided the supremum exists and \<open>B\<close> is not empty.\<close>
  have "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
    using \<open>continuous V f norm\<close> by (rule fn_norm_works)
  moreover have "0 \<in> B V f" ..
  ultimately show ?thesis ..
qed

text \<open>
  \<^medskip>
  The fundamental property of function norms is:
  \begin{center}
  \<open>\<bar>f x\<bar> \<le> \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>\<close>
  \end{center}
\<close>

lemma (in normed_vectorspace_with_fn_norm) fn_norm_le_cong:
  assumes "continuous V f norm" "linearform V f"
  assumes x: "x \<in> V"
  shows "\<bar>f x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>"
proof -
  interpret continuous V f norm by fact
  interpret linearform V f by fact
  show ?thesis
  proof (cases "x = 0")
    case True
    then have "\<bar>f x\<bar> = \<bar>f 0\<bar>" by simp
    also have "f 0 = 0" by rule unfold_locales
    also have "\<bar>\<dots>\<bar> = 0" by simp
    also have a: "0 \<le> \<parallel>f\<parallel>\<hyphen>V"
      using \<open>continuous V f norm\<close> by (rule fn_norm_ge_zero)
    from x have "0 \<le> norm x" ..
    with a have "0 \<le> \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>" by (simp add: zero_le_mult_iff)
    finally show "\<bar>f x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>" .
  next
    case False
    with x have neq: "\<parallel>x\<parallel> \<noteq> 0" by simp
    then have "\<bar>f x\<bar> = (\<bar>f x\<bar> * inverse \<parallel>x\<parallel>) * \<parallel>x\<parallel>" by simp
    also have "\<dots> \<le>  \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>"
    proof (rule mult_right_mono)
      from x show "0 \<le> \<parallel>x\<parallel>" ..
      from x and neq have "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<in> B V f"
        by (auto simp add: B_def divide_inverse)
      with \<open>continuous V f norm\<close> show "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<le> \<parallel>f\<parallel>\<hyphen>V"
        by (rule fn_norm_ub)
    qed
    finally show ?thesis .
  qed
qed

text \<open>
  \<^medskip>
  The function norm is the least positive real number for which the
  following inequality holds:
  \begin{center}
    \<open>\<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>\<close>
  \end{center}
\<close>

lemma (in normed_vectorspace_with_fn_norm) fn_norm_least [intro?]:
  assumes "continuous V f norm"
  assumes ineq: "\<And>x. x \<in> V \<Longrightarrow> \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" and ge: "0 \<le> c"
  shows "\<parallel>f\<parallel>\<hyphen>V \<le> c"
proof -
  interpret continuous V f norm by fact
  show ?thesis
  proof (rule fn_norm_leastB [folded B_def fn_norm_def])
    fix b assume b: "b \<in> B V f"
    show "b \<le> c"
    proof (cases "b = 0")
      case True
      with ge show ?thesis by simp
    next
      case False
      with b obtain x where b_rep: "b = \<bar>f x\<bar> * inverse \<parallel>x\<parallel>"
        and x_neq: "x \<noteq> 0" and x: "x \<in> V"
        by (auto simp add: B_def divide_inverse)
      note b_rep
      also have "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<le> (c * \<parallel>x\<parallel>) * inverse \<parallel>x\<parallel>"
      proof (rule mult_right_mono)
        have "0 < \<parallel>x\<parallel>" using x x_neq ..
        then show "0 \<le> inverse \<parallel>x\<parallel>" by simp
        from x show "\<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" by (rule ineq)
      qed
      also have "\<dots> = c"
      proof -
        from x_neq and x have "\<parallel>x\<parallel> \<noteq> 0" by simp
        then show ?thesis by simp
      qed
      finally show ?thesis .
    qed
  qed (use \<open>continuous V f norm\<close> in \<open>simp_all add: continuous_def\<close>)
qed

end
