(*  Title:      HOL/Real/HahnBanach/FunctionNorm.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The norm of a function *}

theory FunctionNorm = NormedSpace + FunctionOrder:

subsection {* Continuous linear forms*}

text {*
  A linear form @{text f} on a normed vector space @{text "(V, \<parallel>\<cdot>\<parallel>)"}
  is \emph{continuous}, iff it is bounded, i.e.
  \begin{center}
  @{text "\<exists>c \<in> R. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>"}
  \end{center}
  In our application no other functions than linear forms are
  considered, so we can define continuous linear forms as bounded
  linear forms:
*}

locale continuous = var V + norm_syntax + linearform +
  assumes bounded: "\<exists>c. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>"

declare continuous.intro [intro?] continuous_axioms.intro [intro?]

lemma continuousI [intro]:
  includes norm_syntax + linearform
  assumes r: "\<And>x. x \<in> V \<Longrightarrow> \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>"
  shows "continuous V norm f"
proof
  show "linearform V f" .
  from r have "\<exists>c. \<forall>x\<in>V. \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" by blast
  then show "continuous_axioms V norm f" ..
qed


subsection {* The norm of a linear form *}

text {*
  The least real number @{text c} for which holds
  \begin{center}
  @{text "\<forall>x \<in> V. \<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>"}
  \end{center}
  is called the \emph{norm} of @{text f}.

  For non-trivial vector spaces @{text "V \<noteq> {0}"} the norm can be
  defined as
  \begin{center}
  @{text "\<parallel>f\<parallel> = \<sup>x \<noteq> 0. \<bar>f x\<bar> / \<parallel>x\<parallel>"}
  \end{center}

  For the case @{text "V = {0}"} the supremum would be taken from an
  empty set. Since @{text \<real>} is unbounded, there would be no supremum.
  To avoid this situation it must be guaranteed that there is an
  element in this set. This element must be @{text "{} \<ge> 0"} so that
  @{text fn_norm} has the norm properties. Furthermore it does not
  have to change the norm in all other cases, so it must be @{text 0},
  as all other elements are @{text "{} \<ge> 0"}.

  Thus we define the set @{text B} where the supremum is taken from as
  follows:
  \begin{center}
  @{text "{0} \<union> {\<bar>f x\<bar> / \<parallel>x\<parallel>. x \<noteq> 0 \<and> x \<in> F}"}
  \end{center}

  @{text fn_norm} is equal to the supremum of @{text B}, if the
  supremum exists (otherwise it is undefined).
*}

locale fn_norm = norm_syntax +
  fixes B defines "B V f \<equiv> {0} \<union> {\<bar>f x\<bar> / \<parallel>x\<parallel> | x. x \<noteq> 0 \<and> x \<in> V}"
  fixes fn_norm ("\<parallel>_\<parallel>\<hyphen>_" [0, 1000] 999)
  defines "\<parallel>f\<parallel>\<hyphen>V \<equiv> \<Squnion>(B V f)"

lemma (in fn_norm) B_not_empty [intro]: "0 \<in> B V f"
  by (simp add: B_def)

text {*
  The following lemma states that every continuous linear form on a
  normed space @{text "(V, \<parallel>\<cdot>\<parallel>)"} has a function norm.
*}

lemma (in normed_vectorspace) fn_norm_works:   (* FIXME bug with "(in fn_norm)" !? *)
  includes fn_norm + continuous
  shows "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
proof -
  txt {* The existence of the supremum is shown using the
    completeness of the reals. Completeness means, that every
    non-empty bounded set of reals has a supremum. *}
  have "\<exists>a. lub (B V f) a"
  proof (rule real_complete)
    txt {* First we have to show that @{text B} is non-empty: *}
    have "0 \<in> B V f" ..
    thus "\<exists>x. x \<in> B V f" ..

    txt {* Then we have to show that @{text B} is bounded: *}
    show "\<exists>c. \<forall>y \<in> B V f. y \<le> c"
    proof -
      txt {* We know that @{text f} is bounded by some value @{text c}. *}
      from bounded obtain c where c: "\<forall>x \<in> V. \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" ..

      txt {* To prove the thesis, we have to show that there is some
        @{text b}, such that @{text "y \<le> b"} for all @{text "y \<in>
        B"}. Due to the definition of @{text B} there are two cases. *}

      def b \<equiv> "max c 0"
      have "\<forall>y \<in> B V f. y \<le> b"
      proof
        fix y assume y: "y \<in> B V f"
        show "y \<le> b"
        proof cases
          assume "y = 0"
          thus ?thesis by (unfold b_def) arith
        next
          txt {* The second case is @{text "y = \<bar>f x\<bar> / \<parallel>x\<parallel>"} for some
            @{text "x \<in> V"} with @{text "x \<noteq> 0"}. *}
          assume "y \<noteq> 0"
          with y obtain x where y_rep: "y = \<bar>f x\<bar> * inverse \<parallel>x\<parallel>"
              and x: "x \<in> V" and neq: "x \<noteq> 0"
            by (auto simp add: B_def real_divide_def)
          from x neq have gt: "0 < \<parallel>x\<parallel>" ..

          txt {* The thesis follows by a short calculation using the
            fact that @{text f} is bounded. *}

          note y_rep
          also have "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<le> (c * \<parallel>x\<parallel>) * inverse \<parallel>x\<parallel>"
          proof (rule mult_right_mono)
            from c show "\<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" ..
            from gt have "0 < inverse \<parallel>x\<parallel>" 
              by (rule positive_imp_inverse_positive)
            thus "0 \<le> inverse \<parallel>x\<parallel>" by (rule order_less_imp_le)
          qed
          also have "\<dots> = c * (\<parallel>x\<parallel> * inverse \<parallel>x\<parallel>)"
            by (rule real_mult_assoc)
          also
          from gt have "\<parallel>x\<parallel> \<noteq> 0" by simp
          hence "\<parallel>x\<parallel> * inverse \<parallel>x\<parallel> = 1" by (simp add: real_mult_inv_right1)
          also have "c * 1 \<le> b" by (simp add: b_def le_maxI1)
          finally show "y \<le> b" .
        qed
      qed
      thus ?thesis ..
    qed
  qed
  then show ?thesis by (unfold fn_norm_def) (rule the_lubI_ex)
qed

lemma (in normed_vectorspace) fn_norm_ub [iff?]:
  includes fn_norm + continuous
  assumes b: "b \<in> B V f"
  shows "b \<le> \<parallel>f\<parallel>\<hyphen>V"
proof -
  have "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
    by (unfold B_def fn_norm_def) (rule fn_norm_works [OF _ continuous.intro])
  from this and b show ?thesis ..
qed

lemma (in normed_vectorspace) fn_norm_leastB:
  includes fn_norm + continuous
  assumes b: "\<And>b. b \<in> B V f \<Longrightarrow> b \<le> y"
  shows "\<parallel>f\<parallel>\<hyphen>V \<le> y"
proof -
  have "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
    by (unfold B_def fn_norm_def) (rule fn_norm_works [OF _ continuous.intro])
  from this and b show ?thesis ..
qed

text {* The norm of a continuous function is always @{text "\<ge> 0"}. *}

lemma (in normed_vectorspace) fn_norm_ge_zero [iff]:
  includes fn_norm + continuous
  shows "0 \<le> \<parallel>f\<parallel>\<hyphen>V"
proof -
  txt {* The function norm is defined as the supremum of @{text B}.
    So it is @{text "\<ge> 0"} if all elements in @{text B} are @{text "\<ge>
    0"}, provided the supremum exists and @{text B} is not empty. *}
  have "lub (B V f) (\<parallel>f\<parallel>\<hyphen>V)"
    by (unfold B_def fn_norm_def) (rule fn_norm_works [OF _ continuous.intro])
  moreover have "0 \<in> B V f" ..
  ultimately show ?thesis ..
qed

text {*
  \medskip The fundamental property of function norms is:
  \begin{center}
  @{text "\<bar>f x\<bar> \<le> \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>"}
  \end{center}
*}

lemma (in normed_vectorspace) fn_norm_le_cong:
  includes fn_norm + continuous + linearform
  assumes x: "x \<in> V"
  shows "\<bar>f x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>"
proof cases
  assume "x = 0"
  then have "\<bar>f x\<bar> = \<bar>f 0\<bar>" by simp
  also have "f 0 = 0" ..
  also have "\<bar>\<dots>\<bar> = 0" by simp
  also have "\<dots> \<le> \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>"
  proof (rule real_le_mult_order1a)
    show "0 \<le> \<parallel>f\<parallel>\<hyphen>V"
      by (unfold B_def fn_norm_def)
        (rule fn_norm_ge_zero [OF _ continuous.intro])
    show "0 \<le> norm x" ..
  qed
  finally show "\<bar>f x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>" .
next
  assume "x \<noteq> 0"
  with x have neq: "\<parallel>x\<parallel> \<noteq> 0" by simp
  then have "\<bar>f x\<bar> = (\<bar>f x\<bar> * inverse \<parallel>x\<parallel>) * \<parallel>x\<parallel>" by simp
  also have "\<dots> \<le>  \<parallel>f\<parallel>\<hyphen>V * \<parallel>x\<parallel>"
  proof (rule mult_right_mono)
    from x show "0 \<le> \<parallel>x\<parallel>" ..
    from x and neq have "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<in> B V f"
      by (auto simp add: B_def real_divide_def)
    then show "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<le> \<parallel>f\<parallel>\<hyphen>V"
      by (unfold B_def fn_norm_def) (rule fn_norm_ub [OF _ continuous.intro])
  qed
  finally show ?thesis .
qed

text {*
  \medskip The function norm is the least positive real number for
  which the following inequation holds:
  \begin{center}
    @{text "\<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>"}
  \end{center}
*}

lemma (in normed_vectorspace) fn_norm_least [intro?]:
  includes fn_norm + continuous
  assumes ineq: "\<forall>x \<in> V. \<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" and ge: "0 \<le> c"
  shows "\<parallel>f\<parallel>\<hyphen>V \<le> c"
proof (rule fn_norm_leastB [folded B_def fn_norm_def])
  fix b assume b: "b \<in> B V f"
  show "b \<le> c"
  proof cases
    assume "b = 0"
    with ge show ?thesis by simp
  next
    assume "b \<noteq> 0"
    with b obtain x where b_rep: "b = \<bar>f x\<bar> * inverse \<parallel>x\<parallel>"
        and x_neq: "x \<noteq> 0" and x: "x \<in> V"
      by (auto simp add: B_def real_divide_def)
    note b_rep
    also have "\<bar>f x\<bar> * inverse \<parallel>x\<parallel> \<le> (c * \<parallel>x\<parallel>) * inverse \<parallel>x\<parallel>"
    proof (rule mult_right_mono)
      have "0 < \<parallel>x\<parallel>" ..
      then show "0 \<le> inverse \<parallel>x\<parallel>" by simp
      from ineq and x show "\<bar>f x\<bar> \<le> c * \<parallel>x\<parallel>" ..
    qed
    also have "\<dots> = c"
    proof -
      from x_neq and x have "\<parallel>x\<parallel> \<noteq> 0" by simp
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
qed (simp_all! add: continuous_def)

end
