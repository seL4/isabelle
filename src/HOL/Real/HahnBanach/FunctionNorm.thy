(*  Title:      HOL/Real/HahnBanach/FunctionNorm.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The norm of a function *}

theory FunctionNorm = NormedSpace + FunctionOrder:

subsection {* Continuous linear forms*}

text {*
  A linear form @{text f} on a normed vector space @{text "(V, \<parallel>\<cdot>\<parallel>)"}
  is \emph{continuous}, iff it is bounded, i.~e.
  \begin{center}
  @{text "\<exists>c \<in> R. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>"}
  \end{center}
  In our application no other functions than linear forms are
  considered, so we can define continuous linear forms as bounded
  linear forms:
*}

constdefs
  is_continuous ::
  "'a::{plus, minus, zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  "is_continuous V norm f \<equiv>
    is_linearform V f \<and> (\<exists>c. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c * norm x)"

lemma continuousI [intro]:
  "is_linearform V f \<Longrightarrow> (\<And>x. x \<in> V \<Longrightarrow> \<bar>f x\<bar> \<le> c * norm x)
  \<Longrightarrow> is_continuous V norm f"
  by (unfold is_continuous_def) blast

lemma continuous_linearform [intro?]:
  "is_continuous V norm f \<Longrightarrow> is_linearform V f"
  by (unfold is_continuous_def) blast

lemma continuous_bounded [intro?]:
  "is_continuous V norm f
  \<Longrightarrow> \<exists>c. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c * norm x"
  by (unfold is_continuous_def) blast


subsection{* The norm of a linear form *}

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
  @{text function_norm} has the norm properties. Furthermore
  it does not have to change the norm in all other cases, so it must
  be @{text 0}, as all other elements of are @{text "{} \<ge> 0"}.

  Thus we define the set @{text B} the supremum is taken from as
  \begin{center}
  @{text "{0} \<union> {\<bar>f x\<bar> / \<parallel>x\<parallel>. x \<noteq> 0 \<and> x \<in> F}"}
  \end{center}
*}

constdefs
  B :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a::{plus, minus, zero} \<Rightarrow> real) \<Rightarrow> real set"
  "B V norm f \<equiv>
  {Numeral0} \<union> {\<bar>f x\<bar> * inverse (norm x) | x. x \<noteq> 0 \<and> x \<in> V}"

text {*
  @{text n} is the function norm of @{text f}, iff @{text n} is the
  supremum of @{text B}.
*}

constdefs
  is_function_norm ::
  "('a::{minus,plus,zero} \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  "is_function_norm f V norm fn \<equiv> is_Sup UNIV (B V norm f) fn"

text {*
  @{text function_norm} is equal to the supremum of @{text B}, if the
  supremum exists. Otherwise it is undefined.
*}

constdefs
  function_norm :: "('a::{minus,plus,zero} \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  "function_norm f V norm \<equiv> Sup UNIV (B V norm f)"

syntax
  function_norm :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"  ("\<parallel>_\<parallel>_,_")

lemma B_not_empty: "Numeral0 \<in> B V norm f"
  by (unfold B_def) blast

text {*
  The following lemma states that every continuous linear form on a
  normed space @{text "(V, \<parallel>\<cdot>\<parallel>)"} has a function norm.
*}

lemma ex_fnorm [intro?]:
  "is_normed_vectorspace V norm \<Longrightarrow> is_continuous V norm f
     \<Longrightarrow> is_function_norm f V norm \<parallel>f\<parallel>V,norm"
proof (unfold function_norm_def is_function_norm_def
  is_continuous_def Sup_def, elim conjE, rule someI2_ex)
  assume "is_normed_vectorspace V norm"
  assume "is_linearform V f"
  and e: "\<exists>c. \<forall>x \<in> V. \<bar>f x\<bar> \<le> c * norm x"

  txt {* The existence of the supremum is shown using the
  completeness of the reals. Completeness means, that
  every non-empty bounded set of reals has a
  supremum. *}
  show  "\<exists>a. is_Sup UNIV (B V norm f) a"
  proof (unfold is_Sup_def, rule reals_complete)

    txt {* First we have to show that @{text B} is non-empty: *}

    show "\<exists>X. X \<in> B V norm f"
    proof
      show "Numeral0 \<in> (B V norm f)" by (unfold B_def) blast
    qed

    txt {* Then we have to show that @{text B} is bounded: *}

    from e show "\<exists>Y. isUb UNIV (B V norm f) Y"
    proof

      txt {* We know that @{text f} is bounded by some value @{text c}. *}

      fix c assume a: "\<forall>x \<in> V. \<bar>f x\<bar> \<le> c * norm x"
      def b \<equiv> "max c Numeral0"

      show "?thesis"
      proof (intro exI isUbI setleI ballI, unfold B_def,
        elim UnE CollectE exE conjE singletonE)

        txt {* To proof the thesis, we have to show that there is some
        constant @{text b}, such that @{text "y \<le> b"} for all
        @{text "y \<in> B"}. Due to the definition of @{text B} there are
        two cases for @{text "y \<in> B"}.  If @{text "y = 0"} then
        @{text "y \<le> max c 0"}: *}

        fix y assume "y = (Numeral0::real)"
        show "y \<le> b" by (simp! add: le_maxI2)

        txt {* The second case is @{text "y = \<bar>f x\<bar> / \<parallel>x\<parallel>"} for some
        @{text "x \<in> V"} with @{text "x \<noteq> 0"}. *}

      next
        fix x y
        assume "x \<in> V"  "x \<noteq> 0"

        txt {* The thesis follows by a short calculation using the
        fact that @{text f} is bounded. *}

        assume "y = \<bar>f x\<bar> * inverse (norm x)"
        also have "... \<le> c * norm x * inverse (norm x)"
        proof (rule real_mult_le_le_mono2)
          show "Numeral0 \<le> inverse (norm x)"
            by (rule order_less_imp_le, rule real_inverse_gt_zero1,
                rule normed_vs_norm_gt_zero)
          from a show "\<bar>f x\<bar> \<le> c * norm x" ..
        qed
        also have "... = c * (norm x * inverse (norm x))"
          by (rule real_mult_assoc)
        also have "(norm x * inverse (norm x)) = (Numeral1::real)"
        proof (rule real_mult_inv_right1)
          show nz: "norm x \<noteq> Numeral0"
            by (rule not_sym, rule lt_imp_not_eq,
              rule normed_vs_norm_gt_zero)
        qed
        also have "c * ... \<le> b " by (simp! add: le_maxI1)
        finally show "y \<le> b" .
      qed simp
    qed
  qed
qed

text {* The norm of a continuous function is always @{text "\<ge> 0"}. *}

lemma fnorm_ge_zero [intro?]:
  "is_continuous V norm f \<Longrightarrow> is_normed_vectorspace V norm
   \<Longrightarrow> Numeral0 \<le> \<parallel>f\<parallel>V,norm"
proof -
  assume c: "is_continuous V norm f"
     and n: "is_normed_vectorspace V norm"

  txt {* The function norm is defined as the supremum of @{text B}.
  So it is @{text "\<ge> 0"} if all elements in @{text B} are
  @{text "\<ge> 0"}, provided the supremum exists and @{text B} is not
  empty. *}

  show ?thesis
  proof (unfold function_norm_def, rule sup_ub1)
    show "\<forall>x \<in> (B V norm f). Numeral0 \<le> x"
    proof (intro ballI, unfold B_def,
           elim UnE singletonE CollectE exE conjE)
      fix x r
      assume "x \<in> V"  "x \<noteq> 0"
        and r: "r = \<bar>f x\<bar> * inverse (norm x)"

      have ge: "Numeral0 \<le> \<bar>f x\<bar>" by (simp! only: abs_ge_zero)
      have "Numeral0 \<le> inverse (norm x)"
        by (rule order_less_imp_le, rule real_inverse_gt_zero1, rule)(***
        proof (rule order_less_imp_le);
          show "Numeral0 < inverse (norm x)";
          proof (rule real_inverse_gt_zero);
            show "Numeral0 < norm x"; ..;
          qed;
        qed; ***)
      with ge show "Numeral0 \<le> r"
       by (simp only: r, rule real_le_mult_order1a)
    qed (simp!)

    txt {* Since @{text f} is continuous the function norm exists: *}

    have "is_function_norm f V norm \<parallel>f\<parallel>V,norm" ..
    thus "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))"
      by (unfold is_function_norm_def function_norm_def)

    txt {* @{text B} is non-empty by construction: *}

    show "Numeral0 \<in> B V norm f" by (rule B_not_empty)
  qed
qed

text {*
  \medskip The fundamental property of function norms is:
  \begin{center}
  @{text "\<bar>f x\<bar> \<le> \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>"}
  \end{center}
*}

lemma norm_fx_le_norm_f_norm_x:
  "is_continuous V norm f \<Longrightarrow> is_normed_vectorspace V norm \<Longrightarrow> x \<in> V
    \<Longrightarrow> \<bar>f x\<bar> \<le> \<parallel>f\<parallel>V,norm * norm x"
proof -
  assume "is_normed_vectorspace V norm"  "x \<in> V"
  and c: "is_continuous V norm f"
  have v: "is_vectorspace V" ..

 txt{* The proof is by case analysis on @{text x}. *}

  show ?thesis
  proof cases

    txt {* For the case @{text "x = 0"} the thesis follows from the
    linearity of @{text f}: for every linear function holds
    @{text "f 0 = 0"}. *}

    assume "x = 0"
    have "\<bar>f x\<bar> = \<bar>f 0\<bar>" by (simp!)
    also from v continuous_linearform have "f 0 = Numeral0" ..
    also note abs_zero
    also have "Numeral0 \<le> \<parallel>f\<parallel>V,norm * norm x"
    proof (rule real_le_mult_order1a)
      show "Numeral0 \<le> \<parallel>f\<parallel>V,norm" ..
      show "Numeral0 \<le> norm x" ..
    qed
    finally
    show "\<bar>f x\<bar> \<le> \<parallel>f\<parallel>V,norm * norm x" .

  next
    assume "x \<noteq> 0"
    have n: "Numeral0 < norm x" ..
    hence nz: "norm x \<noteq> Numeral0"
      by (simp only: lt_imp_not_eq)

    txt {* For the case @{text "x \<noteq> 0"} we derive the following fact
    from the definition of the function norm:*}

    have l: "\<bar>f x\<bar> * inverse (norm x) \<le> \<parallel>f\<parallel>V,norm"
    proof (unfold function_norm_def, rule sup_ub)
      from ex_fnorm [OF _ c]
      show "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))"
         by (simp! add: is_function_norm_def function_norm_def)
      show "\<bar>f x\<bar> * inverse (norm x) \<in> B V norm f"
        by (unfold B_def, intro UnI2 CollectI exI [of _ x]
            conjI, simp)
    qed

    txt {* The thesis now follows by a short calculation: *}

    have "\<bar>f x\<bar> = \<bar>f x\<bar> * Numeral1" by (simp!)
    also from nz have "Numeral1 = inverse (norm x) * norm x"
      by (simp add: real_mult_inv_left1)
    also have "\<bar>f x\<bar> * ... = \<bar>f x\<bar> * inverse (norm x) * norm x"
      by (simp! add: real_mult_assoc)
    also from n l have "... \<le> \<parallel>f\<parallel>V,norm * norm x"
      by (simp add: real_mult_le_le_mono2)
    finally show "\<bar>f x\<bar> \<le> \<parallel>f\<parallel>V,norm * norm x" .
  qed
qed

text {*
  \medskip The function norm is the least positive real number for
  which the following inequation holds:
  \begin{center}
  @{text "\<bar>f x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>"}
  \end{center}
*}

lemma fnorm_le_ub:
  "is_continuous V norm f \<Longrightarrow> is_normed_vectorspace V norm \<Longrightarrow>
     \<forall>x \<in> V. \<bar>f x\<bar> \<le> c * norm x \<Longrightarrow> Numeral0 \<le> c
  \<Longrightarrow> \<parallel>f\<parallel>V,norm \<le> c"
proof (unfold function_norm_def)
  assume "is_normed_vectorspace V norm"
  assume c: "is_continuous V norm f"
  assume fb: "\<forall>x \<in> V. \<bar>f x\<bar> \<le> c * norm x"
    and "Numeral0 \<le> c"

  txt {* Suppose the inequation holds for some @{text "c \<ge> 0"}.  If
  @{text c} is an upper bound of @{text B}, then @{text c} is greater
  than the function norm since the function norm is the least upper
  bound.  *}

  show "Sup UNIV (B V norm f) \<le> c"
  proof (rule sup_le_ub)
    from ex_fnorm [OF _ c]
    show "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))"
      by (simp! add: is_function_norm_def function_norm_def)

    txt {* @{text c} is an upper bound of @{text B}, i.e. every
    @{text "y \<in> B"} is less than @{text c}. *}

    show "isUb UNIV (B V norm f) c"
    proof (intro isUbI setleI ballI)
      fix y assume "y \<in> B V norm f"
      thus le: "y \<le> c"
      proof (unfold B_def, elim UnE CollectE exE conjE singletonE)

       txt {* The first case for @{text "y \<in> B"} is @{text "y = 0"}. *}

        assume "y = Numeral0"
        show "y \<le> c" by (blast!)

        txt{* The second case is @{text "y = \<bar>f x\<bar> / \<parallel>x\<parallel>"} for some
        @{text "x \<in> V"} with @{text "x \<noteq> 0"}. *}

      next
        fix x
        assume "x \<in> V"  "x \<noteq> 0"

        have lz: "Numeral0 < norm x"
          by (simp! add: normed_vs_norm_gt_zero)

        have nz: "norm x \<noteq> Numeral0"
        proof (rule not_sym)
          from lz show "Numeral0 \<noteq> norm x"
            by (simp! add: order_less_imp_not_eq)
        qed

        from lz have "Numeral0 < inverse (norm x)"
          by (simp! add: real_inverse_gt_zero1)
        hence inverse_gez: "Numeral0 \<le> inverse (norm x)"
          by (rule order_less_imp_le)

        assume "y = \<bar>f x\<bar> * inverse (norm x)"
        also from inverse_gez have "... \<le> c * norm x * inverse (norm x)"
          proof (rule real_mult_le_le_mono2)
            show "\<bar>f x\<bar> \<le> c * norm x" by (rule bspec)
          qed
        also have "... \<le> c" by (simp add: nz real_mult_assoc)
        finally show ?thesis .
      qed
    qed blast
  qed
qed

end
