(*  Title:      HOL/NSA/NSA.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Lawrence C Paulson, University of Cambridge
*)

header{*Infinite Numbers, Infinitesimals, Infinitely Close Relation*}

theory NSA
imports HyperDef RComplete
begin

definition
  hnorm :: "'a::real_normed_vector star \<Rightarrow> real star" where
  [transfer_unfold]: "hnorm = *f* norm"

definition
  Infinitesimal  :: "('a::real_normed_vector) star set" where
  "Infinitesimal = {x. \<forall>r \<in> Reals. 0 < r --> hnorm x < r}"

definition
  HFinite :: "('a::real_normed_vector) star set" where
  "HFinite = {x. \<exists>r \<in> Reals. hnorm x < r}"

definition
  HInfinite :: "('a::real_normed_vector) star set" where
  "HInfinite = {x. \<forall>r \<in> Reals. r < hnorm x}"

definition
  approx :: "['a::real_normed_vector star, 'a star] => bool"  (infixl "@=" 50) where
    --{*the `infinitely close' relation*}
  "(x @= y) = ((x - y) \<in> Infinitesimal)"

definition
  st        :: "hypreal => hypreal" where
    --{*the standard part of a hyperreal*}
  "st = (%x. @r. x \<in> HFinite & r \<in> Reals & r @= x)"

definition
  monad     :: "'a::real_normed_vector star => 'a star set" where
  "monad x = {y. x @= y}"

definition
  galaxy    :: "'a::real_normed_vector star => 'a star set" where
  "galaxy x = {y. (x + -y) \<in> HFinite}"

notation (xsymbols)
  approx  (infixl "\<approx>" 50)

notation (HTML output)
  approx  (infixl "\<approx>" 50)

lemma SReal_def: "Reals == {x. \<exists>r. x = hypreal_of_real r}"
by (simp add: Reals_def image_def)

subsection {* Nonstandard Extension of the Norm Function *}

definition
  scaleHR :: "real star \<Rightarrow> 'a star \<Rightarrow> 'a::real_normed_vector star" where
  [transfer_unfold]: "scaleHR = starfun2 scaleR"

lemma Standard_hnorm [simp]: "x \<in> Standard \<Longrightarrow> hnorm x \<in> Standard"
by (simp add: hnorm_def)

lemma star_of_norm [simp]: "star_of (norm x) = hnorm (star_of x)"
by transfer (rule refl)

lemma hnorm_ge_zero [simp]:
  "\<And>x::'a::real_normed_vector star. 0 \<le> hnorm x"
by transfer (rule norm_ge_zero)

lemma hnorm_eq_zero [simp]:
  "\<And>x::'a::real_normed_vector star. (hnorm x = 0) = (x = 0)"
by transfer (rule norm_eq_zero)

lemma hnorm_triangle_ineq:
  "\<And>x y::'a::real_normed_vector star. hnorm (x + y) \<le> hnorm x + hnorm y"
by transfer (rule norm_triangle_ineq)

lemma hnorm_triangle_ineq3:
  "\<And>x y::'a::real_normed_vector star. \<bar>hnorm x - hnorm y\<bar> \<le> hnorm (x - y)"
by transfer (rule norm_triangle_ineq3)

lemma hnorm_scaleR:
  "\<And>x::'a::real_normed_vector star.
   hnorm (a *\<^sub>R x) = \<bar>star_of a\<bar> * hnorm x"
by transfer (rule norm_scaleR)

lemma hnorm_scaleHR:
  "\<And>a (x::'a::real_normed_vector star).
   hnorm (scaleHR a x) = \<bar>a\<bar> * hnorm x"
by transfer (rule norm_scaleR)

lemma hnorm_mult_ineq:
  "\<And>x y::'a::real_normed_algebra star. hnorm (x * y) \<le> hnorm x * hnorm y"
by transfer (rule norm_mult_ineq)

lemma hnorm_mult:
  "\<And>x y::'a::real_normed_div_algebra star. hnorm (x * y) = hnorm x * hnorm y"
by transfer (rule norm_mult)

lemma hnorm_hyperpow:
  "\<And>(x::'a::{real_normed_div_algebra} star) n.
   hnorm (x pow n) = hnorm x pow n"
by transfer (rule norm_power)

lemma hnorm_one [simp]:
  "hnorm (1\<Colon>'a::real_normed_div_algebra star) = 1"
by transfer (rule norm_one)

lemma hnorm_zero [simp]:
  "hnorm (0\<Colon>'a::real_normed_vector star) = 0"
by transfer (rule norm_zero)

lemma zero_less_hnorm_iff [simp]:
  "\<And>x::'a::real_normed_vector star. (0 < hnorm x) = (x \<noteq> 0)"
by transfer (rule zero_less_norm_iff)

lemma hnorm_minus_cancel [simp]:
  "\<And>x::'a::real_normed_vector star. hnorm (- x) = hnorm x"
by transfer (rule norm_minus_cancel)

lemma hnorm_minus_commute:
  "\<And>a b::'a::real_normed_vector star. hnorm (a - b) = hnorm (b - a)"
by transfer (rule norm_minus_commute)

lemma hnorm_triangle_ineq2:
  "\<And>a b::'a::real_normed_vector star. hnorm a - hnorm b \<le> hnorm (a - b)"
by transfer (rule norm_triangle_ineq2)

lemma hnorm_triangle_ineq4:
  "\<And>a b::'a::real_normed_vector star. hnorm (a - b) \<le> hnorm a + hnorm b"
by transfer (rule norm_triangle_ineq4)

lemma abs_hnorm_cancel [simp]:
  "\<And>a::'a::real_normed_vector star. \<bar>hnorm a\<bar> = hnorm a"
by transfer (rule abs_norm_cancel)

lemma hnorm_of_hypreal [simp]:
  "\<And>r. hnorm (of_hypreal r::'a::real_normed_algebra_1 star) = \<bar>r\<bar>"
by transfer (rule norm_of_real)

lemma nonzero_hnorm_inverse:
  "\<And>a::'a::real_normed_div_algebra star.
   a \<noteq> 0 \<Longrightarrow> hnorm (inverse a) = inverse (hnorm a)"
by transfer (rule nonzero_norm_inverse)

lemma hnorm_inverse:
  "\<And>a::'a::{real_normed_div_algebra, division_ring_inverse_zero} star.
   hnorm (inverse a) = inverse (hnorm a)"
by transfer (rule norm_inverse)

lemma hnorm_divide:
  "\<And>a b::'a::{real_normed_field, field_inverse_zero} star.
   hnorm (a / b) = hnorm a / hnorm b"
by transfer (rule norm_divide)

lemma hypreal_hnorm_def [simp]:
  "\<And>r::hypreal. hnorm r = \<bar>r\<bar>"
by transfer (rule real_norm_def)

lemma hnorm_add_less:
  "\<And>(x::'a::real_normed_vector star) y r s.
   \<lbrakk>hnorm x < r; hnorm y < s\<rbrakk> \<Longrightarrow> hnorm (x + y) < r + s"
by transfer (rule norm_add_less)

lemma hnorm_mult_less:
  "\<And>(x::'a::real_normed_algebra star) y r s.
   \<lbrakk>hnorm x < r; hnorm y < s\<rbrakk> \<Longrightarrow> hnorm (x * y) < r * s"
by transfer (rule norm_mult_less)

lemma hnorm_scaleHR_less:
  "\<lbrakk>\<bar>x\<bar> < r; hnorm y < s\<rbrakk> \<Longrightarrow> hnorm (scaleHR x y) < r * s"
apply (simp only: hnorm_scaleHR)
apply (simp add: mult_strict_mono')
done

subsection{*Closure Laws for the Standard Reals*}

lemma Reals_minus_iff [simp]: "(-x \<in> Reals) = (x \<in> Reals)"
apply auto
apply (drule Reals_minus, auto)
done

lemma Reals_add_cancel: "\<lbrakk>x + y \<in> Reals; y \<in> Reals\<rbrakk> \<Longrightarrow> x \<in> Reals"
by (drule (1) Reals_diff, simp)

lemma SReal_hrabs: "(x::hypreal) \<in> Reals ==> abs x \<in> Reals"
by (simp add: Reals_eq_Standard)

lemma SReal_hypreal_of_real [simp]: "hypreal_of_real x \<in> Reals"
by (simp add: Reals_eq_Standard)

lemma SReal_divide_number_of: "r \<in> Reals ==> r/(number_of w::hypreal) \<in> Reals"
by simp

text{*epsilon is not in Reals because it is an infinitesimal*}
lemma SReal_epsilon_not_mem: "epsilon \<notin> Reals"
apply (simp add: SReal_def)
apply (auto simp add: hypreal_of_real_not_eq_epsilon [THEN not_sym])
done

lemma SReal_omega_not_mem: "omega \<notin> Reals"
apply (simp add: SReal_def)
apply (auto simp add: hypreal_of_real_not_eq_omega [THEN not_sym])
done

lemma SReal_UNIV_real: "{x. hypreal_of_real x \<in> Reals} = (UNIV::real set)"
by simp

lemma SReal_iff: "(x \<in> Reals) = (\<exists>y. x = hypreal_of_real y)"
by (simp add: SReal_def)

lemma hypreal_of_real_image: "hypreal_of_real `(UNIV::real set) = Reals"
by (simp add: Reals_eq_Standard Standard_def)

lemma inv_hypreal_of_real_image: "inv hypreal_of_real ` Reals = UNIV"
apply (auto simp add: SReal_def)
apply (rule inj_star_of [THEN inv_f_f, THEN subst], blast)
done

lemma SReal_hypreal_of_real_image:
      "[| \<exists>x. x: P; P \<subseteq> Reals |] ==> \<exists>Q. P = hypreal_of_real ` Q"
by (simp add: SReal_def image_def, blast)

lemma SReal_dense:
     "[| (x::hypreal) \<in> Reals; y \<in> Reals;  x<y |] ==> \<exists>r \<in> Reals. x<r & r<y"
apply (auto simp add: SReal_def)
apply (drule dense, auto)
done

text{*Completeness of Reals, but both lemmas are unused.*}

lemma SReal_sup_lemma:
     "P \<subseteq> Reals ==> ((\<exists>x \<in> P. y < x) =
      (\<exists>X. hypreal_of_real X \<in> P & y < hypreal_of_real X))"
by (blast dest!: SReal_iff [THEN iffD1])

lemma SReal_sup_lemma2:
     "[| P \<subseteq> Reals; \<exists>x. x \<in> P; \<exists>y \<in> Reals. \<forall>x \<in> P. x < y |]
      ==> (\<exists>X. X \<in> {w. hypreal_of_real w \<in> P}) &
          (\<exists>Y. \<forall>X \<in> {w. hypreal_of_real w \<in> P}. X < Y)"
apply (rule conjI)
apply (fast dest!: SReal_iff [THEN iffD1])
apply (auto, frule subsetD, assumption)
apply (drule SReal_iff [THEN iffD1])
apply (auto, rule_tac x = ya in exI, auto)
done


subsection{* Set of Finite Elements is a Subring of the Extended Reals*}

lemma HFinite_add: "[|x \<in> HFinite; y \<in> HFinite|] ==> (x+y) \<in> HFinite"
apply (simp add: HFinite_def)
apply (blast intro!: Reals_add hnorm_add_less)
done

lemma HFinite_mult:
  fixes x y :: "'a::real_normed_algebra star"
  shows "[|x \<in> HFinite; y \<in> HFinite|] ==> x*y \<in> HFinite"
apply (simp add: HFinite_def)
apply (blast intro!: Reals_mult hnorm_mult_less)
done

lemma HFinite_scaleHR:
  "[|x \<in> HFinite; y \<in> HFinite|] ==> scaleHR x y \<in> HFinite"
apply (simp add: HFinite_def)
apply (blast intro!: Reals_mult hnorm_scaleHR_less)
done

lemma HFinite_minus_iff: "(-x \<in> HFinite) = (x \<in> HFinite)"
by (simp add: HFinite_def)

lemma HFinite_star_of [simp]: "star_of x \<in> HFinite"
apply (simp add: HFinite_def)
apply (rule_tac x="star_of (norm x) + 1" in bexI)
apply (transfer, simp)
apply (blast intro: Reals_add SReal_hypreal_of_real Reals_1)
done

lemma SReal_subset_HFinite: "(Reals::hypreal set) \<subseteq> HFinite"
by (auto simp add: SReal_def)

lemma HFiniteD: "x \<in> HFinite ==> \<exists>t \<in> Reals. hnorm x < t"
by (simp add: HFinite_def)

lemma HFinite_hrabs_iff [iff]: "(abs (x::hypreal) \<in> HFinite) = (x \<in> HFinite)"
by (simp add: HFinite_def)

lemma HFinite_hnorm_iff [iff]:
  "(hnorm (x::hypreal) \<in> HFinite) = (x \<in> HFinite)"
by (simp add: HFinite_def)

lemma HFinite_number_of [simp]: "number_of w \<in> HFinite"
unfolding star_number_def by (rule HFinite_star_of)

(** As always with numerals, 0 and 1 are special cases **)

lemma HFinite_0 [simp]: "0 \<in> HFinite"
unfolding star_zero_def by (rule HFinite_star_of)

lemma HFinite_1 [simp]: "1 \<in> HFinite"
unfolding star_one_def by (rule HFinite_star_of)

lemma hrealpow_HFinite:
  fixes x :: "'a::{real_normed_algebra,monoid_mult} star"
  shows "x \<in> HFinite ==> x ^ n \<in> HFinite"
apply (induct n)
apply (auto simp add: power_Suc intro: HFinite_mult)
done

lemma HFinite_bounded:
  "[|(x::hypreal) \<in> HFinite; y \<le> x; 0 \<le> y |] ==> y \<in> HFinite"
apply (cases "x \<le> 0")
apply (drule_tac y = x in order_trans)
apply (drule_tac [2] order_antisym)
apply (auto simp add: linorder_not_le)
apply (auto intro: order_le_less_trans simp add: abs_if HFinite_def)
done


subsection{* Set of Infinitesimals is a Subring of the Hyperreals*}

lemma InfinitesimalI:
  "(\<And>r. \<lbrakk>r \<in> \<real>; 0 < r\<rbrakk> \<Longrightarrow> hnorm x < r) \<Longrightarrow> x \<in> Infinitesimal"
by (simp add: Infinitesimal_def)

lemma InfinitesimalD:
      "x \<in> Infinitesimal ==> \<forall>r \<in> Reals. 0 < r --> hnorm x < r"
by (simp add: Infinitesimal_def)

lemma InfinitesimalI2:
  "(\<And>r. 0 < r \<Longrightarrow> hnorm x < star_of r) \<Longrightarrow> x \<in> Infinitesimal"
by (auto simp add: Infinitesimal_def SReal_def)

lemma InfinitesimalD2:
  "\<lbrakk>x \<in> Infinitesimal; 0 < r\<rbrakk> \<Longrightarrow> hnorm x < star_of r"
by (auto simp add: Infinitesimal_def SReal_def)

lemma Infinitesimal_zero [iff]: "0 \<in> Infinitesimal"
by (simp add: Infinitesimal_def)

lemma hypreal_sum_of_halves: "x/(2::hypreal) + x/(2::hypreal) = x"
by auto

lemma Infinitesimal_add:
     "[| x \<in> Infinitesimal; y \<in> Infinitesimal |] ==> (x+y) \<in> Infinitesimal"
apply (rule InfinitesimalI)
apply (rule hypreal_sum_of_halves [THEN subst])
apply (drule half_gt_zero)
apply (blast intro: hnorm_add_less SReal_divide_number_of dest: InfinitesimalD)
done

lemma Infinitesimal_minus_iff [simp]: "(-x:Infinitesimal) = (x:Infinitesimal)"
by (simp add: Infinitesimal_def)

lemma Infinitesimal_hnorm_iff:
  "(hnorm x \<in> Infinitesimal) = (x \<in> Infinitesimal)"
by (simp add: Infinitesimal_def)

lemma Infinitesimal_hrabs_iff [iff]:
  "(abs (x::hypreal) \<in> Infinitesimal) = (x \<in> Infinitesimal)"
by (simp add: abs_if)

lemma Infinitesimal_of_hypreal_iff [simp]:
  "((of_hypreal x::'a::real_normed_algebra_1 star) \<in> Infinitesimal) =
   (x \<in> Infinitesimal)"
by (subst Infinitesimal_hnorm_iff [symmetric], simp)

lemma Infinitesimal_diff:
     "[| x \<in> Infinitesimal;  y \<in> Infinitesimal |] ==> x-y \<in> Infinitesimal"
by (simp add: diff_minus Infinitesimal_add)

lemma Infinitesimal_mult:
  fixes x y :: "'a::real_normed_algebra star"
  shows "[|x \<in> Infinitesimal; y \<in> Infinitesimal|] ==> (x * y) \<in> Infinitesimal"
apply (rule InfinitesimalI)
apply (subgoal_tac "hnorm (x * y) < 1 * r", simp only: mult_1)
apply (rule hnorm_mult_less)
apply (simp_all add: InfinitesimalD)
done

lemma Infinitesimal_HFinite_mult:
  fixes x y :: "'a::real_normed_algebra star"
  shows "[| x \<in> Infinitesimal; y \<in> HFinite |] ==> (x * y) \<in> Infinitesimal"
apply (rule InfinitesimalI)
apply (drule HFiniteD, clarify)
apply (subgoal_tac "0 < t")
apply (subgoal_tac "hnorm (x * y) < (r / t) * t", simp)
apply (subgoal_tac "0 < r / t")
apply (rule hnorm_mult_less)
apply (simp add: InfinitesimalD Reals_divide)
apply assumption
apply (simp only: divide_pos_pos)
apply (erule order_le_less_trans [OF hnorm_ge_zero])
done

lemma Infinitesimal_HFinite_scaleHR:
  "[| x \<in> Infinitesimal; y \<in> HFinite |] ==> scaleHR x y \<in> Infinitesimal"
apply (rule InfinitesimalI)
apply (drule HFiniteD, clarify)
apply (drule InfinitesimalD)
apply (simp add: hnorm_scaleHR)
apply (subgoal_tac "0 < t")
apply (subgoal_tac "\<bar>x\<bar> * hnorm y < (r / t) * t", simp)
apply (subgoal_tac "0 < r / t")
apply (rule mult_strict_mono', simp_all)
apply (simp only: divide_pos_pos)
apply (erule order_le_less_trans [OF hnorm_ge_zero])
done

lemma Infinitesimal_HFinite_mult2:
  fixes x y :: "'a::real_normed_algebra star"
  shows "[| x \<in> Infinitesimal; y \<in> HFinite |] ==> (y * x) \<in> Infinitesimal"
apply (rule InfinitesimalI)
apply (drule HFiniteD, clarify)
apply (subgoal_tac "0 < t")
apply (subgoal_tac "hnorm (y * x) < t * (r / t)", simp)
apply (subgoal_tac "0 < r / t")
apply (rule hnorm_mult_less)
apply assumption
apply (simp add: InfinitesimalD Reals_divide)
apply (simp only: divide_pos_pos)
apply (erule order_le_less_trans [OF hnorm_ge_zero])
done

lemma Infinitesimal_scaleR2:
  "x \<in> Infinitesimal ==> a *\<^sub>R x \<in> Infinitesimal"
apply (case_tac "a = 0", simp)
apply (rule InfinitesimalI)
apply (drule InfinitesimalD)
apply (drule_tac x="r / \<bar>star_of a\<bar>" in bspec)
apply (simp add: Reals_eq_Standard)
apply (simp add: divide_pos_pos)
apply (simp add: hnorm_scaleR pos_less_divide_eq mult_commute)
done

lemma Compl_HFinite: "- HFinite = HInfinite"
apply (auto simp add: HInfinite_def HFinite_def linorder_not_less)
apply (rule_tac y="r + 1" in order_less_le_trans, simp)
apply simp
done

lemma HInfinite_inverse_Infinitesimal:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "x \<in> HInfinite ==> inverse x \<in> Infinitesimal"
apply (rule InfinitesimalI)
apply (subgoal_tac "x \<noteq> 0")
apply (rule inverse_less_imp_less)
apply (simp add: nonzero_hnorm_inverse)
apply (simp add: HInfinite_def Reals_inverse)
apply assumption
apply (clarify, simp add: Compl_HFinite [symmetric])
done

lemma HInfiniteI: "(\<And>r. r \<in> \<real> \<Longrightarrow> r < hnorm x) \<Longrightarrow> x \<in> HInfinite"
by (simp add: HInfinite_def)

lemma HInfiniteD: "\<lbrakk>x \<in> HInfinite; r \<in> \<real>\<rbrakk> \<Longrightarrow> r < hnorm x"
by (simp add: HInfinite_def)

lemma HInfinite_mult:
  fixes x y :: "'a::real_normed_div_algebra star"
  shows "[|x \<in> HInfinite; y \<in> HInfinite|] ==> (x*y) \<in> HInfinite"
apply (rule HInfiniteI, simp only: hnorm_mult)
apply (subgoal_tac "r * 1 < hnorm x * hnorm y", simp only: mult_1)
apply (case_tac "x = 0", simp add: HInfinite_def)
apply (rule mult_strict_mono)
apply (simp_all add: HInfiniteD)
done

lemma hypreal_add_zero_less_le_mono: "[|r < x; (0::hypreal) \<le> y|] ==> r < x+y"
by (auto dest: add_less_le_mono)

lemma HInfinite_add_ge_zero:
     "[|(x::hypreal) \<in> HInfinite; 0 \<le> y; 0 \<le> x|] ==> (x + y): HInfinite"
by (auto intro!: hypreal_add_zero_less_le_mono 
       simp add: abs_if add_commute add_nonneg_nonneg HInfinite_def)

lemma HInfinite_add_ge_zero2:
     "[|(x::hypreal) \<in> HInfinite; 0 \<le> y; 0 \<le> x|] ==> (y + x): HInfinite"
by (auto intro!: HInfinite_add_ge_zero simp add: add_commute)

lemma HInfinite_add_gt_zero:
     "[|(x::hypreal) \<in> HInfinite; 0 < y; 0 < x|] ==> (x + y): HInfinite"
by (blast intro: HInfinite_add_ge_zero order_less_imp_le)

lemma HInfinite_minus_iff: "(-x \<in> HInfinite) = (x \<in> HInfinite)"
by (simp add: HInfinite_def)

lemma HInfinite_add_le_zero:
     "[|(x::hypreal) \<in> HInfinite; y \<le> 0; x \<le> 0|] ==> (x + y): HInfinite"
apply (drule HInfinite_minus_iff [THEN iffD2])
apply (rule HInfinite_minus_iff [THEN iffD1])
apply (auto intro: HInfinite_add_ge_zero)
done

lemma HInfinite_add_lt_zero:
     "[|(x::hypreal) \<in> HInfinite; y < 0; x < 0|] ==> (x + y): HInfinite"
by (blast intro: HInfinite_add_le_zero order_less_imp_le)

lemma HFinite_sum_squares:
  fixes a b c :: "'a::real_normed_algebra star"
  shows "[|a: HFinite; b: HFinite; c: HFinite|]
      ==> a*a + b*b + c*c \<in> HFinite"
by (auto intro: HFinite_mult HFinite_add)

lemma not_Infinitesimal_not_zero: "x \<notin> Infinitesimal ==> x \<noteq> 0"
by auto

lemma not_Infinitesimal_not_zero2: "x \<in> HFinite - Infinitesimal ==> x \<noteq> 0"
by auto

lemma HFinite_diff_Infinitesimal_hrabs:
  "(x::hypreal) \<in> HFinite - Infinitesimal ==> abs x \<in> HFinite - Infinitesimal"
by blast

lemma hnorm_le_Infinitesimal:
  "\<lbrakk>e \<in> Infinitesimal; hnorm x \<le> e\<rbrakk> \<Longrightarrow> x \<in> Infinitesimal"
by (auto simp add: Infinitesimal_def abs_less_iff)

lemma hnorm_less_Infinitesimal:
  "\<lbrakk>e \<in> Infinitesimal; hnorm x < e\<rbrakk> \<Longrightarrow> x \<in> Infinitesimal"
by (erule hnorm_le_Infinitesimal, erule order_less_imp_le)

lemma hrabs_le_Infinitesimal:
     "[| e \<in> Infinitesimal; abs (x::hypreal) \<le> e |] ==> x \<in> Infinitesimal"
by (erule hnorm_le_Infinitesimal, simp)

lemma hrabs_less_Infinitesimal:
      "[| e \<in> Infinitesimal; abs (x::hypreal) < e |] ==> x \<in> Infinitesimal"
by (erule hnorm_less_Infinitesimal, simp)

lemma Infinitesimal_interval:
      "[| e \<in> Infinitesimal; e' \<in> Infinitesimal; e' < x ; x < e |] 
       ==> (x::hypreal) \<in> Infinitesimal"
by (auto simp add: Infinitesimal_def abs_less_iff)

lemma Infinitesimal_interval2:
     "[| e \<in> Infinitesimal; e' \<in> Infinitesimal;
         e' \<le> x ; x \<le> e |] ==> (x::hypreal) \<in> Infinitesimal"
by (auto intro: Infinitesimal_interval simp add: order_le_less)


lemma lemma_Infinitesimal_hyperpow:
     "[| (x::hypreal) \<in> Infinitesimal; 0 < N |] ==> abs (x pow N) \<le> abs x"
apply (unfold Infinitesimal_def)
apply (auto intro!: hyperpow_Suc_le_self2 
          simp add: hyperpow_hrabs [symmetric] hypnat_gt_zero_iff2 abs_ge_zero)
done

lemma Infinitesimal_hyperpow:
     "[| (x::hypreal) \<in> Infinitesimal; 0 < N |] ==> x pow N \<in> Infinitesimal"
apply (rule hrabs_le_Infinitesimal)
apply (rule_tac [2] lemma_Infinitesimal_hyperpow, auto)
done

lemma hrealpow_hyperpow_Infinitesimal_iff:
     "(x ^ n \<in> Infinitesimal) = (x pow (hypnat_of_nat n) \<in> Infinitesimal)"
by (simp only: hyperpow_hypnat_of_nat)

lemma Infinitesimal_hrealpow:
     "[| (x::hypreal) \<in> Infinitesimal; 0 < n |] ==> x ^ n \<in> Infinitesimal"
by (simp add: hrealpow_hyperpow_Infinitesimal_iff Infinitesimal_hyperpow)

lemma not_Infinitesimal_mult:
  fixes x y :: "'a::real_normed_div_algebra star"
  shows "[| x \<notin> Infinitesimal;  y \<notin> Infinitesimal|] ==> (x*y) \<notin>Infinitesimal"
apply (unfold Infinitesimal_def, clarify, rename_tac r s)
apply (simp only: linorder_not_less hnorm_mult)
apply (drule_tac x = "r * s" in bspec)
apply (fast intro: Reals_mult)
apply (drule mp, blast intro: mult_pos_pos)
apply (drule_tac c = s and d = "hnorm y" and a = r and b = "hnorm x" in mult_mono)
apply (simp_all (no_asm_simp))
done

lemma Infinitesimal_mult_disj:
  fixes x y :: "'a::real_normed_div_algebra star"
  shows "x*y \<in> Infinitesimal ==> x \<in> Infinitesimal | y \<in> Infinitesimal"
apply (rule ccontr)
apply (drule de_Morgan_disj [THEN iffD1])
apply (fast dest: not_Infinitesimal_mult)
done

lemma HFinite_Infinitesimal_not_zero: "x \<in> HFinite-Infinitesimal ==> x \<noteq> 0"
by blast

lemma HFinite_Infinitesimal_diff_mult:
  fixes x y :: "'a::real_normed_div_algebra star"
  shows "[| x \<in> HFinite - Infinitesimal;
                   y \<in> HFinite - Infinitesimal
                |] ==> (x*y) \<in> HFinite - Infinitesimal"
apply clarify
apply (blast dest: HFinite_mult not_Infinitesimal_mult)
done

lemma Infinitesimal_subset_HFinite:
      "Infinitesimal \<subseteq> HFinite"
apply (simp add: Infinitesimal_def HFinite_def, auto)
apply (rule_tac x = 1 in bexI, auto)
done

lemma Infinitesimal_star_of_mult:
  fixes x :: "'a::real_normed_algebra star"
  shows "x \<in> Infinitesimal ==> x * star_of r \<in> Infinitesimal"
by (erule HFinite_star_of [THEN [2] Infinitesimal_HFinite_mult])

lemma Infinitesimal_star_of_mult2:
  fixes x :: "'a::real_normed_algebra star"
  shows "x \<in> Infinitesimal ==> star_of r * x \<in> Infinitesimal"
by (erule HFinite_star_of [THEN [2] Infinitesimal_HFinite_mult2])


subsection{*The Infinitely Close Relation*}

lemma mem_infmal_iff: "(x \<in> Infinitesimal) = (x @= 0)"
by (simp add: Infinitesimal_def approx_def)

lemma approx_minus_iff: " (x @= y) = (x - y @= 0)"
by (simp add: approx_def)

lemma approx_minus_iff2: " (x @= y) = (-y + x @= 0)"
by (simp add: approx_def diff_minus add_commute)

lemma approx_refl [iff]: "x @= x"
by (simp add: approx_def Infinitesimal_def)

lemma hypreal_minus_distrib1: "-(y + -(x::'a::ab_group_add)) = x + -y"
by (simp add: add_commute)

lemma approx_sym: "x @= y ==> y @= x"
apply (simp add: approx_def)
apply (drule Infinitesimal_minus_iff [THEN iffD2])
apply simp
done

lemma approx_trans: "[| x @= y; y @= z |] ==> x @= z"
apply (simp add: approx_def)
apply (drule (1) Infinitesimal_add)
apply (simp add: diff_minus)
done

lemma approx_trans2: "[| r @= x; s @= x |] ==> r @= s"
by (blast intro: approx_sym approx_trans)

lemma approx_trans3: "[| x @= r; x @= s|] ==> r @= s"
by (blast intro: approx_sym approx_trans)

lemma approx_reorient: "(x @= y) = (y @= x)"
by (blast intro: approx_sym)

(*reorientation simplification procedure: reorients (polymorphic)
  0 = x, 1 = x, nnn = x provided x isn't 0, 1 or a numeral.*)
simproc_setup approx_reorient_simproc
  ("0 @= x" | "1 @= y" | "number_of w @= z") =
{*
  let val rule = @{thm approx_reorient} RS eq_reflection
      fun proc phi ss ct = case term_of ct of
          _ $ t $ u => if can HOLogic.dest_number u then NONE
            else if can HOLogic.dest_number t then SOME rule else NONE
        | _ => NONE
  in proc end
*}

lemma Infinitesimal_approx_minus: "(x-y \<in> Infinitesimal) = (x @= y)"
by (simp add: approx_minus_iff [symmetric] mem_infmal_iff)

lemma approx_monad_iff: "(x @= y) = (monad(x)=monad(y))"
apply (simp add: monad_def)
apply (auto dest: approx_sym elim!: approx_trans equalityCE)
done

lemma Infinitesimal_approx:
     "[| x \<in> Infinitesimal; y \<in> Infinitesimal |] ==> x @= y"
apply (simp add: mem_infmal_iff)
apply (blast intro: approx_trans approx_sym)
done

lemma approx_add: "[| a @= b; c @= d |] ==> a+c @= b+d"
proof (unfold approx_def)
  assume inf: "a - b \<in> Infinitesimal" "c - d \<in> Infinitesimal"
  have "a + c - (b + d) = (a - b) + (c - d)" by simp
  also have "... \<in> Infinitesimal" using inf by (rule Infinitesimal_add)
  finally show "a + c - (b + d) \<in> Infinitesimal" .
qed

lemma approx_minus: "a @= b ==> -a @= -b"
apply (rule approx_minus_iff [THEN iffD2, THEN approx_sym])
apply (drule approx_minus_iff [THEN iffD1])
apply (simp add: add_commute diff_minus)
done

lemma approx_minus2: "-a @= -b ==> a @= b"
by (auto dest: approx_minus)

lemma approx_minus_cancel [simp]: "(-a @= -b) = (a @= b)"
by (blast intro: approx_minus approx_minus2)

lemma approx_add_minus: "[| a @= b; c @= d |] ==> a + -c @= b + -d"
by (blast intro!: approx_add approx_minus)

lemma approx_diff: "[| a @= b; c @= d |] ==> a - c @= b - d"
by (simp only: diff_minus approx_add approx_minus)

lemma approx_mult1:
  fixes a b c :: "'a::real_normed_algebra star"
  shows "[| a @= b; c: HFinite|] ==> a*c @= b*c"
by (simp add: approx_def Infinitesimal_HFinite_mult
              left_diff_distrib [symmetric])

lemma approx_mult2:
  fixes a b c :: "'a::real_normed_algebra star"
  shows "[|a @= b; c: HFinite|] ==> c*a @= c*b"
by (simp add: approx_def Infinitesimal_HFinite_mult2
              right_diff_distrib [symmetric])

lemma approx_mult_subst:
  fixes u v x y :: "'a::real_normed_algebra star"
  shows "[|u @= v*x; x @= y; v \<in> HFinite|] ==> u @= v*y"
by (blast intro: approx_mult2 approx_trans)

lemma approx_mult_subst2:
  fixes u v x y :: "'a::real_normed_algebra star"
  shows "[| u @= x*v; x @= y; v \<in> HFinite |] ==> u @= y*v"
by (blast intro: approx_mult1 approx_trans)

lemma approx_mult_subst_star_of:
  fixes u x y :: "'a::real_normed_algebra star"
  shows "[| u @= x*star_of v; x @= y |] ==> u @= y*star_of v"
by (auto intro: approx_mult_subst2)

lemma approx_eq_imp: "a = b ==> a @= b"
by (simp add: approx_def)

lemma Infinitesimal_minus_approx: "x \<in> Infinitesimal ==> -x @= x"
by (blast intro: Infinitesimal_minus_iff [THEN iffD2] 
                    mem_infmal_iff [THEN iffD1] approx_trans2)

lemma bex_Infinitesimal_iff: "(\<exists>y \<in> Infinitesimal. x - z = y) = (x @= z)"
by (simp add: approx_def)

lemma bex_Infinitesimal_iff2: "(\<exists>y \<in> Infinitesimal. x = z + y) = (x @= z)"
by (force simp add: bex_Infinitesimal_iff [symmetric])

lemma Infinitesimal_add_approx: "[| y \<in> Infinitesimal; x + y = z |] ==> x @= z"
apply (rule bex_Infinitesimal_iff [THEN iffD1])
apply (drule Infinitesimal_minus_iff [THEN iffD2])
apply (auto simp add: add_assoc [symmetric])
done

lemma Infinitesimal_add_approx_self: "y \<in> Infinitesimal ==> x @= x + y"
apply (rule bex_Infinitesimal_iff [THEN iffD1])
apply (drule Infinitesimal_minus_iff [THEN iffD2])
apply (auto simp add: add_assoc [symmetric])
done

lemma Infinitesimal_add_approx_self2: "y \<in> Infinitesimal ==> x @= y + x"
by (auto dest: Infinitesimal_add_approx_self simp add: add_commute)

lemma Infinitesimal_add_minus_approx_self: "y \<in> Infinitesimal ==> x @= x + -y"
by (blast intro!: Infinitesimal_add_approx_self Infinitesimal_minus_iff [THEN iffD2])

lemma Infinitesimal_add_cancel: "[| y \<in> Infinitesimal; x+y @= z|] ==> x @= z"
apply (drule_tac x = x in Infinitesimal_add_approx_self [THEN approx_sym])
apply (erule approx_trans3 [THEN approx_sym], assumption)
done

lemma Infinitesimal_add_right_cancel:
     "[| y \<in> Infinitesimal; x @= z + y|] ==> x @= z"
apply (drule_tac x = z in Infinitesimal_add_approx_self2 [THEN approx_sym])
apply (erule approx_trans3 [THEN approx_sym])
apply (simp add: add_commute)
apply (erule approx_sym)
done

lemma approx_add_left_cancel: "d + b  @= d + c ==> b @= c"
apply (drule approx_minus_iff [THEN iffD1])
apply (simp add: approx_minus_iff [symmetric] add_ac)
done

lemma approx_add_right_cancel: "b + d @= c + d ==> b @= c"
apply (rule approx_add_left_cancel)
apply (simp add: add_commute)
done

lemma approx_add_mono1: "b @= c ==> d + b @= d + c"
apply (rule approx_minus_iff [THEN iffD2])
apply (simp add: approx_minus_iff [symmetric] add_ac)
done

lemma approx_add_mono2: "b @= c ==> b + a @= c + a"
by (simp add: add_commute approx_add_mono1)

lemma approx_add_left_iff [simp]: "(a + b @= a + c) = (b @= c)"
by (fast elim: approx_add_left_cancel approx_add_mono1)

lemma approx_add_right_iff [simp]: "(b + a @= c + a) = (b @= c)"
by (simp add: add_commute)

lemma approx_HFinite: "[| x \<in> HFinite; x @= y |] ==> y \<in> HFinite"
apply (drule bex_Infinitesimal_iff2 [THEN iffD2], safe)
apply (drule Infinitesimal_subset_HFinite [THEN subsetD, THEN HFinite_minus_iff [THEN iffD2]])
apply (drule HFinite_add)
apply (auto simp add: add_assoc)
done

lemma approx_star_of_HFinite: "x @= star_of D ==> x \<in> HFinite"
by (rule approx_sym [THEN [2] approx_HFinite], auto)

lemma approx_mult_HFinite:
  fixes a b c d :: "'a::real_normed_algebra star"
  shows "[|a @= b; c @= d; b: HFinite; d: HFinite|] ==> a*c @= b*d"
apply (rule approx_trans)
apply (rule_tac [2] approx_mult2)
apply (rule approx_mult1)
prefer 2 apply (blast intro: approx_HFinite approx_sym, auto)
done

lemma scaleHR_left_diff_distrib:
  "\<And>a b x. scaleHR (a - b) x = scaleHR a x - scaleHR b x"
by transfer (rule scaleR_left_diff_distrib)

lemma approx_scaleR1:
  "[| a @= star_of b; c: HFinite|] ==> scaleHR a c @= b *\<^sub>R c"
apply (unfold approx_def)
apply (drule (1) Infinitesimal_HFinite_scaleHR)
apply (simp only: scaleHR_left_diff_distrib)
apply (simp add: scaleHR_def star_scaleR_def [symmetric])
done

lemma approx_scaleR2:
  "a @= b ==> c *\<^sub>R a @= c *\<^sub>R b"
by (simp add: approx_def Infinitesimal_scaleR2
              scaleR_right_diff_distrib [symmetric])

lemma approx_scaleR_HFinite:
  "[|a @= star_of b; c @= d; d: HFinite|] ==> scaleHR a c @= b *\<^sub>R d"
apply (rule approx_trans)
apply (rule_tac [2] approx_scaleR2)
apply (rule approx_scaleR1)
prefer 2 apply (blast intro: approx_HFinite approx_sym, auto)
done

lemma approx_mult_star_of:
  fixes a c :: "'a::real_normed_algebra star"
  shows "[|a @= star_of b; c @= star_of d |]
      ==> a*c @= star_of b*star_of d"
by (blast intro!: approx_mult_HFinite approx_star_of_HFinite HFinite_star_of)

lemma approx_SReal_mult_cancel_zero:
     "[| (a::hypreal) \<in> Reals; a \<noteq> 0; a*x @= 0 |] ==> x @= 0"
apply (drule Reals_inverse [THEN SReal_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: mult_assoc [symmetric])
done

lemma approx_mult_SReal1: "[| (a::hypreal) \<in> Reals; x @= 0 |] ==> x*a @= 0"
by (auto dest: SReal_subset_HFinite [THEN subsetD] approx_mult1)

lemma approx_mult_SReal2: "[| (a::hypreal) \<in> Reals; x @= 0 |] ==> a*x @= 0"
by (auto dest: SReal_subset_HFinite [THEN subsetD] approx_mult2)

lemma approx_mult_SReal_zero_cancel_iff [simp]:
     "[|(a::hypreal) \<in> Reals; a \<noteq> 0 |] ==> (a*x @= 0) = (x @= 0)"
by (blast intro: approx_SReal_mult_cancel_zero approx_mult_SReal2)

lemma approx_SReal_mult_cancel:
     "[| (a::hypreal) \<in> Reals; a \<noteq> 0; a* w @= a*z |] ==> w @= z"
apply (drule Reals_inverse [THEN SReal_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: mult_assoc [symmetric])
done

lemma approx_SReal_mult_cancel_iff1 [simp]:
     "[| (a::hypreal) \<in> Reals; a \<noteq> 0|] ==> (a* w @= a*z) = (w @= z)"
by (auto intro!: approx_mult2 SReal_subset_HFinite [THEN subsetD]
         intro: approx_SReal_mult_cancel)

lemma approx_le_bound: "[| (z::hypreal) \<le> f; f @= g; g \<le> z |] ==> f @= z"
apply (simp add: bex_Infinitesimal_iff2 [symmetric], auto)
apply (rule_tac x = "g+y-z" in bexI)
apply (simp (no_asm))
apply (rule Infinitesimal_interval2)
apply (rule_tac [2] Infinitesimal_zero, auto)
done

lemma approx_hnorm:
  fixes x y :: "'a::real_normed_vector star"
  shows "x \<approx> y \<Longrightarrow> hnorm x \<approx> hnorm y"
proof (unfold approx_def)
  assume "x - y \<in> Infinitesimal"
  hence 1: "hnorm (x - y) \<in> Infinitesimal"
    by (simp only: Infinitesimal_hnorm_iff)
  moreover have 2: "(0::real star) \<in> Infinitesimal"
    by (rule Infinitesimal_zero)
  moreover have 3: "0 \<le> \<bar>hnorm x - hnorm y\<bar>"
    by (rule abs_ge_zero)
  moreover have 4: "\<bar>hnorm x - hnorm y\<bar> \<le> hnorm (x - y)"
    by (rule hnorm_triangle_ineq3)
  ultimately have "\<bar>hnorm x - hnorm y\<bar> \<in> Infinitesimal"
    by (rule Infinitesimal_interval2)
  thus "hnorm x - hnorm y \<in> Infinitesimal"
    by (simp only: Infinitesimal_hrabs_iff)
qed


subsection{* Zero is the Only Infinitesimal that is also a Real*}

lemma Infinitesimal_less_SReal:
     "[| (x::hypreal) \<in> Reals; y \<in> Infinitesimal; 0 < x |] ==> y < x"
apply (simp add: Infinitesimal_def)
apply (rule abs_ge_self [THEN order_le_less_trans], auto)
done

lemma Infinitesimal_less_SReal2:
     "(y::hypreal) \<in> Infinitesimal ==> \<forall>r \<in> Reals. 0 < r --> y < r"
by (blast intro: Infinitesimal_less_SReal)

lemma SReal_not_Infinitesimal:
     "[| 0 < y;  (y::hypreal) \<in> Reals|] ==> y \<notin> Infinitesimal"
apply (simp add: Infinitesimal_def)
apply (auto simp add: abs_if)
done

lemma SReal_minus_not_Infinitesimal:
     "[| y < 0;  (y::hypreal) \<in> Reals |] ==> y \<notin> Infinitesimal"
apply (subst Infinitesimal_minus_iff [symmetric])
apply (rule SReal_not_Infinitesimal, auto)
done

lemma SReal_Int_Infinitesimal_zero: "Reals Int Infinitesimal = {0::hypreal}"
apply auto
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (blast dest: SReal_not_Infinitesimal SReal_minus_not_Infinitesimal)
done

lemma SReal_Infinitesimal_zero:
  "[| (x::hypreal) \<in> Reals; x \<in> Infinitesimal|] ==> x = 0"
by (cut_tac SReal_Int_Infinitesimal_zero, blast)

lemma SReal_HFinite_diff_Infinitesimal:
     "[| (x::hypreal) \<in> Reals; x \<noteq> 0 |] ==> x \<in> HFinite - Infinitesimal"
by (auto dest: SReal_Infinitesimal_zero SReal_subset_HFinite [THEN subsetD])

lemma hypreal_of_real_HFinite_diff_Infinitesimal:
     "hypreal_of_real x \<noteq> 0 ==> hypreal_of_real x \<in> HFinite - Infinitesimal"
by (rule SReal_HFinite_diff_Infinitesimal, auto)

lemma star_of_Infinitesimal_iff_0 [iff]:
  "(star_of x \<in> Infinitesimal) = (x = 0)"
apply (auto simp add: Infinitesimal_def)
apply (drule_tac x="hnorm (star_of x)" in bspec)
apply (simp add: SReal_def)
apply (rule_tac x="norm x" in exI, simp)
apply simp
done

lemma star_of_HFinite_diff_Infinitesimal:
     "x \<noteq> 0 ==> star_of x \<in> HFinite - Infinitesimal"
by simp

lemma number_of_not_Infinitesimal [simp]:
     "number_of w \<noteq> (0::hypreal) ==> (number_of w :: hypreal) \<notin> Infinitesimal"
by (fast dest: Reals_number_of [THEN SReal_Infinitesimal_zero])

(*again: 1 is a special case, but not 0 this time*)
lemma one_not_Infinitesimal [simp]:
  "(1::'a::{real_normed_vector,zero_neq_one} star) \<notin> Infinitesimal"
apply (simp only: star_one_def star_of_Infinitesimal_iff_0)
apply simp
done

lemma approx_SReal_not_zero:
  "[| (y::hypreal) \<in> Reals; x @= y; y\<noteq> 0 |] ==> x \<noteq> 0"
apply (cut_tac x = 0 and y = y in linorder_less_linear, simp)
apply (blast dest: approx_sym [THEN mem_infmal_iff [THEN iffD2]] SReal_not_Infinitesimal SReal_minus_not_Infinitesimal)
done

lemma HFinite_diff_Infinitesimal_approx:
     "[| x @= y; y \<in> HFinite - Infinitesimal |]
      ==> x \<in> HFinite - Infinitesimal"
apply (auto intro: approx_sym [THEN [2] approx_HFinite]
            simp add: mem_infmal_iff)
apply (drule approx_trans3, assumption)
apply (blast dest: approx_sym)
done

(*The premise y\<noteq>0 is essential; otherwise x/y =0 and we lose the
  HFinite premise.*)
lemma Infinitesimal_ratio:
  fixes x y :: "'a::{real_normed_div_algebra,field} star"
  shows "[| y \<noteq> 0;  y \<in> Infinitesimal;  x/y \<in> HFinite |]
         ==> x \<in> Infinitesimal"
apply (drule Infinitesimal_HFinite_mult2, assumption)
apply (simp add: divide_inverse mult_assoc)
done

lemma Infinitesimal_SReal_divide: 
  "[| (x::hypreal) \<in> Infinitesimal; y \<in> Reals |] ==> x/y \<in> Infinitesimal"
apply (simp add: divide_inverse)
apply (auto intro!: Infinitesimal_HFinite_mult 
            dest!: Reals_inverse [THEN SReal_subset_HFinite [THEN subsetD]])
done

(*------------------------------------------------------------------
       Standard Part Theorem: Every finite x: R* is infinitely
       close to a unique real number (i.e a member of Reals)
 ------------------------------------------------------------------*)

subsection{* Uniqueness: Two Infinitely Close Reals are Equal*}

lemma star_of_approx_iff [simp]: "(star_of x @= star_of y) = (x = y)"
apply safe
apply (simp add: approx_def)
apply (simp only: star_of_diff [symmetric])
apply (simp only: star_of_Infinitesimal_iff_0)
apply simp
done

lemma SReal_approx_iff:
  "[|(x::hypreal) \<in> Reals; y \<in> Reals|] ==> (x @= y) = (x = y)"
apply auto
apply (simp add: approx_def)
apply (drule (1) Reals_diff)
apply (drule (1) SReal_Infinitesimal_zero)
apply simp
done

lemma number_of_approx_iff [simp]:
     "(number_of v @= (number_of w :: 'a::{number,real_normed_vector} star)) =
      (number_of v = (number_of w :: 'a))"
apply (unfold star_number_def)
apply (rule star_of_approx_iff)
done

(*And also for 0 @= #nn and 1 @= #nn, #nn @= 0 and #nn @= 1.*)
lemma [simp]:
  "(number_of w @= (0::'a::{number,real_normed_vector} star)) =
   (number_of w = (0::'a))"
  "((0::'a::{number,real_normed_vector} star) @= number_of w) =
   (number_of w = (0::'a))"
  "(number_of w @= (1::'b::{number,one,real_normed_vector} star)) =
   (number_of w = (1::'b))"
  "((1::'b::{number,one,real_normed_vector} star) @= number_of w) =
   (number_of w = (1::'b))"
  "~ (0 @= (1::'c::{zero_neq_one,real_normed_vector} star))"
  "~ (1 @= (0::'c::{zero_neq_one,real_normed_vector} star))"
apply (unfold star_number_def star_zero_def star_one_def)
apply (unfold star_of_approx_iff)
by (auto intro: sym)

lemma star_of_approx_number_of_iff [simp]:
     "(star_of k @= number_of w) = (k = number_of w)"
by (subst star_of_approx_iff [symmetric], auto)

lemma star_of_approx_zero_iff [simp]: "(star_of k @= 0) = (k = 0)"
by (simp_all add: star_of_approx_iff [symmetric])

lemma star_of_approx_one_iff [simp]: "(star_of k @= 1) = (k = 1)"
by (simp_all add: star_of_approx_iff [symmetric])

lemma approx_unique_real:
     "[| (r::hypreal) \<in> Reals; s \<in> Reals; r @= x; s @= x|] ==> r = s"
by (blast intro: SReal_approx_iff [THEN iffD1] approx_trans2)


subsection{* Existence of Unique Real Infinitely Close*}

subsubsection{*Lifting of the Ub and Lub Properties*}

lemma hypreal_of_real_isUb_iff:
      "(isUb (Reals) (hypreal_of_real ` Q) (hypreal_of_real Y)) =
       (isUb (UNIV :: real set) Q Y)"
by (simp add: isUb_def setle_def)

lemma hypreal_of_real_isLub1:
     "isLub Reals (hypreal_of_real ` Q) (hypreal_of_real Y)
      ==> isLub (UNIV :: real set) Q Y"
apply (simp add: isLub_def leastP_def)
apply (auto intro: hypreal_of_real_isUb_iff [THEN iffD2]
            simp add: hypreal_of_real_isUb_iff setge_def)
done

lemma hypreal_of_real_isLub2:
      "isLub (UNIV :: real set) Q Y
       ==> isLub Reals (hypreal_of_real ` Q) (hypreal_of_real Y)"
apply (simp add: isLub_def leastP_def)
apply (auto simp add: hypreal_of_real_isUb_iff setge_def)
apply (frule_tac x2 = x in isUbD2a [THEN SReal_iff [THEN iffD1], THEN exE])
 prefer 2 apply assumption
apply (drule_tac x = xa in spec)
apply (auto simp add: hypreal_of_real_isUb_iff)
done

lemma hypreal_of_real_isLub_iff:
     "(isLub Reals (hypreal_of_real ` Q) (hypreal_of_real Y)) =
      (isLub (UNIV :: real set) Q Y)"
by (blast intro: hypreal_of_real_isLub1 hypreal_of_real_isLub2)

lemma lemma_isUb_hypreal_of_real:
     "isUb Reals P Y ==> \<exists>Yo. isUb Reals P (hypreal_of_real Yo)"
by (auto simp add: SReal_iff isUb_def)

lemma lemma_isLub_hypreal_of_real:
     "isLub Reals P Y ==> \<exists>Yo. isLub Reals P (hypreal_of_real Yo)"
by (auto simp add: isLub_def leastP_def isUb_def SReal_iff)

lemma lemma_isLub_hypreal_of_real2:
     "\<exists>Yo. isLub Reals P (hypreal_of_real Yo) ==> \<exists>Y. isLub Reals P Y"
by (auto simp add: isLub_def leastP_def isUb_def)

lemma SReal_complete:
     "[| P \<subseteq> Reals;  \<exists>x. x \<in> P;  \<exists>Y. isUb Reals P Y |]
      ==> \<exists>t::hypreal. isLub Reals P t"
apply (frule SReal_hypreal_of_real_image)
apply (auto, drule lemma_isUb_hypreal_of_real)
apply (auto intro!: reals_complete lemma_isLub_hypreal_of_real2
            simp add: hypreal_of_real_isLub_iff hypreal_of_real_isUb_iff)
done

(* lemma about lubs *)
lemma hypreal_isLub_unique:
     "[| isLub R S x; isLub R S y |] ==> x = (y::hypreal)"
apply (frule isLub_isUb)
apply (frule_tac x = y in isLub_isUb)
apply (blast intro!: order_antisym dest!: isLub_le_isUb)
done

lemma lemma_st_part_ub:
     "(x::hypreal) \<in> HFinite ==> \<exists>u. isUb Reals {s. s \<in> Reals & s < x} u"
apply (drule HFiniteD, safe)
apply (rule exI, rule isUbI)
apply (auto intro: setleI isUbI simp add: abs_less_iff)
done

lemma lemma_st_part_nonempty:
  "(x::hypreal) \<in> HFinite ==> \<exists>y. y \<in> {s. s \<in> Reals & s < x}"
apply (drule HFiniteD, safe)
apply (drule Reals_minus)
apply (rule_tac x = "-t" in exI)
apply (auto simp add: abs_less_iff)
done

lemma lemma_st_part_subset: "{s. s \<in> Reals & s < x} \<subseteq> Reals"
by auto

lemma lemma_st_part_lub:
     "(x::hypreal) \<in> HFinite ==> \<exists>t. isLub Reals {s. s \<in> Reals & s < x} t"
by (blast intro!: SReal_complete lemma_st_part_ub lemma_st_part_nonempty lemma_st_part_subset)

lemma lemma_hypreal_le_left_cancel: "((t::hypreal) + r \<le> t) = (r \<le> 0)"
apply safe
apply (drule_tac c = "-t" in add_left_mono)
apply (drule_tac [2] c = t in add_left_mono)
apply (auto simp add: add_assoc [symmetric])
done

lemma lemma_st_part_le1:
     "[| (x::hypreal) \<in> HFinite;  isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals;  0 < r |] ==> x \<le> t + r"
apply (frule isLubD1a)
apply (rule ccontr, drule linorder_not_le [THEN iffD2])
apply (drule (1) Reals_add)
apply (drule_tac y = "r + t" in isLubD1 [THEN setleD], auto)
done

lemma hypreal_setle_less_trans:
     "[| S *<= (x::hypreal); x < y |] ==> S *<= y"
apply (simp add: setle_def)
apply (auto dest!: bspec order_le_less_trans intro: order_less_imp_le)
done

lemma hypreal_gt_isUb:
     "[| isUb R S (x::hypreal); x < y; y \<in> R |] ==> isUb R S y"
apply (simp add: isUb_def)
apply (blast intro: hypreal_setle_less_trans)
done

lemma lemma_st_part_gt_ub:
     "[| (x::hypreal) \<in> HFinite; x < y; y \<in> Reals |]
      ==> isUb Reals {s. s \<in> Reals & s < x} y"
by (auto dest: order_less_trans intro: order_less_imp_le intro!: isUbI setleI)

lemma lemma_minus_le_zero: "t \<le> t + -r ==> r \<le> (0::hypreal)"
apply (drule_tac c = "-t" in add_left_mono)
apply (auto simp add: add_assoc [symmetric])
done

lemma lemma_st_part_le2:
     "[| (x::hypreal) \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> t + -r \<le> x"
apply (frule isLubD1a)
apply (rule ccontr, drule linorder_not_le [THEN iffD1])
apply (drule Reals_minus, drule_tac a = t in Reals_add, assumption)
apply (drule lemma_st_part_gt_ub, assumption+)
apply (drule isLub_le_isUb, assumption)
apply (drule lemma_minus_le_zero)
apply (auto dest: order_less_le_trans)
done

lemma lemma_st_part1a:
     "[| (x::hypreal) \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> x + -t \<le> r"
apply (subgoal_tac "x \<le> t+r") 
apply (auto intro: lemma_st_part_le1)
done

lemma lemma_st_part2a:
     "[| (x::hypreal) \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals;  0 < r |]
      ==> -(x + -t) \<le> r"
apply (subgoal_tac "(t + -r \<le> x)") 
apply (auto intro: lemma_st_part_le2)
done

lemma lemma_SReal_ub:
     "(x::hypreal) \<in> Reals ==> isUb Reals {s. s \<in> Reals & s < x} x"
by (auto intro: isUbI setleI order_less_imp_le)

lemma lemma_SReal_lub:
     "(x::hypreal) \<in> Reals ==> isLub Reals {s. s \<in> Reals & s < x} x"
apply (auto intro!: isLubI2 lemma_SReal_ub setgeI)
apply (frule isUbD2a)
apply (rule_tac x = x and y = y in linorder_cases)
apply (auto intro!: order_less_imp_le)
apply (drule SReal_dense, assumption, assumption, safe)
apply (drule_tac y = r in isUbD)
apply (auto dest: order_less_le_trans)
done

lemma lemma_st_part_not_eq1:
     "[| (x::hypreal) \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> x + -t \<noteq> r"
apply auto
apply (frule isLubD1a [THEN Reals_minus])
apply (drule Reals_add_cancel, assumption)
apply (drule_tac x = x in lemma_SReal_lub)
apply (drule hypreal_isLub_unique, assumption, auto)
done

lemma lemma_st_part_not_eq2:
     "[| (x::hypreal) \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> -(x + -t) \<noteq> r"
apply (auto)
apply (frule isLubD1a)
apply (drule Reals_add_cancel, assumption)
apply (drule_tac a = "-x" in Reals_minus, simp)
apply (drule_tac x = x in lemma_SReal_lub)
apply (drule hypreal_isLub_unique, assumption, auto)
done

lemma lemma_st_part_major:
     "[| (x::hypreal) \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> abs (x - t) < r"
apply (frule lemma_st_part1a)
apply (frule_tac [4] lemma_st_part2a, auto)
apply (drule order_le_imp_less_or_eq)+
apply (auto dest: lemma_st_part_not_eq1 lemma_st_part_not_eq2 simp add: abs_less_iff)
done

lemma lemma_st_part_major2:
     "[| (x::hypreal) \<in> HFinite; isLub Reals {s. s \<in> Reals & s < x} t |]
      ==> \<forall>r \<in> Reals. 0 < r --> abs (x - t) < r"
by (blast dest!: lemma_st_part_major)


text{*Existence of real and Standard Part Theorem*}
lemma lemma_st_part_Ex:
     "(x::hypreal) \<in> HFinite
       ==> \<exists>t \<in> Reals. \<forall>r \<in> Reals. 0 < r --> abs (x - t) < r"
apply (frule lemma_st_part_lub, safe)
apply (frule isLubD1a)
apply (blast dest: lemma_st_part_major2)
done

lemma st_part_Ex:
     "(x::hypreal) \<in> HFinite ==> \<exists>t \<in> Reals. x @= t"
apply (simp add: approx_def Infinitesimal_def)
apply (drule lemma_st_part_Ex, auto)
done

text{*There is a unique real infinitely close*}
lemma st_part_Ex1: "x \<in> HFinite ==> EX! t::hypreal. t \<in> Reals & x @= t"
apply (drule st_part_Ex, safe)
apply (drule_tac [2] approx_sym, drule_tac [2] approx_sym, drule_tac [2] approx_sym)
apply (auto intro!: approx_unique_real)
done

subsection{* Finite, Infinite and Infinitesimal*}

lemma HFinite_Int_HInfinite_empty [simp]: "HFinite Int HInfinite = {}"
apply (simp add: HFinite_def HInfinite_def)
apply (auto dest: order_less_trans)
done

lemma HFinite_not_HInfinite: 
  assumes x: "x \<in> HFinite" shows "x \<notin> HInfinite"
proof
  assume x': "x \<in> HInfinite"
  with x have "x \<in> HFinite \<inter> HInfinite" by blast
  thus False by auto
qed

lemma not_HFinite_HInfinite: "x\<notin> HFinite ==> x \<in> HInfinite"
apply (simp add: HInfinite_def HFinite_def, auto)
apply (drule_tac x = "r + 1" in bspec)
apply (auto)
done

lemma HInfinite_HFinite_disj: "x \<in> HInfinite | x \<in> HFinite"
by (blast intro: not_HFinite_HInfinite)

lemma HInfinite_HFinite_iff: "(x \<in> HInfinite) = (x \<notin> HFinite)"
by (blast dest: HFinite_not_HInfinite not_HFinite_HInfinite)

lemma HFinite_HInfinite_iff: "(x \<in> HFinite) = (x \<notin> HInfinite)"
by (simp add: HInfinite_HFinite_iff)


lemma HInfinite_diff_HFinite_Infinitesimal_disj:
     "x \<notin> Infinitesimal ==> x \<in> HInfinite | x \<in> HFinite - Infinitesimal"
by (fast intro: not_HFinite_HInfinite)

lemma HFinite_inverse:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "[| x \<in> HFinite; x \<notin> Infinitesimal |] ==> inverse x \<in> HFinite"
apply (subgoal_tac "x \<noteq> 0")
apply (cut_tac x = "inverse x" in HInfinite_HFinite_disj)
apply (auto dest!: HInfinite_inverse_Infinitesimal
            simp add: nonzero_inverse_inverse_eq)
done

lemma HFinite_inverse2:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "x \<in> HFinite - Infinitesimal ==> inverse x \<in> HFinite"
by (blast intro: HFinite_inverse)

(* stronger statement possible in fact *)
lemma Infinitesimal_inverse_HFinite:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "x \<notin> Infinitesimal ==> inverse(x) \<in> HFinite"
apply (drule HInfinite_diff_HFinite_Infinitesimal_disj)
apply (blast intro: HFinite_inverse HInfinite_inverse_Infinitesimal Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma HFinite_not_Infinitesimal_inverse:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "x \<in> HFinite - Infinitesimal ==> inverse x \<in> HFinite - Infinitesimal"
apply (auto intro: Infinitesimal_inverse_HFinite)
apply (drule Infinitesimal_HFinite_mult2, assumption)
apply (simp add: not_Infinitesimal_not_zero right_inverse)
done

lemma approx_inverse:
  fixes x y :: "'a::real_normed_div_algebra star"
  shows
     "[| x @= y; y \<in>  HFinite - Infinitesimal |]
      ==> inverse x @= inverse y"
apply (frule HFinite_diff_Infinitesimal_approx, assumption)
apply (frule not_Infinitesimal_not_zero2)
apply (frule_tac x = x in not_Infinitesimal_not_zero2)
apply (drule HFinite_inverse2)+
apply (drule approx_mult2, assumption, auto)
apply (drule_tac c = "inverse x" in approx_mult1, assumption)
apply (auto intro: approx_sym simp add: mult_assoc)
done

(*Used for NSLIM_inverse, NSLIMSEQ_inverse*)
lemmas star_of_approx_inverse = star_of_HFinite_diff_Infinitesimal [THEN [2] approx_inverse]
lemmas hypreal_of_real_approx_inverse =  hypreal_of_real_HFinite_diff_Infinitesimal [THEN [2] approx_inverse]

lemma inverse_add_Infinitesimal_approx:
  fixes x h :: "'a::real_normed_div_algebra star"
  shows
     "[| x \<in> HFinite - Infinitesimal;
         h \<in> Infinitesimal |] ==> inverse(x + h) @= inverse x"
apply (auto intro: approx_inverse approx_sym Infinitesimal_add_approx_self)
done

lemma inverse_add_Infinitesimal_approx2:
  fixes x h :: "'a::real_normed_div_algebra star"
  shows
     "[| x \<in> HFinite - Infinitesimal;
         h \<in> Infinitesimal |] ==> inverse(h + x) @= inverse x"
apply (rule add_commute [THEN subst])
apply (blast intro: inverse_add_Infinitesimal_approx)
done

lemma inverse_add_Infinitesimal_approx_Infinitesimal:
  fixes x h :: "'a::real_normed_div_algebra star"
  shows
     "[| x \<in> HFinite - Infinitesimal;
         h \<in> Infinitesimal |] ==> inverse(x + h) - inverse x @= h"
apply (rule approx_trans2)
apply (auto intro: inverse_add_Infinitesimal_approx 
            simp add: mem_infmal_iff approx_minus_iff [symmetric])
done

lemma Infinitesimal_square_iff:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "(x \<in> Infinitesimal) = (x*x \<in> Infinitesimal)"
apply (auto intro: Infinitesimal_mult)
apply (rule ccontr, frule Infinitesimal_inverse_HFinite)
apply (frule not_Infinitesimal_not_zero)
apply (auto dest: Infinitesimal_HFinite_mult simp add: mult_assoc)
done
declare Infinitesimal_square_iff [symmetric, simp]

lemma HFinite_square_iff [simp]:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "(x*x \<in> HFinite) = (x \<in> HFinite)"
apply (auto intro: HFinite_mult)
apply (auto dest: HInfinite_mult simp add: HFinite_HInfinite_iff)
done

lemma HInfinite_square_iff [simp]:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "(x*x \<in> HInfinite) = (x \<in> HInfinite)"
by (auto simp add: HInfinite_HFinite_iff)

lemma approx_HFinite_mult_cancel:
  fixes a w z :: "'a::real_normed_div_algebra star"
  shows "[| a: HFinite-Infinitesimal; a* w @= a*z |] ==> w @= z"
apply safe
apply (frule HFinite_inverse, assumption)
apply (drule not_Infinitesimal_not_zero)
apply (auto dest: approx_mult2 simp add: mult_assoc [symmetric])
done

lemma approx_HFinite_mult_cancel_iff1:
  fixes a w z :: "'a::real_normed_div_algebra star"
  shows "a: HFinite-Infinitesimal ==> (a * w @= a * z) = (w @= z)"
by (auto intro: approx_mult2 approx_HFinite_mult_cancel)

lemma HInfinite_HFinite_add_cancel:
     "[| x + y \<in> HInfinite; y \<in> HFinite |] ==> x \<in> HInfinite"
apply (rule ccontr)
apply (drule HFinite_HInfinite_iff [THEN iffD2])
apply (auto dest: HFinite_add simp add: HInfinite_HFinite_iff)
done

lemma HInfinite_HFinite_add:
     "[| x \<in> HInfinite; y \<in> HFinite |] ==> x + y \<in> HInfinite"
apply (rule_tac y = "-y" in HInfinite_HFinite_add_cancel)
apply (auto simp add: add_assoc HFinite_minus_iff)
done

lemma HInfinite_ge_HInfinite:
     "[| (x::hypreal) \<in> HInfinite; x \<le> y; 0 \<le> x |] ==> y \<in> HInfinite"
by (auto intro: HFinite_bounded simp add: HInfinite_HFinite_iff)

lemma Infinitesimal_inverse_HInfinite:
  fixes x :: "'a::real_normed_div_algebra star"
  shows "[| x \<in> Infinitesimal; x \<noteq> 0 |] ==> inverse x \<in> HInfinite"
apply (rule ccontr, drule HFinite_HInfinite_iff [THEN iffD2])
apply (auto dest: Infinitesimal_HFinite_mult2)
done

lemma HInfinite_HFinite_not_Infinitesimal_mult:
  fixes x y :: "'a::real_normed_div_algebra star"
  shows "[| x \<in> HInfinite; y \<in> HFinite - Infinitesimal |]
      ==> x * y \<in> HInfinite"
apply (rule ccontr, drule HFinite_HInfinite_iff [THEN iffD2])
apply (frule HFinite_Infinitesimal_not_zero)
apply (drule HFinite_not_Infinitesimal_inverse)
apply (safe, drule HFinite_mult)
apply (auto simp add: mult_assoc HFinite_HInfinite_iff)
done

lemma HInfinite_HFinite_not_Infinitesimal_mult2:
  fixes x y :: "'a::real_normed_div_algebra star"
  shows "[| x \<in> HInfinite; y \<in> HFinite - Infinitesimal |]
      ==> y * x \<in> HInfinite"
apply (rule ccontr, drule HFinite_HInfinite_iff [THEN iffD2])
apply (frule HFinite_Infinitesimal_not_zero)
apply (drule HFinite_not_Infinitesimal_inverse)
apply (safe, drule_tac x="inverse y" in HFinite_mult)
apply assumption
apply (auto simp add: mult_assoc [symmetric] HFinite_HInfinite_iff)
done

lemma HInfinite_gt_SReal:
  "[| (x::hypreal) \<in> HInfinite; 0 < x; y \<in> Reals |] ==> y < x"
by (auto dest!: bspec simp add: HInfinite_def abs_if order_less_imp_le)

lemma HInfinite_gt_zero_gt_one:
  "[| (x::hypreal) \<in> HInfinite; 0 < x |] ==> 1 < x"
by (auto intro: HInfinite_gt_SReal)


lemma not_HInfinite_one [simp]: "1 \<notin> HInfinite"
apply (simp (no_asm) add: HInfinite_HFinite_iff)
done

lemma approx_hrabs_disj: "abs (x::hypreal) @= x | abs x @= -x"
by (cut_tac x = x in hrabs_disj, auto)


subsection{*Theorems about Monads*}

lemma monad_hrabs_Un_subset: "monad (abs x) \<le> monad(x::hypreal) Un monad(-x)"
by (rule_tac x1 = x in hrabs_disj [THEN disjE], auto)

lemma Infinitesimal_monad_eq: "e \<in> Infinitesimal ==> monad (x+e) = monad x"
by (fast intro!: Infinitesimal_add_approx_self [THEN approx_sym] approx_monad_iff [THEN iffD1])

lemma mem_monad_iff: "(u \<in> monad x) = (-u \<in> monad (-x))"
by (simp add: monad_def)

lemma Infinitesimal_monad_zero_iff: "(x \<in> Infinitesimal) = (x \<in> monad 0)"
by (auto intro: approx_sym simp add: monad_def mem_infmal_iff)

lemma monad_zero_minus_iff: "(x \<in> monad 0) = (-x \<in> monad 0)"
apply (simp (no_asm) add: Infinitesimal_monad_zero_iff [symmetric])
done

lemma monad_zero_hrabs_iff: "((x::hypreal) \<in> monad 0) = (abs x \<in> monad 0)"
apply (rule_tac x1 = x in hrabs_disj [THEN disjE])
apply (auto simp add: monad_zero_minus_iff [symmetric])
done

lemma mem_monad_self [simp]: "x \<in> monad x"
by (simp add: monad_def)


subsection{*Proof that @{term "x @= y"} implies @{term"\<bar>x\<bar> @= \<bar>y\<bar>"}*}

lemma approx_subset_monad: "x @= y ==> {x,y} \<le> monad x"
apply (simp (no_asm))
apply (simp add: approx_monad_iff)
done

lemma approx_subset_monad2: "x @= y ==> {x,y} \<le> monad y"
apply (drule approx_sym)
apply (fast dest: approx_subset_monad)
done

lemma mem_monad_approx: "u \<in> monad x ==> x @= u"
by (simp add: monad_def)

lemma approx_mem_monad: "x @= u ==> u \<in> monad x"
by (simp add: monad_def)

lemma approx_mem_monad2: "x @= u ==> x \<in> monad u"
apply (simp add: monad_def)
apply (blast intro!: approx_sym)
done

lemma approx_mem_monad_zero: "[| x @= y;x \<in> monad 0 |] ==> y \<in> monad 0"
apply (drule mem_monad_approx)
apply (fast intro: approx_mem_monad approx_trans)
done

lemma Infinitesimal_approx_hrabs:
     "[| x @= y; (x::hypreal) \<in> Infinitesimal |] ==> abs x @= abs y"
apply (drule Infinitesimal_monad_zero_iff [THEN iffD1])
apply (blast intro: approx_mem_monad_zero monad_zero_hrabs_iff [THEN iffD1] mem_monad_approx approx_trans3)
done

lemma less_Infinitesimal_less:
     "[| 0 < x;  (x::hypreal) \<notin>Infinitesimal;  e :Infinitesimal |] ==> e < x"
apply (rule ccontr)
apply (auto intro: Infinitesimal_zero [THEN [2] Infinitesimal_interval] 
            dest!: order_le_imp_less_or_eq simp add: linorder_not_less)
done

lemma Ball_mem_monad_gt_zero:
     "[| 0 < (x::hypreal);  x \<notin> Infinitesimal; u \<in> monad x |] ==> 0 < u"
apply (drule mem_monad_approx [THEN approx_sym])
apply (erule bex_Infinitesimal_iff2 [THEN iffD2, THEN bexE])
apply (drule_tac e = "-xa" in less_Infinitesimal_less, auto)
done

lemma Ball_mem_monad_less_zero:
     "[| (x::hypreal) < 0; x \<notin> Infinitesimal; u \<in> monad x |] ==> u < 0"
apply (drule mem_monad_approx [THEN approx_sym])
apply (erule bex_Infinitesimal_iff [THEN iffD2, THEN bexE])
apply (cut_tac x = "-x" and e = xa in less_Infinitesimal_less, auto)
done

lemma lemma_approx_gt_zero:
     "[|0 < (x::hypreal); x \<notin> Infinitesimal; x @= y|] ==> 0 < y"
by (blast dest: Ball_mem_monad_gt_zero approx_subset_monad)

lemma lemma_approx_less_zero:
     "[|(x::hypreal) < 0; x \<notin> Infinitesimal; x @= y|] ==> y < 0"
by (blast dest: Ball_mem_monad_less_zero approx_subset_monad)

theorem approx_hrabs: "(x::hypreal) @= y ==> abs x @= abs y"
by (drule approx_hnorm, simp)

lemma approx_hrabs_zero_cancel: "abs(x::hypreal) @= 0 ==> x @= 0"
apply (cut_tac x = x in hrabs_disj)
apply (auto dest: approx_minus)
done

lemma approx_hrabs_add_Infinitesimal:
  "(e::hypreal) \<in> Infinitesimal ==> abs x @= abs(x+e)"
by (fast intro: approx_hrabs Infinitesimal_add_approx_self)

lemma approx_hrabs_add_minus_Infinitesimal:
     "(e::hypreal) \<in> Infinitesimal ==> abs x @= abs(x + -e)"
by (fast intro: approx_hrabs Infinitesimal_add_minus_approx_self)

lemma hrabs_add_Infinitesimal_cancel:
     "[| (e::hypreal) \<in> Infinitesimal; e' \<in> Infinitesimal;
         abs(x+e) = abs(y+e')|] ==> abs x @= abs y"
apply (drule_tac x = x in approx_hrabs_add_Infinitesimal)
apply (drule_tac x = y in approx_hrabs_add_Infinitesimal)
apply (auto intro: approx_trans2)
done

lemma hrabs_add_minus_Infinitesimal_cancel:
     "[| (e::hypreal) \<in> Infinitesimal; e' \<in> Infinitesimal;
         abs(x + -e) = abs(y + -e')|] ==> abs x @= abs y"
apply (drule_tac x = x in approx_hrabs_add_minus_Infinitesimal)
apply (drule_tac x = y in approx_hrabs_add_minus_Infinitesimal)
apply (auto intro: approx_trans2)
done

subsection {* More @{term HFinite} and @{term Infinitesimal} Theorems *}

(* interesting slightly counterintuitive theorem: necessary
   for proving that an open interval is an NS open set
*)
lemma Infinitesimal_add_hypreal_of_real_less:
     "[| x < y;  u \<in> Infinitesimal |]
      ==> hypreal_of_real x + u < hypreal_of_real y"
apply (simp add: Infinitesimal_def)
apply (drule_tac x = "hypreal_of_real y + -hypreal_of_real x" in bspec, simp)
apply (simp add: abs_less_iff)
done

lemma Infinitesimal_add_hrabs_hypreal_of_real_less:
     "[| x \<in> Infinitesimal; abs(hypreal_of_real r) < hypreal_of_real y |]
      ==> abs (hypreal_of_real r + x) < hypreal_of_real y"
apply (drule_tac x = "hypreal_of_real r" in approx_hrabs_add_Infinitesimal)
apply (drule approx_sym [THEN bex_Infinitesimal_iff2 [THEN iffD2]])
apply (auto intro!: Infinitesimal_add_hypreal_of_real_less
            simp del: star_of_abs
            simp add: star_of_abs [symmetric])
done

lemma Infinitesimal_add_hrabs_hypreal_of_real_less2:
     "[| x \<in> Infinitesimal;  abs(hypreal_of_real r) < hypreal_of_real y |]
      ==> abs (x + hypreal_of_real r) < hypreal_of_real y"
apply (rule add_commute [THEN subst])
apply (erule Infinitesimal_add_hrabs_hypreal_of_real_less, assumption)
done

lemma hypreal_of_real_le_add_Infininitesimal_cancel:
     "[| u \<in> Infinitesimal; v \<in> Infinitesimal;
         hypreal_of_real x + u \<le> hypreal_of_real y + v |]
      ==> hypreal_of_real x \<le> hypreal_of_real y"
apply (simp add: linorder_not_less [symmetric], auto)
apply (drule_tac u = "v-u" in Infinitesimal_add_hypreal_of_real_less)
apply (auto simp add: Infinitesimal_diff)
done

lemma hypreal_of_real_le_add_Infininitesimal_cancel2:
     "[| u \<in> Infinitesimal; v \<in> Infinitesimal;
         hypreal_of_real x + u \<le> hypreal_of_real y + v |]
      ==> x \<le> y"
by (blast intro: star_of_le [THEN iffD1] 
          intro!: hypreal_of_real_le_add_Infininitesimal_cancel)

lemma hypreal_of_real_less_Infinitesimal_le_zero:
    "[| hypreal_of_real x < e; e \<in> Infinitesimal |] ==> hypreal_of_real x \<le> 0"
apply (rule linorder_not_less [THEN iffD1], safe)
apply (drule Infinitesimal_interval)
apply (drule_tac [4] SReal_hypreal_of_real [THEN SReal_Infinitesimal_zero], auto)
done

(*used once, in Lim/NSDERIV_inverse*)
lemma Infinitesimal_add_not_zero:
     "[| h \<in> Infinitesimal; x \<noteq> 0 |] ==> star_of x + h \<noteq> 0"
apply auto
apply (subgoal_tac "h = - star_of x", auto intro: minus_unique [symmetric])
done

lemma Infinitesimal_square_cancel [simp]:
     "(x::hypreal)*x + y*y \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_interval2)
apply (rule_tac [3] zero_le_square, assumption)
apply (auto)
done

lemma HFinite_square_cancel [simp]:
  "(x::hypreal)*x + y*y \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_bounded, assumption)
apply (auto)
done

lemma Infinitesimal_square_cancel2 [simp]:
     "(x::hypreal)*x + y*y \<in> Infinitesimal ==> y*y \<in> Infinitesimal"
apply (rule Infinitesimal_square_cancel)
apply (rule add_commute [THEN subst])
apply (simp (no_asm))
done

lemma HFinite_square_cancel2 [simp]:
  "(x::hypreal)*x + y*y \<in> HFinite ==> y*y \<in> HFinite"
apply (rule HFinite_square_cancel)
apply (rule add_commute [THEN subst])
apply (simp (no_asm))
done

lemma Infinitesimal_sum_square_cancel [simp]:
     "(x::hypreal)*x + y*y + z*z \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_interval2, assumption)
apply (rule_tac [2] zero_le_square, simp)
apply (insert zero_le_square [of y]) 
apply (insert zero_le_square [of z], simp del:zero_le_square)
done

lemma HFinite_sum_square_cancel [simp]:
     "(x::hypreal)*x + y*y + z*z \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_bounded, assumption)
apply (rule_tac [2] zero_le_square)
apply (insert zero_le_square [of y]) 
apply (insert zero_le_square [of z], simp del:zero_le_square)
done

lemma Infinitesimal_sum_square_cancel2 [simp]:
     "(y::hypreal)*y + x*x + z*z \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_sum_square_cancel)
apply (simp add: add_ac)
done

lemma HFinite_sum_square_cancel2 [simp]:
     "(y::hypreal)*y + x*x + z*z \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_sum_square_cancel)
apply (simp add: add_ac)
done

lemma Infinitesimal_sum_square_cancel3 [simp]:
     "(z::hypreal)*z + y*y + x*x \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_sum_square_cancel)
apply (simp add: add_ac)
done

lemma HFinite_sum_square_cancel3 [simp]:
     "(z::hypreal)*z + y*y + x*x \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_sum_square_cancel)
apply (simp add: add_ac)
done

lemma monad_hrabs_less:
     "[| y \<in> monad x; 0 < hypreal_of_real e |]
      ==> abs (y - x) < hypreal_of_real e"
apply (drule mem_monad_approx [THEN approx_sym])
apply (drule bex_Infinitesimal_iff [THEN iffD2])
apply (auto dest!: InfinitesimalD)
done

lemma mem_monad_SReal_HFinite:
     "x \<in> monad (hypreal_of_real  a) ==> x \<in> HFinite"
apply (drule mem_monad_approx [THEN approx_sym])
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])
apply (safe dest!: Infinitesimal_subset_HFinite [THEN subsetD])
apply (erule SReal_hypreal_of_real [THEN SReal_subset_HFinite [THEN subsetD], THEN HFinite_add])
done


subsection{* Theorems about Standard Part*}

lemma st_approx_self: "x \<in> HFinite ==> st x @= x"
apply (simp add: st_def)
apply (frule st_part_Ex, safe)
apply (rule someI2)
apply (auto intro: approx_sym)
done

lemma st_SReal: "x \<in> HFinite ==> st x \<in> Reals"
apply (simp add: st_def)
apply (frule st_part_Ex, safe)
apply (rule someI2)
apply (auto intro: approx_sym)
done

lemma st_HFinite: "x \<in> HFinite ==> st x \<in> HFinite"
by (erule st_SReal [THEN SReal_subset_HFinite [THEN subsetD]])

lemma st_unique: "\<lbrakk>r \<in> \<real>; r \<approx> x\<rbrakk> \<Longrightarrow> st x = r"
apply (frule SReal_subset_HFinite [THEN subsetD])
apply (drule (1) approx_HFinite)
apply (unfold st_def)
apply (rule some_equality)
apply (auto intro: approx_unique_real)
done

lemma st_SReal_eq: "x \<in> Reals ==> st x = x"
apply (erule st_unique)
apply (rule approx_refl)
done

lemma st_hypreal_of_real [simp]: "st (hypreal_of_real x) = hypreal_of_real x"
by (rule SReal_hypreal_of_real [THEN st_SReal_eq])

lemma st_eq_approx: "[| x \<in> HFinite; y \<in> HFinite; st x = st y |] ==> x @= y"
by (auto dest!: st_approx_self elim!: approx_trans3)

lemma approx_st_eq: 
  assumes x: "x \<in> HFinite" and y: "y \<in> HFinite" and xy: "x @= y" 
  shows "st x = st y"
proof -
  have "st x @= x" "st y @= y" "st x \<in> Reals" "st y \<in> Reals"
    by (simp_all add: st_approx_self st_SReal x y)
  with xy show ?thesis
    by (fast elim: approx_trans approx_trans2 SReal_approx_iff [THEN iffD1])
qed

lemma st_eq_approx_iff:
     "[| x \<in> HFinite; y \<in> HFinite|]
                   ==> (x @= y) = (st x = st y)"
by (blast intro: approx_st_eq st_eq_approx)

lemma st_Infinitesimal_add_SReal:
     "[| x \<in> Reals; e \<in> Infinitesimal |] ==> st(x + e) = x"
apply (erule st_unique)
apply (erule Infinitesimal_add_approx_self)
done

lemma st_Infinitesimal_add_SReal2:
     "[| x \<in> Reals; e \<in> Infinitesimal |] ==> st(e + x) = x"
apply (erule st_unique)
apply (erule Infinitesimal_add_approx_self2)
done

lemma HFinite_st_Infinitesimal_add:
     "x \<in> HFinite ==> \<exists>e \<in> Infinitesimal. x = st(x) + e"
by (blast dest!: st_approx_self [THEN approx_sym] bex_Infinitesimal_iff2 [THEN iffD2])

lemma st_add: "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> st (x + y) = st x + st y"
by (simp add: st_unique st_SReal st_approx_self approx_add)

lemma st_number_of [simp]: "st (number_of w) = number_of w"
by (rule Reals_number_of [THEN st_SReal_eq])

lemma st_0 [simp]: "st 0 = 0"
by (simp add: st_SReal_eq)

lemma st_1 [simp]: "st 1 = 1"
by (simp add: st_SReal_eq)

lemma st_minus: "x \<in> HFinite \<Longrightarrow> st (- x) = - st x"
by (simp add: st_unique st_SReal st_approx_self approx_minus)

lemma st_diff: "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> st (x - y) = st x - st y"
by (simp add: st_unique st_SReal st_approx_self approx_diff)

lemma st_mult: "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> st (x * y) = st x * st y"
by (simp add: st_unique st_SReal st_approx_self approx_mult_HFinite)

lemma st_Infinitesimal: "x \<in> Infinitesimal ==> st x = 0"
by (simp add: st_unique mem_infmal_iff)

lemma st_not_Infinitesimal: "st(x) \<noteq> 0 ==> x \<notin> Infinitesimal"
by (fast intro: st_Infinitesimal)

lemma st_inverse:
     "[| x \<in> HFinite; st x \<noteq> 0 |]
      ==> st(inverse x) = inverse (st x)"
apply (rule_tac c1 = "st x" in hypreal_mult_left_cancel [THEN iffD1])
apply (auto simp add: st_mult [symmetric] st_not_Infinitesimal HFinite_inverse)
apply (subst right_inverse, auto)
done

lemma st_divide [simp]:
     "[| x \<in> HFinite; y \<in> HFinite; st y \<noteq> 0 |]
      ==> st(x/y) = (st x) / (st y)"
by (simp add: divide_inverse st_mult st_not_Infinitesimal HFinite_inverse st_inverse)

lemma st_idempotent [simp]: "x \<in> HFinite ==> st(st(x)) = st(x)"
by (blast intro: st_HFinite st_approx_self approx_st_eq)

lemma Infinitesimal_add_st_less:
     "[| x \<in> HFinite; y \<in> HFinite; u \<in> Infinitesimal; st x < st y |] 
      ==> st x + u < st y"
apply (drule st_SReal)+
apply (auto intro!: Infinitesimal_add_hypreal_of_real_less simp add: SReal_iff)
done

lemma Infinitesimal_add_st_le_cancel:
     "[| x \<in> HFinite; y \<in> HFinite;
         u \<in> Infinitesimal; st x \<le> st y + u
      |] ==> st x \<le> st y"
apply (simp add: linorder_not_less [symmetric])
apply (auto dest: Infinitesimal_add_st_less)
done

lemma st_le: "[| x \<in> HFinite; y \<in> HFinite; x \<le> y |] ==> st(x) \<le> st(y)"
apply (frule HFinite_st_Infinitesimal_add)
apply (rotate_tac 1)
apply (frule HFinite_st_Infinitesimal_add, safe)
apply (rule Infinitesimal_add_st_le_cancel)
apply (rule_tac [3] x = ea and y = e in Infinitesimal_diff)
apply (auto simp add: add_assoc [symmetric])
done

lemma st_zero_le: "[| 0 \<le> x;  x \<in> HFinite |] ==> 0 \<le> st x"
apply (subst st_0 [symmetric])
apply (rule st_le, auto)
done

lemma st_zero_ge: "[| x \<le> 0;  x \<in> HFinite |] ==> st x \<le> 0"
apply (subst st_0 [symmetric])
apply (rule st_le, auto)
done

lemma st_hrabs: "x \<in> HFinite ==> abs(st x) = st(abs x)"
apply (simp add: linorder_not_le st_zero_le abs_if st_minus
   linorder_not_less)
apply (auto dest!: st_zero_ge [OF order_less_imp_le]) 
done



subsection {* Alternative Definitions using Free Ultrafilter *}

subsubsection {* @{term HFinite} *}

lemma HFinite_FreeUltrafilterNat:
    "star_n X \<in> HFinite 
     ==> \<exists>u. {n. norm (X n) < u} \<in> FreeUltrafilterNat"
apply (auto simp add: HFinite_def SReal_def)
apply (rule_tac x=r in exI)
apply (simp add: hnorm_def star_of_def starfun_star_n)
apply (simp add: star_less_def starP2_star_n)
done

lemma FreeUltrafilterNat_HFinite:
     "\<exists>u. {n. norm (X n) < u} \<in> FreeUltrafilterNat
       ==>  star_n X \<in> HFinite"
apply (auto simp add: HFinite_def mem_Rep_star_iff)
apply (rule_tac x="star_of u" in bexI)
apply (simp add: hnorm_def starfun_star_n star_of_def)
apply (simp add: star_less_def starP2_star_n)
apply (simp add: SReal_def)
done

lemma HFinite_FreeUltrafilterNat_iff:
     "(star_n X \<in> HFinite) = (\<exists>u. {n. norm (X n) < u} \<in> FreeUltrafilterNat)"
by (blast intro!: HFinite_FreeUltrafilterNat FreeUltrafilterNat_HFinite)

subsubsection {* @{term HInfinite} *}

lemma lemma_Compl_eq: "- {n. u < norm (xa n)} = {n. norm (xa n) \<le> u}"
by auto

lemma lemma_Compl_eq2: "- {n. norm (xa n) < u} = {n. u \<le> norm (xa n)}"
by auto

lemma lemma_Int_eq1:
     "{n. norm (xa n) \<le> u} Int {n. u \<le> norm (xa n)}
          = {n. norm(xa n) = u}"
by auto

lemma lemma_FreeUltrafilterNat_one:
     "{n. norm (xa n) = u} \<le> {n. norm (xa n) < u + (1::real)}"
by auto

(*-------------------------------------
  Exclude this type of sets from free
  ultrafilter for Infinite numbers!
 -------------------------------------*)
lemma FreeUltrafilterNat_const_Finite:
     "{n. norm (X n) = u} \<in> FreeUltrafilterNat ==> star_n X \<in> HFinite"
apply (rule FreeUltrafilterNat_HFinite)
apply (rule_tac x = "u + 1" in exI)
apply (erule ultra, simp)
done

lemma HInfinite_FreeUltrafilterNat:
     "star_n X \<in> HInfinite ==> \<forall>u. {n. u < norm (X n)} \<in> FreeUltrafilterNat"
apply (drule HInfinite_HFinite_iff [THEN iffD1])
apply (simp add: HFinite_FreeUltrafilterNat_iff)
apply (rule allI, drule_tac x="u + 1" in spec)
apply (drule FreeUltrafilterNat.not_memD)
apply (simp add: Collect_neg_eq [symmetric] linorder_not_less)
apply (erule ultra, simp)
done

lemma lemma_Int_HI:
     "{n. norm (Xa n) < u} Int {n. X n = Xa n} \<subseteq> {n. norm (X n) < (u::real)}"
by auto

lemma lemma_Int_HIa: "{n. u < norm (X n)} Int {n. norm (X n) < u} = {}"
by (auto intro: order_less_asym)

lemma FreeUltrafilterNat_HInfinite:
     "\<forall>u. {n. u < norm (X n)} \<in> FreeUltrafilterNat ==> star_n X \<in> HInfinite"
apply (rule HInfinite_HFinite_iff [THEN iffD2])
apply (safe, drule HFinite_FreeUltrafilterNat, safe)
apply (drule_tac x = u in spec)
apply (drule (1) FreeUltrafilterNat.Int)
apply (simp add: Collect_conj_eq [symmetric])
apply (subgoal_tac "\<forall>n. \<not> (norm (X n) < u \<and> u < norm (X n))", auto)
done

lemma HInfinite_FreeUltrafilterNat_iff:
     "(star_n X \<in> HInfinite) = (\<forall>u. {n. u < norm (X n)} \<in> FreeUltrafilterNat)"
by (blast intro!: HInfinite_FreeUltrafilterNat FreeUltrafilterNat_HInfinite)

subsubsection {* @{term Infinitesimal} *}

lemma ball_SReal_eq: "(\<forall>x::hypreal \<in> Reals. P x) = (\<forall>x::real. P (star_of x))"
by (unfold SReal_def, auto)

lemma Infinitesimal_FreeUltrafilterNat:
     "star_n X \<in> Infinitesimal ==> \<forall>u>0. {n. norm (X n) < u} \<in> \<U>"
apply (simp add: Infinitesimal_def ball_SReal_eq)
apply (simp add: hnorm_def starfun_star_n star_of_def)
apply (simp add: star_less_def starP2_star_n)
done

lemma FreeUltrafilterNat_Infinitesimal:
     "\<forall>u>0. {n. norm (X n) < u} \<in> \<U> ==> star_n X \<in> Infinitesimal"
apply (simp add: Infinitesimal_def ball_SReal_eq)
apply (simp add: hnorm_def starfun_star_n star_of_def)
apply (simp add: star_less_def starP2_star_n)
done

lemma Infinitesimal_FreeUltrafilterNat_iff:
     "(star_n X \<in> Infinitesimal) = (\<forall>u>0. {n. norm (X n) < u} \<in> \<U>)"
by (blast intro!: Infinitesimal_FreeUltrafilterNat FreeUltrafilterNat_Infinitesimal)

(*------------------------------------------------------------------------
         Infinitesimals as smaller than 1/n for all n::nat (> 0)
 ------------------------------------------------------------------------*)

lemma lemma_Infinitesimal:
     "(\<forall>r. 0 < r --> x < r) = (\<forall>n. x < inverse(real (Suc n)))"
apply (auto simp add: real_of_nat_Suc_gt_zero)
apply (blast dest!: reals_Archimedean intro: order_less_trans)
done

lemma lemma_Infinitesimal2:
     "(\<forall>r \<in> Reals. 0 < r --> x < r) =
      (\<forall>n. x < inverse(hypreal_of_nat (Suc n)))"
apply safe
apply (drule_tac x = "inverse (hypreal_of_real (real (Suc n))) " in bspec)
apply (simp (no_asm_use))
apply (rule real_of_nat_Suc_gt_zero [THEN positive_imp_inverse_positive, THEN star_of_less [THEN iffD2], THEN [2] impE])
prefer 2 apply assumption
apply (simp add: real_of_nat_def)
apply (auto dest!: reals_Archimedean simp add: SReal_iff)
apply (drule star_of_less [THEN iffD2])
apply (simp add: real_of_nat_def)
apply (blast intro: order_less_trans)
done


lemma Infinitesimal_hypreal_of_nat_iff:
     "Infinitesimal = {x. \<forall>n. hnorm x < inverse (hypreal_of_nat (Suc n))}"
apply (simp add: Infinitesimal_def)
apply (auto simp add: lemma_Infinitesimal2)
done


subsection{*Proof that @{term omega} is an infinite number*}

text{*It will follow that epsilon is an infinitesimal number.*}

lemma Suc_Un_eq: "{n. n < Suc m} = {n. n < m} Un {n. n = m}"
by (auto simp add: less_Suc_eq)

(*-------------------------------------------
  Prove that any segment is finite and
  hence cannot belong to FreeUltrafilterNat
 -------------------------------------------*)
lemma finite_nat_segment: "finite {n::nat. n < m}"
apply (induct "m")
apply (auto simp add: Suc_Un_eq)
done

lemma finite_real_of_nat_segment: "finite {n::nat. real n < real (m::nat)}"
by (auto intro: finite_nat_segment)

lemma finite_real_of_nat_less_real: "finite {n::nat. real n < u}"
apply (cut_tac x = u in reals_Archimedean2, safe)
apply (rule finite_real_of_nat_segment [THEN [2] finite_subset])
apply (auto dest: order_less_trans)
done

lemma lemma_real_le_Un_eq:
     "{n. f n \<le> u} = {n. f n < u} Un {n. u = (f n :: real)}"
by (auto dest: order_le_imp_less_or_eq simp add: order_less_imp_le)

lemma finite_real_of_nat_le_real: "finite {n::nat. real n \<le> u}"
by (auto simp add: lemma_real_le_Un_eq lemma_finite_omega_set finite_real_of_nat_less_real)

lemma finite_rabs_real_of_nat_le_real: "finite {n::nat. abs(real n) \<le> u}"
apply (simp (no_asm) add: real_of_nat_Suc_gt_zero finite_real_of_nat_le_real)
done

lemma rabs_real_of_nat_le_real_FreeUltrafilterNat:
     "{n. abs(real n) \<le> u} \<notin> FreeUltrafilterNat"
by (blast intro!: FreeUltrafilterNat.finite finite_rabs_real_of_nat_le_real)

lemma FreeUltrafilterNat_nat_gt_real: "{n. u < real n} \<in> FreeUltrafilterNat"
apply (rule ccontr, drule FreeUltrafilterNat.not_memD)
apply (subgoal_tac "- {n::nat. u < real n} = {n. real n \<le> u}")
prefer 2 apply force
apply (simp add: finite_real_of_nat_le_real [THEN FreeUltrafilterNat.finite])
done

(*--------------------------------------------------------------
 The complement of {n. abs(real n) \<le> u} =
 {n. u < abs (real n)} is in FreeUltrafilterNat
 by property of (free) ultrafilters
 --------------------------------------------------------------*)

lemma Compl_real_le_eq: "- {n::nat. real n \<le> u} = {n. u < real n}"
by (auto dest!: order_le_less_trans simp add: linorder_not_le)

text{*@{term omega} is a member of @{term HInfinite}*}

lemma FreeUltrafilterNat_omega: "{n. u < real n} \<in> FreeUltrafilterNat"
apply (cut_tac u = u in rabs_real_of_nat_le_real_FreeUltrafilterNat)
apply (auto dest: FreeUltrafilterNat.not_memD simp add: Compl_real_le_eq)
done

theorem HInfinite_omega [simp]: "omega \<in> HInfinite"
apply (simp add: omega_def)
apply (rule FreeUltrafilterNat_HInfinite)
apply (simp (no_asm) add: real_norm_def real_of_nat_Suc diff_less_eq [symmetric] FreeUltrafilterNat_omega)
done

(*-----------------------------------------------
       Epsilon is a member of Infinitesimal
 -----------------------------------------------*)

lemma Infinitesimal_epsilon [simp]: "epsilon \<in> Infinitesimal"
by (auto intro!: HInfinite_inverse_Infinitesimal HInfinite_omega simp add: hypreal_epsilon_inverse_omega)

lemma HFinite_epsilon [simp]: "epsilon \<in> HFinite"
by (auto intro: Infinitesimal_subset_HFinite [THEN subsetD])

lemma epsilon_approx_zero [simp]: "epsilon @= 0"
apply (simp (no_asm) add: mem_infmal_iff [symmetric])
done

(*------------------------------------------------------------------------
  Needed for proof that we define a hyperreal [<X(n)] @= hypreal_of_real a given
  that \<forall>n. |X n - a| < 1/n. Used in proof of NSLIM => LIM.
 -----------------------------------------------------------------------*)

lemma real_of_nat_less_inverse_iff:
     "0 < u  ==> (u < inverse (real(Suc n))) = (real(Suc n) < inverse u)"
apply (simp add: inverse_eq_divide)
apply (subst pos_less_divide_eq, assumption)
apply (subst pos_less_divide_eq)
 apply (simp add: real_of_nat_Suc_gt_zero)
apply (simp add: mult_commute)
done

lemma finite_inverse_real_of_posnat_gt_real:
     "0 < u ==> finite {n. u < inverse(real(Suc n))}"
apply (simp (no_asm_simp) add: real_of_nat_less_inverse_iff)
apply (simp (no_asm_simp) add: real_of_nat_Suc less_diff_eq [symmetric])
apply (rule finite_real_of_nat_less_real)
done

lemma lemma_real_le_Un_eq2:
     "{n. u \<le> inverse(real(Suc n))} =
     {n. u < inverse(real(Suc n))} Un {n. u = inverse(real(Suc n))}"
apply (auto dest: order_le_imp_less_or_eq simp add: order_less_imp_le)
done

lemma real_of_nat_inverse_eq_iff:
     "(u = inverse (real(Suc n))) = (real(Suc n) = inverse u)"
by (auto simp add: real_of_nat_Suc_gt_zero less_imp_neq [THEN not_sym])

lemma lemma_finite_omega_set2: "finite {n::nat. u = inverse(real(Suc n))}"
apply (simp (no_asm_simp) add: real_of_nat_inverse_eq_iff)
apply (cut_tac x = "inverse u - 1" in lemma_finite_omega_set)
apply (simp add: real_of_nat_Suc diff_eq_eq [symmetric] eq_commute)
done

lemma finite_inverse_real_of_posnat_ge_real:
     "0 < u ==> finite {n. u \<le> inverse(real(Suc n))}"
by (auto simp add: lemma_real_le_Un_eq2 lemma_finite_omega_set2 finite_inverse_real_of_posnat_gt_real)

lemma inverse_real_of_posnat_ge_real_FreeUltrafilterNat:
     "0 < u ==> {n. u \<le> inverse(real(Suc n))} \<notin> FreeUltrafilterNat"
by (blast intro!: FreeUltrafilterNat.finite finite_inverse_real_of_posnat_ge_real)

(*--------------------------------------------------------------
    The complement of  {n. u \<le> inverse(real(Suc n))} =
    {n. inverse(real(Suc n)) < u} is in FreeUltrafilterNat
    by property of (free) ultrafilters
 --------------------------------------------------------------*)
lemma Compl_le_inverse_eq:
     "- {n. u \<le> inverse(real(Suc n))} =
      {n. inverse(real(Suc n)) < u}"
apply (auto dest!: order_le_less_trans simp add: linorder_not_le)
done

lemma FreeUltrafilterNat_inverse_real_of_posnat:
     "0 < u ==>
      {n. inverse(real(Suc n)) < u} \<in> FreeUltrafilterNat"
apply (cut_tac u = u in inverse_real_of_posnat_ge_real_FreeUltrafilterNat)
apply (auto dest: FreeUltrafilterNat.not_memD simp add: Compl_le_inverse_eq)
done

text{* Example of an hypersequence (i.e. an extended standard sequence)
   whose term with an hypernatural suffix is an infinitesimal i.e.
   the whn'nth term of the hypersequence is a member of Infinitesimal*}

lemma SEQ_Infinitesimal:
      "( *f* (%n::nat. inverse(real(Suc n)))) whn : Infinitesimal"
apply (simp add: hypnat_omega_def starfun_star_n star_n_inverse)
apply (simp add: Infinitesimal_FreeUltrafilterNat_iff)
apply (simp add: real_of_nat_Suc_gt_zero FreeUltrafilterNat_inverse_real_of_posnat)
done

text{* Example where we get a hyperreal from a real sequence
      for which a particular property holds. The theorem is
      used in proofs about equivalence of nonstandard and
      standard neighbourhoods. Also used for equivalence of
      nonstandard ans standard definitions of pointwise
      limit.*}

(*-----------------------------------------------------
    |X(n) - x| < 1/n ==> [<X n>] - hypreal_of_real x| \<in> Infinitesimal
 -----------------------------------------------------*)
lemma real_seq_to_hypreal_Infinitesimal:
     "\<forall>n. norm(X n - x) < inverse(real(Suc n))
     ==> star_n X - star_of x \<in> Infinitesimal"
apply (auto intro!: bexI dest: FreeUltrafilterNat_inverse_real_of_posnat FreeUltrafilterNat.Int intro: order_less_trans FreeUltrafilterNat.subset simp add: star_n_diff star_of_def Infinitesimal_FreeUltrafilterNat_iff star_n_inverse)
done

lemma real_seq_to_hypreal_approx:
     "\<forall>n. norm(X n - x) < inverse(real(Suc n))
      ==> star_n X @= star_of x"
apply (subst approx_minus_iff)
apply (rule mem_infmal_iff [THEN subst])
apply (erule real_seq_to_hypreal_Infinitesimal)
done

lemma real_seq_to_hypreal_approx2:
     "\<forall>n. norm(x - X n) < inverse(real(Suc n))
               ==> star_n X @= star_of x"
apply (rule real_seq_to_hypreal_approx)
apply (subst norm_minus_cancel [symmetric])
apply (simp del: norm_minus_cancel)
done

lemma real_seq_to_hypreal_Infinitesimal2:
     "\<forall>n. norm(X n - Y n) < inverse(real(Suc n))
      ==> star_n X - star_n Y \<in> Infinitesimal"
by (auto intro!: bexI
         dest: FreeUltrafilterNat_inverse_real_of_posnat 
               FreeUltrafilterNat.Int
         intro: order_less_trans FreeUltrafilterNat.subset 
         simp add: Infinitesimal_FreeUltrafilterNat_iff star_n_diff 
                   star_n_inverse)

end
