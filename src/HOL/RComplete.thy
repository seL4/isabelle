(*  Title:      HOL/RComplete.thy
    Author:     Jacques D. Fleuriot, University of Edinburgh
    Author:     Larry Paulson, University of Cambridge
    Author:     Jeremy Avigad, Carnegie Mellon University
    Author:     Florian Zuleger, Johannes Hoelzl, and Simon Funke, TU Muenchen
*)

header {* Completeness of the Reals; Floor and Ceiling Functions *}

theory RComplete
imports Lubs RealDef
begin

lemma real_sum_of_halves: "x/2 + x/2 = (x::real)"
  by simp

lemma abs_diff_less_iff:
  "(\<bar>x - a\<bar> < (r::'a::linordered_idom)) = (a - r < x \<and> x < a + r)"
  by auto

subsection {* Completeness of Positive Reals *}

text {*
  Supremum property for the set of positive reals

  Let @{text "P"} be a non-empty set of positive reals, with an upper
  bound @{text "y"}.  Then @{text "P"} has a least upper bound
  (written @{text "S"}).

  FIXME: Can the premise be weakened to @{text "\<forall>x \<in> P. x\<le> y"}?
*}

text {* Only used in HOL/Import/HOL4Compat.thy; delete? *}

lemma posreal_complete:
  fixes P :: "real set"
  assumes not_empty_P: "\<exists>x. x \<in> P"
    and upper_bound_Ex: "\<exists>y. \<forall>x \<in> P. x<y"
  shows "\<exists>S. \<forall>y. (\<exists>x \<in> P. y < x) = (y < S)"
proof -
  from upper_bound_Ex have "\<exists>z. \<forall>x\<in>P. x \<le> z"
    by (auto intro: less_imp_le)
  from complete_real [OF not_empty_P this] obtain S
  where S1: "\<And>x. x \<in> P \<Longrightarrow> x \<le> S" and S2: "\<And>z. \<forall>x\<in>P. x \<le> z \<Longrightarrow> S \<le> z" by fast
  have "\<forall>y. (\<exists>x \<in> P. y < x) = (y < S)"
  proof
    fix y show "(\<exists>x\<in>P. y < x) = (y < S)"
      apply (cases "\<exists>x\<in>P. y < x", simp_all)
      apply (clarify, drule S1, simp)
      apply (simp add: not_less S2)
      done
  qed
  thus ?thesis ..
qed

text {*
  \medskip Completeness properties using @{text "isUb"}, @{text "isLub"} etc.
*}

lemma real_isLub_unique: "[| isLub R S x; isLub R S y |] ==> x = (y::real)"
  apply (frule isLub_isUb)
  apply (frule_tac x = y in isLub_isUb)
  apply (blast intro!: order_antisym dest!: isLub_le_isUb)
  done


text {*
  \medskip reals Completeness (again!)
*}

lemma reals_complete:
  assumes notempty_S: "\<exists>X. X \<in> S"
    and exists_Ub: "\<exists>Y. isUb (UNIV::real set) S Y"
  shows "\<exists>t. isLub (UNIV :: real set) S t"
proof -
  from assms have "\<exists>X. X \<in> S" and "\<exists>Y. \<forall>x\<in>S. x \<le> Y"
    unfolding isUb_def setle_def by simp_all
  from complete_real [OF this] show ?thesis
    by (simp add: isLub_def leastP_def isUb_def setle_def setge_def)
qed


subsection {* The Archimedean Property of the Reals *}

theorem reals_Archimedean:
  assumes x_pos: "0 < x"
  shows "\<exists>n. inverse (real (Suc n)) < x"
  unfolding real_of_nat_def using x_pos
  by (rule ex_inverse_of_nat_Suc_less)

lemma reals_Archimedean2: "\<exists>n. (x::real) < real (n::nat)"
  unfolding real_of_nat_def by (rule ex_less_of_nat)

lemma reals_Archimedean3:
  assumes x_greater_zero: "0 < x"
  shows "\<forall>(y::real). \<exists>(n::nat). y < real n * x"
  unfolding real_of_nat_def using `0 < x`
  by (auto intro: ex_less_of_nat_mult)


subsection{*Density of the Rational Reals in the Reals*}

text{* This density proof is due to Stefan Richter and was ported by TN.  The
original source is \emph{Real Analysis} by H.L. Royden.
It employs the Archimedean property of the reals. *}

lemma Rats_dense_in_real:
  fixes x :: real
  assumes "x < y" shows "\<exists>r\<in>\<rat>. x < r \<and> r < y"
proof -
  from `x<y` have "0 < y-x" by simp
  with reals_Archimedean obtain q::nat 
    where q: "inverse (real q) < y-x" and "0 < q" by auto
  def p \<equiv> "ceiling (y * real q) - 1"
  def r \<equiv> "of_int p / real q"
  from q have "x < y - inverse (real q)" by simp
  also have "y - inverse (real q) \<le> r"
    unfolding r_def p_def
    by (simp add: le_divide_eq left_diff_distrib le_of_int_ceiling `0 < q`)
  finally have "x < r" .
  moreover have "r < y"
    unfolding r_def p_def
    by (simp add: divide_less_eq diff_less_eq `0 < q`
      less_ceiling_iff [symmetric])
  moreover from r_def have "r \<in> \<rat>" by simp
  ultimately show ?thesis by fast
qed


subsection{*Floor and Ceiling Functions from the Reals to the Integers*}

(* FIXME: theorems for negative numerals *)
lemma numeral_less_real_of_int_iff [simp]:
     "((numeral n) < real (m::int)) = (numeral n < m)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma numeral_less_real_of_int_iff2 [simp]:
     "(real (m::int) < (numeral n)) = (m < numeral n)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma numeral_le_real_of_int_iff [simp]:
     "((numeral n) \<le> real (m::int)) = (numeral n \<le> m)"
by (simp add: linorder_not_less [symmetric])

lemma numeral_le_real_of_int_iff2 [simp]:
     "(real (m::int) \<le> (numeral n)) = (m \<le> numeral n)"
by (simp add: linorder_not_less [symmetric])

lemma floor_real_of_nat [simp]: "floor (real (n::nat)) = int n"
unfolding real_of_nat_def by simp

lemma floor_minus_real_of_nat [simp]: "floor (- real (n::nat)) = - int n"
unfolding real_of_nat_def by (simp add: floor_minus)

lemma floor_real_of_int [simp]: "floor (real (n::int)) = n"
unfolding real_of_int_def by simp

lemma floor_minus_real_of_int [simp]: "floor (- real (n::int)) = - n"
unfolding real_of_int_def by (simp add: floor_minus)

lemma real_lb_ub_int: " \<exists>n::int. real n \<le> r & r < real (n+1)"
unfolding real_of_int_def by (rule floor_exists)

lemma lemma_floor:
  assumes a1: "real m \<le> r" and a2: "r < real n + 1"
  shows "m \<le> (n::int)"
proof -
  have "real m < real n + 1" using a1 a2 by (rule order_le_less_trans)
  also have "... = real (n + 1)" by simp
  finally have "m < n + 1" by (simp only: real_of_int_less_iff)
  thus ?thesis by arith
qed

lemma real_of_int_floor_le [simp]: "real (floor r) \<le> r"
unfolding real_of_int_def by (rule of_int_floor_le)

lemma lemma_floor2: "real n < real (x::int) + 1 ==> n \<le> x"
by (auto intro: lemma_floor)

lemma real_of_int_floor_cancel [simp]:
    "(real (floor x) = x) = (\<exists>n::int. x = real n)"
  using floor_real_of_int by metis

lemma floor_eq: "[| real n < x; x < real n + 1 |] ==> floor x = n"
  unfolding real_of_int_def using floor_unique [of n x] by simp

lemma floor_eq2: "[| real n \<le> x; x < real n + 1 |] ==> floor x = n"
  unfolding real_of_int_def by (rule floor_unique)

lemma floor_eq3: "[| real n < x; x < real (Suc n) |] ==> nat(floor x) = n"
apply (rule inj_int [THEN injD])
apply (simp add: real_of_nat_Suc)
apply (simp add: real_of_nat_Suc floor_eq floor_eq [where n = "int n"])
done

lemma floor_eq4: "[| real n \<le> x; x < real (Suc n) |] ==> nat(floor x) = n"
apply (drule order_le_imp_less_or_eq)
apply (auto intro: floor_eq3)
done

lemma real_of_int_floor_ge_diff_one [simp]: "r - 1 \<le> real(floor r)"
  unfolding real_of_int_def using floor_correct [of r] by simp

lemma real_of_int_floor_gt_diff_one [simp]: "r - 1 < real(floor r)"
  unfolding real_of_int_def using floor_correct [of r] by simp

lemma real_of_int_floor_add_one_ge [simp]: "r \<le> real(floor r) + 1"
  unfolding real_of_int_def using floor_correct [of r] by simp

lemma real_of_int_floor_add_one_gt [simp]: "r < real(floor r) + 1"
  unfolding real_of_int_def using floor_correct [of r] by simp

lemma le_floor: "real a <= x ==> a <= floor x"
  unfolding real_of_int_def by (simp add: le_floor_iff)

lemma real_le_floor: "a <= floor x ==> real a <= x"
  unfolding real_of_int_def by (simp add: le_floor_iff)

lemma le_floor_eq: "(a <= floor x) = (real a <= x)"
  unfolding real_of_int_def by (rule le_floor_iff)

lemma floor_less_eq: "(floor x < a) = (x < real a)"
  unfolding real_of_int_def by (rule floor_less_iff)

lemma less_floor_eq: "(a < floor x) = (real a + 1 <= x)"
  unfolding real_of_int_def by (rule less_floor_iff)

lemma floor_le_eq: "(floor x <= a) = (x < real a + 1)"
  unfolding real_of_int_def by (rule floor_le_iff)

lemma floor_add [simp]: "floor (x + real a) = floor x + a"
  unfolding real_of_int_def by (rule floor_add_of_int)

lemma floor_subtract [simp]: "floor (x - real a) = floor x - a"
  unfolding real_of_int_def by (rule floor_diff_of_int)

lemma le_mult_floor:
  assumes "0 \<le> (a :: real)" and "0 \<le> b"
  shows "floor a * floor b \<le> floor (a * b)"
proof -
  have "real (floor a) \<le> a"
    and "real (floor b) \<le> b" by auto
  hence "real (floor a * floor b) \<le> a * b"
    using assms by (auto intro!: mult_mono)
  also have "a * b < real (floor (a * b) + 1)" by auto
  finally show ?thesis unfolding real_of_int_less_iff by simp
qed

lemma ceiling_real_of_nat [simp]: "ceiling (real (n::nat)) = int n"
  unfolding real_of_nat_def by simp

lemma real_of_int_ceiling_ge [simp]: "r \<le> real (ceiling r)"
  unfolding real_of_int_def by (rule le_of_int_ceiling)

lemma ceiling_real_of_int [simp]: "ceiling (real (n::int)) = n"
  unfolding real_of_int_def by simp

lemma real_of_int_ceiling_cancel [simp]:
     "(real (ceiling x) = x) = (\<exists>n::int. x = real n)"
  using ceiling_real_of_int by metis

lemma ceiling_eq: "[| real n < x; x < real n + 1 |] ==> ceiling x = n + 1"
  unfolding real_of_int_def using ceiling_unique [of "n + 1" x] by simp

lemma ceiling_eq2: "[| real n < x; x \<le> real n + 1 |] ==> ceiling x = n + 1"
  unfolding real_of_int_def using ceiling_unique [of "n + 1" x] by simp

lemma ceiling_eq3: "[| real n - 1 < x; x \<le> real n  |] ==> ceiling x = n"
  unfolding real_of_int_def using ceiling_unique [of n x] by simp

lemma real_of_int_ceiling_diff_one_le [simp]: "real (ceiling r) - 1 \<le> r"
  unfolding real_of_int_def using ceiling_correct [of r] by simp

lemma real_of_int_ceiling_le_add_one [simp]: "real (ceiling r) \<le> r + 1"
  unfolding real_of_int_def using ceiling_correct [of r] by simp

lemma ceiling_le: "x <= real a ==> ceiling x <= a"
  unfolding real_of_int_def by (simp add: ceiling_le_iff)

lemma ceiling_le_real: "ceiling x <= a ==> x <= real a"
  unfolding real_of_int_def by (simp add: ceiling_le_iff)

lemma ceiling_le_eq: "(ceiling x <= a) = (x <= real a)"
  unfolding real_of_int_def by (rule ceiling_le_iff)

lemma less_ceiling_eq: "(a < ceiling x) = (real a < x)"
  unfolding real_of_int_def by (rule less_ceiling_iff)

lemma ceiling_less_eq: "(ceiling x < a) = (x <= real a - 1)"
  unfolding real_of_int_def by (rule ceiling_less_iff)

lemma le_ceiling_eq: "(a <= ceiling x) = (real a - 1 < x)"
  unfolding real_of_int_def by (rule le_ceiling_iff)

lemma ceiling_add [simp]: "ceiling (x + real a) = ceiling x + a"
  unfolding real_of_int_def by (rule ceiling_add_of_int)

lemma ceiling_subtract [simp]: "ceiling (x - real a) = ceiling x - a"
  unfolding real_of_int_def by (rule ceiling_diff_of_int)


subsection {* Versions for the natural numbers *}

definition
  natfloor :: "real => nat" where
  "natfloor x = nat(floor x)"

definition
  natceiling :: "real => nat" where
  "natceiling x = nat(ceiling x)"

lemma natfloor_zero [simp]: "natfloor 0 = 0"
  by (unfold natfloor_def, simp)

lemma natfloor_one [simp]: "natfloor 1 = 1"
  by (unfold natfloor_def, simp)

lemma zero_le_natfloor [simp]: "0 <= natfloor x"
  by (unfold natfloor_def, simp)

lemma natfloor_numeral_eq [simp]: "natfloor (numeral n) = numeral n"
  by (unfold natfloor_def, simp)

lemma natfloor_real_of_nat [simp]: "natfloor(real n) = n"
  by (unfold natfloor_def, simp)

lemma real_natfloor_le: "0 <= x ==> real(natfloor x) <= x"
  by (unfold natfloor_def, simp)

lemma natfloor_neg: "x <= 0 ==> natfloor x = 0"
  unfolding natfloor_def by simp

lemma natfloor_mono: "x <= y ==> natfloor x <= natfloor y"
  unfolding natfloor_def by (intro nat_mono floor_mono)

lemma le_natfloor: "real x <= a ==> x <= natfloor a"
  apply (unfold natfloor_def)
  apply (subst nat_int [THEN sym])
  apply (rule nat_mono)
  apply (rule le_floor)
  apply simp
done

lemma natfloor_less_iff: "0 \<le> x \<Longrightarrow> natfloor x < n \<longleftrightarrow> x < real n"
  unfolding natfloor_def real_of_nat_def
  by (simp add: nat_less_iff floor_less_iff)

lemma less_natfloor:
  assumes "0 \<le> x" and "x < real (n :: nat)"
  shows "natfloor x < n"
  using assms by (simp add: natfloor_less_iff)

lemma le_natfloor_eq: "0 <= x ==> (a <= natfloor x) = (real a <= x)"
  apply (rule iffI)
  apply (rule order_trans)
  prefer 2
  apply (erule real_natfloor_le)
  apply (subst real_of_nat_le_iff)
  apply assumption
  apply (erule le_natfloor)
done

lemma le_natfloor_eq_numeral [simp]:
    "~ neg((numeral n)::int) ==> 0 <= x ==>
      (numeral n <= natfloor x) = (numeral n <= x)"
  apply (subst le_natfloor_eq, assumption)
  apply simp
done

lemma le_natfloor_eq_one [simp]: "(1 <= natfloor x) = (1 <= x)"
  apply (case_tac "0 <= x")
  apply (subst le_natfloor_eq, assumption, simp)
  apply (rule iffI)
  apply (subgoal_tac "natfloor x <= natfloor 0")
  apply simp
  apply (rule natfloor_mono)
  apply simp
  apply simp
done

lemma natfloor_eq: "real n <= x ==> x < real n + 1 ==> natfloor x = n"
  unfolding natfloor_def by (simp add: floor_eq2 [where n="int n"])

lemma real_natfloor_add_one_gt: "x < real(natfloor x) + 1"
  apply (case_tac "0 <= x")
  apply (unfold natfloor_def)
  apply simp
  apply simp_all
done

lemma real_natfloor_gt_diff_one: "x - 1 < real(natfloor x)"
using real_natfloor_add_one_gt by (simp add: algebra_simps)

lemma ge_natfloor_plus_one_imp_gt: "natfloor z + 1 <= n ==> z < real n"
  apply (subgoal_tac "z < real(natfloor z) + 1")
  apply arith
  apply (rule real_natfloor_add_one_gt)
done

lemma natfloor_add [simp]: "0 <= x ==> natfloor (x + real a) = natfloor x + a"
  unfolding natfloor_def
  unfolding real_of_int_of_nat_eq [symmetric] floor_add
  by (simp add: nat_add_distrib)

lemma natfloor_add_numeral [simp]:
    "~neg ((numeral n)::int) ==> 0 <= x ==>
      natfloor (x + numeral n) = natfloor x + numeral n"
  by (simp add: natfloor_add [symmetric])

lemma natfloor_add_one: "0 <= x ==> natfloor(x + 1) = natfloor x + 1"
  by (simp add: natfloor_add [symmetric] del: One_nat_def)

lemma natfloor_subtract [simp]:
    "natfloor(x - real a) = natfloor x - a"
  unfolding natfloor_def real_of_int_of_nat_eq [symmetric] floor_subtract
  by simp

lemma natfloor_div_nat:
  assumes "1 <= x" and "y > 0"
  shows "natfloor (x / real y) = natfloor x div y"
proof (rule natfloor_eq)
  have "(natfloor x) div y * y \<le> natfloor x"
    by (rule add_leD1 [where k="natfloor x mod y"], simp)
  thus "real (natfloor x div y) \<le> x / real y"
    using assms by (simp add: le_divide_eq le_natfloor_eq)
  have "natfloor x < (natfloor x) div y * y + y"
    apply (subst mod_div_equality [symmetric])
    apply (rule add_strict_left_mono)
    apply (rule mod_less_divisor)
    apply fact
    done
  thus "x / real y < real (natfloor x div y) + 1"
    using assms
    by (simp add: divide_less_eq natfloor_less_iff left_distrib)
qed

lemma le_mult_natfloor:
  shows "natfloor a * natfloor b \<le> natfloor (a * b)"
  by (cases "0 <= a & 0 <= b")
    (auto simp add: le_natfloor_eq mult_nonneg_nonneg mult_mono' real_natfloor_le natfloor_neg)

lemma natceiling_zero [simp]: "natceiling 0 = 0"
  by (unfold natceiling_def, simp)

lemma natceiling_one [simp]: "natceiling 1 = 1"
  by (unfold natceiling_def, simp)

lemma zero_le_natceiling [simp]: "0 <= natceiling x"
  by (unfold natceiling_def, simp)

lemma natceiling_numeral_eq [simp]: "natceiling (numeral n) = numeral n"
  by (unfold natceiling_def, simp)

lemma natceiling_real_of_nat [simp]: "natceiling(real n) = n"
  by (unfold natceiling_def, simp)

lemma real_natceiling_ge: "x <= real(natceiling x)"
  unfolding natceiling_def by (cases "x < 0", simp_all)

lemma natceiling_neg: "x <= 0 ==> natceiling x = 0"
  unfolding natceiling_def by simp

lemma natceiling_mono: "x <= y ==> natceiling x <= natceiling y"
  unfolding natceiling_def by (intro nat_mono ceiling_mono)

lemma natceiling_le: "x <= real a ==> natceiling x <= a"
  unfolding natceiling_def real_of_nat_def
  by (simp add: nat_le_iff ceiling_le_iff)

lemma natceiling_le_eq: "(natceiling x <= a) = (x <= real a)"
  unfolding natceiling_def real_of_nat_def
  by (simp add: nat_le_iff ceiling_le_iff)

lemma natceiling_le_eq_numeral [simp]:
    "~ neg((numeral n)::int) ==>
      (natceiling x <= numeral n) = (x <= numeral n)"
  by (simp add: natceiling_le_eq)

lemma natceiling_le_eq_one: "(natceiling x <= 1) = (x <= 1)"
  unfolding natceiling_def
  by (simp add: nat_le_iff ceiling_le_iff)

lemma natceiling_eq: "real n < x ==> x <= real n + 1 ==> natceiling x = n + 1"
  unfolding natceiling_def
  by (simp add: ceiling_eq2 [where n="int n"])

lemma natceiling_add [simp]: "0 <= x ==>
    natceiling (x + real a) = natceiling x + a"
  unfolding natceiling_def
  unfolding real_of_int_of_nat_eq [symmetric] ceiling_add
  by (simp add: nat_add_distrib)

lemma natceiling_add_numeral [simp]:
    "~ neg ((numeral n)::int) ==> 0 <= x ==>
      natceiling (x + numeral n) = natceiling x + numeral n"
  by (simp add: natceiling_add [symmetric])

lemma natceiling_add_one: "0 <= x ==> natceiling(x + 1) = natceiling x + 1"
  by (simp add: natceiling_add [symmetric] del: One_nat_def)

lemma natceiling_subtract [simp]: "natceiling(x - real a) = natceiling x - a"
  unfolding natceiling_def real_of_int_of_nat_eq [symmetric] ceiling_subtract
  by simp

subsection {* Exponentiation with floor *}

lemma floor_power:
  assumes "x = real (floor x)"
  shows "floor (x ^ n) = floor x ^ n"
proof -
  have *: "x ^ n = real (floor x ^ n)"
    using assms by (induct n arbitrary: x) simp_all
  show ?thesis unfolding real_of_int_inject[symmetric]
    unfolding * floor_real_of_int ..
qed

lemma natfloor_power:
  assumes "x = real (natfloor x)"
  shows "natfloor (x ^ n) = natfloor x ^ n"
proof -
  from assms have "0 \<le> floor x" by auto
  note assms[unfolded natfloor_def real_nat_eq_real[OF `0 \<le> floor x`]]
  from floor_power[OF this]
  show ?thesis unfolding natfloor_def nat_power_eq[OF `0 \<le> floor x`, symmetric]
    by simp
qed

end
