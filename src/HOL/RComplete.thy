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
  assumes positive_P: "\<forall>x \<in> P. (0::real) < x"
    and not_empty_P: "\<exists>x. x \<in> P"
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
    unfolding isLub_def leastP_def setle_def setge_def Ball_def
      Collect_def mem_def isUb_def UNIV_def by simp
qed

text{*A version of the same theorem without all those predicates!*}
lemma reals_complete2:
  fixes S :: "(real set)"
  assumes "\<exists>y. y\<in>S" and "\<exists>(x::real). \<forall>y\<in>S. y \<le> x"
  shows "\<exists>x. (\<forall>y\<in>S. y \<le> x) & 
               (\<forall>z. ((\<forall>y\<in>S. y \<le> z) --> x \<le> z))"
using assms by (rule complete_real)


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

lemma reals_Archimedean6:
     "0 \<le> r ==> \<exists>(n::nat). real (n - 1) \<le> r & r < real (n)"
unfolding real_of_nat_def
apply (rule exI [where x="nat (floor r + 1)"])
apply (insert floor_correct [of r])
apply (simp add: nat_add_distrib of_nat_nat)
done

lemma reals_Archimedean6a: "0 \<le> r ==> \<exists>n. real (n) \<le> r & r < real (Suc n)"
  by (drule reals_Archimedean6) auto

text {* TODO: delete *}
lemma reals_Archimedean_6b_int:
     "0 \<le> r ==> \<exists>n::int. real n \<le> r & r < real (n+1)"
  unfolding real_of_int_def by (rule floor_exists)

text {* TODO: delete *}
lemma reals_Archimedean_6c_int:
     "r < 0 ==> \<exists>n::int. real n \<le> r & r < real (n+1)"
  unfolding real_of_int_def by (rule floor_exists)


subsection{*Density of the Rational Reals in the Reals*}

text{* This density proof is due to Stefan Richter and was ported by TN.  The
original source is \emph{Real Analysis} by H.L. Royden.
It employs the Archimedean property of the reals. *}

lemma Rats_dense_in_nn_real: fixes x::real
assumes "0\<le>x" and "x<y" shows "\<exists>r \<in> \<rat>.  x<r \<and> r<y"
proof -
  from `x<y` have "0 < y-x" by simp
  with reals_Archimedean obtain q::nat 
    where q: "inverse (real q) < y-x" and "0 < real q" by auto  
  def p \<equiv> "LEAST n.  y \<le> real (Suc n)/real q"  
  from reals_Archimedean2 obtain n::nat where "y * real q < real n" by auto
  with `0 < real q` have ex: "y \<le> real n/real q" (is "?P n")
    by (simp add: pos_less_divide_eq[THEN sym])
  also from assms have "\<not> y \<le> real (0::nat) / real q" by simp
  ultimately have main: "(LEAST n. y \<le> real n/real q) = Suc p"
    by (unfold p_def) (rule Least_Suc)
  also from ex have "?P (LEAST x. ?P x)" by (rule LeastI)
  ultimately have suc: "y \<le> real (Suc p) / real q" by simp
  def r \<equiv> "real p/real q"
  have "x = y-(y-x)" by simp
  also from suc q have "\<dots> < real (Suc p)/real q - inverse (real q)" by arith
  also have "\<dots> = real p / real q"
    by (simp only: inverse_eq_divide diff_minus real_of_nat_Suc 
    minus_divide_left add_divide_distrib[THEN sym]) simp
  finally have "x<r" by (unfold r_def)
  have "p<Suc p" .. also note main[THEN sym]
  finally have "\<not> ?P p"  by (rule not_less_Least)
  hence "r<y" by (simp add: r_def)
  from r_def have "r \<in> \<rat>" by simp
  with `x<r` `r<y` show ?thesis by fast
qed

theorem Rats_dense_in_real: fixes x y :: real
assumes "x<y" shows "\<exists>r \<in> \<rat>.  x<r \<and> r<y"
proof -
  from reals_Archimedean2 obtain n::nat where "-x < real n" by auto
  hence "0 \<le> x + real n" by arith
  also from `x<y` have "x + real n < y + real n" by arith
  ultimately have "\<exists>r \<in> \<rat>. x + real n < r \<and> r < y + real n"
    by(rule Rats_dense_in_nn_real)
  then obtain r where "r \<in> \<rat>" and r2: "x + real n < r" 
    and r3: "r < y + real n"
    by blast
  have "r - real n = r + real (int n)/real (-1::int)" by simp
  also from `r\<in>\<rat>` have "r + real (int n)/real (-1::int) \<in> \<rat>" by simp
  also from r2 have "x < r - real n" by arith
  moreover from r3 have "r - real n < y" by arith
  ultimately show ?thesis by fast
qed


subsection{*Floor and Ceiling Functions from the Reals to the Integers*}

lemma number_of_less_real_of_int_iff [simp]:
     "((number_of n) < real (m::int)) = (number_of n < m)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma number_of_less_real_of_int_iff2 [simp]:
     "(real (m::int) < (number_of n)) = (m < number_of n)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma number_of_le_real_of_int_iff [simp]:
     "((number_of n) \<le> real (m::int)) = (number_of n \<le> m)"
by (simp add: linorder_not_less [symmetric])

lemma number_of_le_real_of_int_iff2 [simp]:
     "(real (m::int) \<le> (number_of n)) = (m \<le> number_of n)"
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

lemma ceiling_floor [simp]: "ceiling (real (floor r)) = floor r"
  unfolding real_of_int_def by simp

lemma floor_ceiling [simp]: "floor (real (ceiling r)) = ceiling r"
  unfolding real_of_int_def by simp

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

lemma natfloor_number_of_eq [simp]: "natfloor (number_of n) = number_of n"
  by (unfold natfloor_def, simp)

lemma natfloor_real_of_nat [simp]: "natfloor(real n) = n"
  by (unfold natfloor_def, simp)

lemma real_natfloor_le: "0 <= x ==> real(natfloor x) <= x"
  by (unfold natfloor_def, simp)

lemma natfloor_neg: "x <= 0 ==> natfloor x = 0"
  apply (unfold natfloor_def)
  apply (subgoal_tac "floor x <= floor 0")
  apply simp
  apply (erule floor_mono)
done

lemma natfloor_mono: "x <= y ==> natfloor x <= natfloor y"
  apply (case_tac "0 <= x")
  apply (subst natfloor_def)+
  apply (subst nat_le_eq_zle)
  apply force
  apply (erule floor_mono)
  apply (subst natfloor_neg)
  apply simp
  apply simp
done

lemma le_natfloor: "real x <= a ==> x <= natfloor a"
  apply (unfold natfloor_def)
  apply (subst nat_int [THEN sym])
  apply (subst nat_le_eq_zle)
  apply simp
  apply (rule le_floor)
  apply simp
done

lemma less_natfloor:
  assumes "0 \<le> x" and "x < real (n :: nat)"
  shows "natfloor x < n"
proof (rule ccontr)
  assume "\<not> ?thesis" hence *: "n \<le> natfloor x" by simp
  note assms(2)
  also have "real n \<le> real (natfloor x)"
    using * unfolding real_of_nat_le_iff .
  finally have "x < real (natfloor x)" .
  with real_natfloor_le[OF assms(1)]
  show False by auto
qed

lemma le_natfloor_eq: "0 <= x ==> (a <= natfloor x) = (real a <= x)"
  apply (rule iffI)
  apply (rule order_trans)
  prefer 2
  apply (erule real_natfloor_le)
  apply (subst real_of_nat_le_iff)
  apply assumption
  apply (erule le_natfloor)
done

lemma le_natfloor_eq_number_of [simp]:
    "~ neg((number_of n)::int) ==> 0 <= x ==>
      (number_of n <= natfloor x) = (number_of n <= x)"
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
  apply (unfold natfloor_def)
  apply (subst (2) nat_int [THEN sym])
  apply (subst eq_nat_nat_iff)
  apply simp
  apply simp
  apply (rule floor_eq2)
  apply auto
done

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
  apply (unfold natfloor_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply (simp add: nat_add_distrib del: real_of_int_of_nat_eq)
  apply simp
done

lemma natfloor_add_number_of [simp]:
    "~neg ((number_of n)::int) ==> 0 <= x ==>
      natfloor (x + number_of n) = natfloor x + number_of n"
  apply (subst natfloor_add [THEN sym])
  apply simp_all
done

lemma natfloor_add_one: "0 <= x ==> natfloor(x + 1) = natfloor x + 1"
  apply (subst natfloor_add [THEN sym])
  apply assumption
  apply simp
done

lemma natfloor_subtract [simp]: "real a <= x ==>
    natfloor(x - real a) = natfloor x - a"
  apply (unfold natfloor_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply (simp del: real_of_int_of_nat_eq)
  apply simp
done

lemma natfloor_div_nat: "1 <= x ==> y > 0 ==>
  natfloor (x / real y) = natfloor x div y"
proof -
  assume "1 <= (x::real)" and "(y::nat) > 0"
  have "natfloor x = (natfloor x) div y * y + (natfloor x) mod y"
    by simp
  then have a: "real(natfloor x) = real ((natfloor x) div y) * real y +
    real((natfloor x) mod y)"
    by (simp only: real_of_nat_add [THEN sym] real_of_nat_mult [THEN sym])
  have "x = real(natfloor x) + (x - real(natfloor x))"
    by simp
  then have "x = real ((natfloor x) div y) * real y +
      real((natfloor x) mod y) + (x - real(natfloor x))"
    by (simp add: a)
  then have "x / real y = ... / real y"
    by simp
  also have "... = real((natfloor x) div y) + real((natfloor x) mod y) /
    real y + (x - real(natfloor x)) / real y"
    by (auto simp add: algebra_simps add_divide_distrib
      diff_divide_distrib prems)
  finally have "natfloor (x / real y) = natfloor(...)" by simp
  also have "... = natfloor(real((natfloor x) mod y) /
    real y + (x - real(natfloor x)) / real y + real((natfloor x) div y))"
    by (simp add: add_ac)
  also have "... = natfloor(real((natfloor x) mod y) /
    real y + (x - real(natfloor x)) / real y) + (natfloor x) div y"
    apply (rule natfloor_add)
    apply (rule add_nonneg_nonneg)
    apply (rule divide_nonneg_pos)
    apply simp
    apply (simp add: prems)
    apply (rule divide_nonneg_pos)
    apply (simp add: algebra_simps)
    apply (rule real_natfloor_le)
    apply (insert prems, auto)
    done
  also have "natfloor(real((natfloor x) mod y) /
    real y + (x - real(natfloor x)) / real y) = 0"
    apply (rule natfloor_eq)
    apply simp
    apply (rule add_nonneg_nonneg)
    apply (rule divide_nonneg_pos)
    apply force
    apply (force simp add: prems)
    apply (rule divide_nonneg_pos)
    apply (simp add: algebra_simps)
    apply (rule real_natfloor_le)
    apply (auto simp add: prems)
    apply (insert prems, arith)
    apply (simp add: add_divide_distrib [THEN sym])
    apply (subgoal_tac "real y = real y - 1 + 1")
    apply (erule ssubst)
    apply (rule add_le_less_mono)
    apply (simp add: algebra_simps)
    apply (subgoal_tac "1 + real(natfloor x mod y) =
      real(natfloor x mod y + 1)")
    apply (erule ssubst)
    apply (subst real_of_nat_le_iff)
    apply (subgoal_tac "natfloor x mod y < y")
    apply arith
    apply (rule mod_less_divisor)
    apply auto
    using real_natfloor_add_one_gt
    apply (simp add: algebra_simps)
    done
  finally show ?thesis by simp
qed

lemma le_mult_natfloor:
  assumes "0 \<le> (a :: real)" and "0 \<le> b"
  shows "natfloor a * natfloor b \<le> natfloor (a * b)"
  unfolding natfloor_def
  apply (subst nat_mult_distrib[symmetric])
  using assms apply simp
  apply (subst nat_le_eq_zle)
  using assms le_mult_floor by (auto intro!: mult_nonneg_nonneg)

lemma natceiling_zero [simp]: "natceiling 0 = 0"
  by (unfold natceiling_def, simp)

lemma natceiling_one [simp]: "natceiling 1 = 1"
  by (unfold natceiling_def, simp)

lemma zero_le_natceiling [simp]: "0 <= natceiling x"
  by (unfold natceiling_def, simp)

lemma natceiling_number_of_eq [simp]: "natceiling (number_of n) = number_of n"
  by (unfold natceiling_def, simp)

lemma natceiling_real_of_nat [simp]: "natceiling(real n) = n"
  by (unfold natceiling_def, simp)

lemma real_natceiling_ge: "x <= real(natceiling x)"
  apply (unfold natceiling_def)
  apply (case_tac "x < 0")
  apply simp
  apply (subst real_nat_eq_real)
  apply (subgoal_tac "ceiling 0 <= ceiling x")
  apply simp
  apply (rule ceiling_mono)
  apply simp
  apply simp
done

lemma natceiling_neg: "x <= 0 ==> natceiling x = 0"
  apply (unfold natceiling_def)
  apply simp
done

lemma natceiling_mono: "x <= y ==> natceiling x <= natceiling y"
  apply (case_tac "0 <= x")
  apply (subst natceiling_def)+
  apply (subst nat_le_eq_zle)
  apply (rule disjI2)
  apply (subgoal_tac "real (0::int) <= real(ceiling y)")
  apply simp
  apply (rule order_trans)
  apply simp
  apply (erule order_trans)
  apply simp
  apply (erule ceiling_mono)
  apply (subst natceiling_neg)
  apply simp_all
done

lemma natceiling_le: "x <= real a ==> natceiling x <= a"
  apply (unfold natceiling_def)
  apply (case_tac "x < 0")
  apply simp
  apply (subst (2) nat_int [THEN sym])
  apply (subst nat_le_eq_zle)
  apply simp
  apply (rule ceiling_le)
  apply simp
done

lemma natceiling_le_eq: "0 <= x ==> (natceiling x <= a) = (x <= real a)"
  apply (rule iffI)
  apply (rule order_trans)
  apply (rule real_natceiling_ge)
  apply (subst real_of_nat_le_iff)
  apply assumption
  apply (erule natceiling_le)
done

lemma natceiling_le_eq_number_of [simp]:
    "~ neg((number_of n)::int) ==> 0 <= x ==>
      (natceiling x <= number_of n) = (x <= number_of n)"
  apply (subst natceiling_le_eq, assumption)
  apply simp
done

lemma natceiling_le_eq_one: "(natceiling x <= 1) = (x <= 1)"
  apply (case_tac "0 <= x")
  apply (subst natceiling_le_eq)
  apply assumption
  apply simp
  apply (subst natceiling_neg)
  apply simp
  apply simp
done

lemma natceiling_eq: "real n < x ==> x <= real n + 1 ==> natceiling x = n + 1"
  apply (unfold natceiling_def)
  apply (simplesubst nat_int [THEN sym]) back back
  apply (subgoal_tac "nat(int n) + 1 = nat(int n + 1)")
  apply (erule ssubst)
  apply (subst eq_nat_nat_iff)
  apply (subgoal_tac "ceiling 0 <= ceiling x")
  apply simp
  apply (rule ceiling_mono)
  apply force
  apply force
  apply (rule ceiling_eq2)
  apply (simp, simp)
  apply (subst nat_add_distrib)
  apply auto
done

lemma natceiling_add [simp]: "0 <= x ==>
    natceiling (x + real a) = natceiling x + a"
  apply (unfold natceiling_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply (simp del: real_of_int_of_nat_eq)
  apply (subst nat_add_distrib)
  apply (subgoal_tac "0 = ceiling 0")
  apply (erule ssubst)
  apply (erule ceiling_mono)
  apply simp_all
done

lemma natceiling_add_number_of [simp]:
    "~ neg ((number_of n)::int) ==> 0 <= x ==>
      natceiling (x + number_of n) = natceiling x + number_of n"
  apply (subst natceiling_add [THEN sym])
  apply simp_all
done

lemma natceiling_add_one: "0 <= x ==> natceiling(x + 1) = natceiling x + 1"
  apply (subst natceiling_add [THEN sym])
  apply assumption
  apply simp
done

lemma natceiling_subtract [simp]: "real a <= x ==>
    natceiling(x - real a) = natceiling x - a"
  apply (unfold natceiling_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply (simp del: real_of_int_of_nat_eq)
  apply simp
done

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
