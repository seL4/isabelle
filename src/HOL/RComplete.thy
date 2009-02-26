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


subsection {* Completeness of Positive Reals *}

text {*
  Supremum property for the set of positive reals

  Let @{text "P"} be a non-empty set of positive reals, with an upper
  bound @{text "y"}.  Then @{text "P"} has a least upper bound
  (written @{text "S"}).

  FIXME: Can the premise be weakened to @{text "\<forall>x \<in> P. x\<le> y"}?
*}

lemma posreal_complete:
  assumes positive_P: "\<forall>x \<in> P. (0::real) < x"
    and not_empty_P: "\<exists>x. x \<in> P"
    and upper_bound_Ex: "\<exists>y. \<forall>x \<in> P. x<y"
  shows "\<exists>S. \<forall>y. (\<exists>x \<in> P. y < x) = (y < S)"
proof (rule exI, rule allI)
  fix y
  let ?pP = "{w. real_of_preal w \<in> P}"

  show "(\<exists>x\<in>P. y < x) = (y < real_of_preal (psup ?pP))"
  proof (cases "0 < y")
    assume neg_y: "\<not> 0 < y"
    show ?thesis
    proof
      assume "\<exists>x\<in>P. y < x"
      have "\<forall>x. y < real_of_preal x"
        using neg_y by (rule real_less_all_real2)
      thus "y < real_of_preal (psup ?pP)" ..
    next
      assume "y < real_of_preal (psup ?pP)"
      obtain "x" where x_in_P: "x \<in> P" using not_empty_P ..
      hence "0 < x" using positive_P by simp
      hence "y < x" using neg_y by simp
      thus "\<exists>x \<in> P. y < x" using x_in_P ..
    qed
  next
    assume pos_y: "0 < y"

    then obtain py where y_is_py: "y = real_of_preal py"
      by (auto simp add: real_gt_zero_preal_Ex)

    obtain a where "a \<in> P" using not_empty_P ..
    with positive_P have a_pos: "0 < a" ..
    then obtain pa where "a = real_of_preal pa"
      by (auto simp add: real_gt_zero_preal_Ex)
    hence "pa \<in> ?pP" using `a \<in> P` by auto
    hence pP_not_empty: "?pP \<noteq> {}" by auto

    obtain sup where sup: "\<forall>x \<in> P. x < sup"
      using upper_bound_Ex ..
    from this and `a \<in> P` have "a < sup" ..
    hence "0 < sup" using a_pos by arith
    then obtain possup where "sup = real_of_preal possup"
      by (auto simp add: real_gt_zero_preal_Ex)
    hence "\<forall>X \<in> ?pP. X \<le> possup"
      using sup by (auto simp add: real_of_preal_lessI)
    with pP_not_empty have psup: "\<And>Z. (\<exists>X \<in> ?pP. Z < X) = (Z < psup ?pP)"
      by (rule preal_complete)

    show ?thesis
    proof
      assume "\<exists>x \<in> P. y < x"
      then obtain x where x_in_P: "x \<in> P" and y_less_x: "y < x" ..
      hence "0 < x" using pos_y by arith
      then obtain px where x_is_px: "x = real_of_preal px"
        by (auto simp add: real_gt_zero_preal_Ex)

      have py_less_X: "\<exists>X \<in> ?pP. py < X"
      proof
        show "py < px" using y_is_py and x_is_px and y_less_x
          by (simp add: real_of_preal_lessI)
        show "px \<in> ?pP" using x_in_P and x_is_px by simp
      qed

      have "(\<exists>X \<in> ?pP. py < X) ==> (py < psup ?pP)"
        using psup by simp
      hence "py < psup ?pP" using py_less_X by simp
      thus "y < real_of_preal (psup {w. real_of_preal w \<in> P})"
        using y_is_py and pos_y by (simp add: real_of_preal_lessI)
    next
      assume y_less_psup: "y < real_of_preal (psup ?pP)"

      hence "py < psup ?pP" using y_is_py
        by (simp add: real_of_preal_lessI)
      then obtain "X" where py_less_X: "py < X" and X_in_pP: "X \<in> ?pP"
        using psup by auto
      then obtain x where x_is_X: "x = real_of_preal X"
        by (simp add: real_gt_zero_preal_Ex)
      hence "y < x" using py_less_X and y_is_py
        by (simp add: real_of_preal_lessI)

      moreover have "x \<in> P" using x_is_X and X_in_pP by simp

      ultimately show "\<exists> x \<in> P. y < x" ..
    qed
  qed
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
  \medskip Completeness theorem for the positive reals (again).
*}

lemma posreals_complete:
  assumes positive_S: "\<forall>x \<in> S. 0 < x"
    and not_empty_S: "\<exists>x. x \<in> S"
    and upper_bound_Ex: "\<exists>u. isUb (UNIV::real set) S u"
  shows "\<exists>t. isLub (UNIV::real set) S t"
proof
  let ?pS = "{w. real_of_preal w \<in> S}"

  obtain u where "isUb UNIV S u" using upper_bound_Ex ..
  hence sup: "\<forall>x \<in> S. x \<le> u" by (simp add: isUb_def setle_def)

  obtain x where x_in_S: "x \<in> S" using not_empty_S ..
  hence x_gt_zero: "0 < x" using positive_S by simp
  have  "x \<le> u" using sup and x_in_S ..
  hence "0 < u" using x_gt_zero by arith

  then obtain pu where u_is_pu: "u = real_of_preal pu"
    by (auto simp add: real_gt_zero_preal_Ex)

  have pS_less_pu: "\<forall>pa \<in> ?pS. pa \<le> pu"
  proof
    fix pa
    assume "pa \<in> ?pS"
    then obtain a where "a \<in> S" and "a = real_of_preal pa"
      by simp
    moreover hence "a \<le> u" using sup by simp
    ultimately show "pa \<le> pu"
      using sup and u_is_pu by (simp add: real_of_preal_le_iff)
  qed

  have "\<forall>y \<in> S. y \<le> real_of_preal (psup ?pS)"
  proof
    fix y
    assume y_in_S: "y \<in> S"
    hence "0 < y" using positive_S by simp
    then obtain py where y_is_py: "y = real_of_preal py"
      by (auto simp add: real_gt_zero_preal_Ex)
    hence py_in_pS: "py \<in> ?pS" using y_in_S by simp
    with pS_less_pu have "py \<le> psup ?pS"
      by (rule preal_psup_le)
    thus "y \<le> real_of_preal (psup ?pS)"
      using y_is_py by (simp add: real_of_preal_le_iff)
  qed

  moreover {
    fix x
    assume x_ub_S: "\<forall>y\<in>S. y \<le> x"
    have "real_of_preal (psup ?pS) \<le> x"
    proof -
      obtain "s" where s_in_S: "s \<in> S" using not_empty_S ..
      hence s_pos: "0 < s" using positive_S by simp

      hence "\<exists> ps. s = real_of_preal ps" by (simp add: real_gt_zero_preal_Ex)
      then obtain "ps" where s_is_ps: "s = real_of_preal ps" ..
      hence ps_in_pS: "ps \<in> {w. real_of_preal w \<in> S}" using s_in_S by simp

      from x_ub_S have "s \<le> x" using s_in_S ..
      hence "0 < x" using s_pos by simp
      hence "\<exists> px. x = real_of_preal px" by (simp add: real_gt_zero_preal_Ex)
      then obtain "px" where x_is_px: "x = real_of_preal px" ..

      have "\<forall>pe \<in> ?pS. pe \<le> px"
      proof
	fix pe
	assume "pe \<in> ?pS"
	hence "real_of_preal pe \<in> S" by simp
	hence "real_of_preal pe \<le> x" using x_ub_S by simp
	thus "pe \<le> px" using x_is_px by (simp add: real_of_preal_le_iff)
      qed

      moreover have "?pS \<noteq> {}" using ps_in_pS by auto
      ultimately have "(psup ?pS) \<le> px" by (simp add: psup_le_ub)
      thus "real_of_preal (psup ?pS) \<le> x" using x_is_px by (simp add: real_of_preal_le_iff)
    qed
  }
  ultimately show "isLub UNIV S (real_of_preal (psup ?pS))"
    by (simp add: isLub_def leastP_def isUb_def setle_def setge_def)
qed

text {*
  \medskip reals Completeness (again!)
*}

lemma reals_complete:
  assumes notempty_S: "\<exists>X. X \<in> S"
    and exists_Ub: "\<exists>Y. isUb (UNIV::real set) S Y"
  shows "\<exists>t. isLub (UNIV :: real set) S t"
proof -
  obtain X where X_in_S: "X \<in> S" using notempty_S ..
  obtain Y where Y_isUb: "isUb (UNIV::real set) S Y"
    using exists_Ub ..
  let ?SHIFT = "{z. \<exists>x \<in>S. z = x + (-X) + 1} \<inter> {x. 0 < x}"

  {
    fix x
    assume "isUb (UNIV::real set) S x"
    hence S_le_x: "\<forall> y \<in> S. y <= x"
      by (simp add: isUb_def setle_def)
    {
      fix s
      assume "s \<in> {z. \<exists>x\<in>S. z = x + - X + 1}"
      hence "\<exists> x \<in> S. s = x + -X + 1" ..
      then obtain x1 where "x1 \<in> S" and "s = x1 + (-X) + 1" ..
      moreover hence "x1 \<le> x" using S_le_x by simp
      ultimately have "s \<le> x + - X + 1" by arith
    }
    then have "isUb (UNIV::real set) ?SHIFT (x + (-X) + 1)"
      by (auto simp add: isUb_def setle_def)
  } note S_Ub_is_SHIFT_Ub = this

  hence "isUb UNIV ?SHIFT (Y + (-X) + 1)" using Y_isUb by simp
  hence "\<exists>Z. isUb UNIV ?SHIFT Z" ..
  moreover have "\<forall>y \<in> ?SHIFT. 0 < y" by auto
  moreover have shifted_not_empty: "\<exists>u. u \<in> ?SHIFT"
    using X_in_S and Y_isUb by auto
  ultimately obtain t where t_is_Lub: "isLub UNIV ?SHIFT t"
    using posreals_complete [of ?SHIFT] by blast

  show ?thesis
  proof
    show "isLub UNIV S (t + X + (-1))"
    proof (rule isLubI2)
      {
        fix x
        assume "isUb (UNIV::real set) S x"
        hence "isUb (UNIV::real set) (?SHIFT) (x + (-X) + 1)"
	  using S_Ub_is_SHIFT_Ub by simp
        hence "t \<le> (x + (-X) + 1)"
	  using t_is_Lub by (simp add: isLub_le_isUb)
        hence "t + X + -1 \<le> x" by arith
      }
      then show "(t + X + -1) <=* Collect (isUb UNIV S)"
	by (simp add: setgeI)
    next
      show "isUb UNIV S (t + X + -1)"
      proof -
        {
          fix y
          assume y_in_S: "y \<in> S"
          have "y \<le> t + X + -1"
          proof -
            obtain "u" where u_in_shift: "u \<in> ?SHIFT" using shifted_not_empty ..
            hence "\<exists> x \<in> S. u = x + - X + 1" by simp
            then obtain "x" where x_and_u: "u = x + - X + 1" ..
            have u_le_t: "u \<le> t" using u_in_shift and t_is_Lub by (simp add: isLubD2)

            show ?thesis
            proof cases
              assume "y \<le> x"
              moreover have "x = u + X + - 1" using x_and_u by arith
              moreover have "u + X + - 1  \<le> t + X + -1" using u_le_t by arith
              ultimately show "y  \<le> t + X + -1" by arith
            next
              assume "~(y \<le> x)"
              hence x_less_y: "x < y" by arith

              have "x + (-X) + 1 \<in> ?SHIFT" using x_and_u and u_in_shift by simp
              hence "0 < x + (-X) + 1" by simp
              hence "0 < y + (-X) + 1" using x_less_y by arith
              hence "y + (-X) + 1 \<in> ?SHIFT" using y_in_S by simp
              hence "y + (-X) + 1 \<le> t" using t_is_Lub  by (simp add: isLubD2)
              thus ?thesis by simp
            qed
          qed
        }
        then show ?thesis by (simp add: isUb_def setle_def)
      qed
    qed
  qed
qed


subsection {* The Archimedean Property of the Reals *}

theorem reals_Archimedean:
  assumes x_pos: "0 < x"
  shows "\<exists>n. inverse (real (Suc n)) < x"
proof (rule ccontr)
  assume contr: "\<not> ?thesis"
  have "\<forall>n. x * real (Suc n) <= 1"
  proof
    fix n
    from contr have "x \<le> inverse (real (Suc n))"
      by (simp add: linorder_not_less)
    hence "x \<le> (1 / (real (Suc n)))"
      by (simp add: inverse_eq_divide)
    moreover have "0 \<le> real (Suc n)"
      by (rule real_of_nat_ge_zero)
    ultimately have "x * real (Suc n) \<le> (1 / real (Suc n)) * real (Suc n)"
      by (rule mult_right_mono)
    thus "x * real (Suc n) \<le> 1" by simp
  qed
  hence "{z. \<exists>n. z = x * (real (Suc n))} *<= 1"
    by (simp add: setle_def, safe, rule spec)
  hence "isUb (UNIV::real set) {z. \<exists>n. z = x * (real (Suc n))} 1"
    by (simp add: isUbI)
  hence "\<exists>Y. isUb (UNIV::real set) {z. \<exists>n. z = x* (real (Suc n))} Y" ..
  moreover have "\<exists>X. X \<in> {z. \<exists>n. z = x* (real (Suc n))}" by auto
  ultimately have "\<exists>t. isLub UNIV {z. \<exists>n. z = x * real (Suc n)} t"
    by (simp add: reals_complete)
  then obtain "t" where
    t_is_Lub: "isLub UNIV {z. \<exists>n. z = x * real (Suc n)} t" ..

  have "\<forall>n::nat. x * real n \<le> t + - x"
  proof
    fix n
    from t_is_Lub have "x * real (Suc n) \<le> t"
      by (simp add: isLubD2)
    hence  "x * (real n) + x \<le> t"
      by (simp add: right_distrib real_of_nat_Suc)
    thus  "x * (real n) \<le> t + - x" by arith
  qed

  hence "\<forall>m. x * real (Suc m) \<le> t + - x" by simp
  hence "{z. \<exists>n. z = x * (real (Suc n))}  *<= (t + - x)"
    by (auto simp add: setle_def)
  hence "isUb (UNIV::real set) {z. \<exists>n. z = x * (real (Suc n))} (t + (-x))"
    by (simp add: isUbI)
  hence "t \<le> t + - x"
    using t_is_Lub by (simp add: isLub_le_isUb)
  thus False using x_pos by arith
qed

text {*
  There must be other proofs, e.g. @{text "Suc"} of the largest
  integer in the cut representing @{text "x"}.
*}

lemma reals_Archimedean2: "\<exists>n. (x::real) < real (n::nat)"
proof cases
  assume "x \<le> 0"
  hence "x < real (1::nat)" by simp
  thus ?thesis ..
next
  assume "\<not> x \<le> 0"
  hence x_greater_zero: "0 < x" by simp
  hence "0 < inverse x" by simp
  then obtain n where "inverse (real (Suc n)) < inverse x"
    using reals_Archimedean by blast
  hence "inverse (real (Suc n)) * x < inverse x * x"
    using x_greater_zero by (rule mult_strict_right_mono)
  hence "inverse (real (Suc n)) * x < 1"
    using x_greater_zero by simp
  hence "real (Suc n) * (inverse (real (Suc n)) * x) < real (Suc n) * 1"
    by (rule mult_strict_left_mono) simp
  hence "x < real (Suc n)"
    by (simp add: algebra_simps)
  thus "\<exists>(n::nat). x < real n" ..
qed

instance real :: archimedean_field
proof
  fix r :: real
  obtain n :: nat where "r < real n"
    using reals_Archimedean2 ..
  then have "r \<le> of_int (int n)"
    unfolding real_eq_of_nat by simp
  then show "\<exists>z. r \<le> of_int z" ..
qed

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

lemma reals_Archimedean_6b_int:
     "0 \<le> r ==> \<exists>n::int. real n \<le> r & r < real (n+1)"
  unfolding real_of_int_def by (rule floor_exists)

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
    by (simp only: inverse_eq_divide real_diff_def real_of_nat_Suc 
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

lemma floor_real_of_nat_zero: "floor (real (0::nat)) = 0"
by auto (* delete? *)

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

lemma floor_number_of_eq:
     "floor(number_of n :: real) = (number_of n :: int)"
  by (rule floor_number_of) (* already declared [simp] *)

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

lemma le_floor_eq_number_of:
    "(number_of n <= floor x) = (number_of n <= x)"
  by (rule number_of_le_floor) (* already declared [simp] *)

lemma le_floor_eq_zero: "(0 <= floor x) = (0 <= x)"
  by (rule zero_le_floor) (* already declared [simp] *)

lemma le_floor_eq_one: "(1 <= floor x) = (1 <= x)"
  by (rule one_le_floor) (* already declared [simp] *)

lemma floor_less_eq: "(floor x < a) = (x < real a)"
  unfolding real_of_int_def by (rule floor_less_iff)

lemma floor_less_eq_number_of:
    "(floor x < number_of n) = (x < number_of n)"
  by (rule floor_less_number_of) (* already declared [simp] *)

lemma floor_less_eq_zero: "(floor x < 0) = (x < 0)"
  by (rule floor_less_zero) (* already declared [simp] *)

lemma floor_less_eq_one: "(floor x < 1) = (x < 1)"
  by (rule floor_less_one) (* already declared [simp] *)

lemma less_floor_eq: "(a < floor x) = (real a + 1 <= x)"
  unfolding real_of_int_def by (rule less_floor_iff)

lemma less_floor_eq_number_of:
    "(number_of n < floor x) = (number_of n + 1 <= x)"
  by (rule number_of_less_floor) (* already declared [simp] *)

lemma less_floor_eq_zero: "(0 < floor x) = (1 <= x)"
  by (rule zero_less_floor) (* already declared [simp] *)

lemma less_floor_eq_one: "(1 < floor x) = (2 <= x)"
  by (rule one_less_floor) (* already declared [simp] *)

lemma floor_le_eq: "(floor x <= a) = (x < real a + 1)"
  unfolding real_of_int_def by (rule floor_le_iff)

lemma floor_le_eq_number_of:
    "(floor x <= number_of n) = (x < number_of n + 1)"
  by (rule floor_le_number_of) (* already declared [simp] *)

lemma floor_le_eq_zero: "(floor x <= 0) = (x < 1)"
  by (rule floor_le_zero) (* already declared [simp] *)

lemma floor_le_eq_one: "(floor x <= 1) = (x < 2)"
  by (rule floor_le_one) (* already declared [simp] *)

lemma floor_add [simp]: "floor (x + real a) = floor x + a"
  unfolding real_of_int_def by (rule floor_add_of_int)

lemma floor_subtract [simp]: "floor (x - real a) = floor x - a"
  unfolding real_of_int_def by (rule floor_diff_of_int)

lemma floor_subtract_number_of: "floor (x - number_of n) =
    floor x - number_of n"
  by (rule floor_diff_number_of) (* already declared [simp] *)

lemma floor_subtract_one: "floor (x - 1) = floor x - 1"
  by (rule floor_diff_one) (* already declared [simp] *)

lemma ceiling_real_of_nat [simp]: "ceiling (real (n::nat)) = int n"
  unfolding real_of_nat_def by simp

lemma ceiling_real_of_nat_zero: "ceiling (real (0::nat)) = 0"
by auto (* delete? *)

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

lemma ceiling_number_of_eq:
     "ceiling (number_of n :: real) = (number_of n)"
  by (rule ceiling_number_of) (* already declared [simp] *)

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

lemma ceiling_le_eq_number_of:
    "(ceiling x <= number_of n) = (x <= number_of n)"
  by (rule ceiling_le_number_of) (* already declared [simp] *)

lemma ceiling_le_zero_eq: "(ceiling x <= 0) = (x <= 0)"
  by (rule ceiling_le_zero) (* already declared [simp] *)

lemma ceiling_le_eq_one: "(ceiling x <= 1) = (x <= 1)"
  by (rule ceiling_le_one) (* already declared [simp] *)

lemma less_ceiling_eq: "(a < ceiling x) = (real a < x)"
  unfolding real_of_int_def by (rule less_ceiling_iff)

lemma less_ceiling_eq_number_of:
    "(number_of n < ceiling x) = (number_of n < x)"
  by (rule number_of_less_ceiling) (* already declared [simp] *)

lemma less_ceiling_eq_zero: "(0 < ceiling x) = (0 < x)"
  by (rule zero_less_ceiling) (* already declared [simp] *)

lemma less_ceiling_eq_one: "(1 < ceiling x) = (1 < x)"
  by (rule one_less_ceiling) (* already declared [simp] *)

lemma ceiling_less_eq: "(ceiling x < a) = (x <= real a - 1)"
  unfolding real_of_int_def by (rule ceiling_less_iff)

lemma ceiling_less_eq_number_of:
    "(ceiling x < number_of n) = (x <= number_of n - 1)"
  by (rule ceiling_less_number_of) (* already declared [simp] *)

lemma ceiling_less_eq_zero: "(ceiling x < 0) = (x <= -1)"
  by (rule ceiling_less_zero) (* already declared [simp] *)

lemma ceiling_less_eq_one: "(ceiling x < 1) = (x <= 0)"
  by (rule ceiling_less_one) (* already declared [simp] *)

lemma le_ceiling_eq: "(a <= ceiling x) = (real a - 1 < x)"
  unfolding real_of_int_def by (rule le_ceiling_iff)

lemma le_ceiling_eq_number_of:
    "(number_of n <= ceiling x) = (number_of n - 1 < x)"
  by (rule number_of_le_ceiling) (* already declared [simp] *)

lemma le_ceiling_eq_zero: "(0 <= ceiling x) = (-1 < x)"
  by (rule zero_le_ceiling) (* already declared [simp] *)

lemma le_ceiling_eq_one: "(1 <= ceiling x) = (0 < x)"
  by (rule one_le_ceiling) (* already declared [simp] *)

lemma ceiling_add [simp]: "ceiling (x + real a) = ceiling x + a"
  unfolding real_of_int_def by (rule ceiling_add_of_int)

lemma ceiling_subtract [simp]: "ceiling (x - real a) = ceiling x - a"
  unfolding real_of_int_def by (rule ceiling_diff_of_int)

lemma ceiling_subtract_number_of: "ceiling (x - number_of n) =
    ceiling x - number_of n"
  by (rule ceiling_diff_number_of) (* already declared [simp] *)

lemma ceiling_subtract_one: "ceiling (x - 1) = ceiling x - 1"
  by (rule ceiling_diff_one) (* already declared [simp] *)


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
  apply (subst nat_int [THEN sym]);back;
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
  apply (subst nat_int [THEN sym]);back;
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

end
