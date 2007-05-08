(*  Title       : NthRoot.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Existence of Nth Root*}

theory NthRoot
imports SEQ Parity
begin

definition
  root :: "[nat, real] \<Rightarrow> real" where
  "root n x = (THE u. (0 < x \<longrightarrow> 0 < u) \<and> (u ^ n = x))"

definition
  sqrt :: "real \<Rightarrow> real" where
  "sqrt x = root 2 x"


text {*
  Various lemmas needed for this result. We follow the proof given by
  John Lindsay Orr (\texttt{jorr@math.unl.edu}) in his Analysis
  Webnotes available at \url{http://www.math.unl.edu/~webnotes}.

  Lemmas about sequences of reals are used to reach the result.
*}

lemma lemma_nth_realpow_non_empty:
     "[| (0::real) < a; 0 < n |] ==> \<exists>s. s : {x. x ^ n <= a & 0 < x}"
apply (case_tac "1 <= a")
apply (rule_tac x = 1 in exI)
apply (drule_tac [2] linorder_not_le [THEN iffD1])
apply (drule_tac [2] less_not_refl2 [THEN not0_implies_Suc], simp) 
apply (force intro!: realpow_Suc_le_self simp del: realpow_Suc)
done

text{*Used only just below*}
lemma realpow_ge_self2: "[| (1::real) \<le> r; 0 < n |] ==> r \<le> r ^ n"
by (insert power_increasing [of 1 n r], simp)

lemma lemma_nth_realpow_isUb_ex:
     "[| (0::real) < a; 0 < n |]  
      ==> \<exists>u. isUb (UNIV::real set) {x. x ^ n <= a & 0 < x} u"
apply (case_tac "1 <= a")
apply (rule_tac x = a in exI)
apply (drule_tac [2] linorder_not_le [THEN iffD1])
apply (rule_tac [2] x = 1 in exI)
apply (rule_tac [!] setleI [THEN isUbI], safe)
apply (simp_all (no_asm))
apply (rule_tac [!] ccontr)
apply (drule_tac [!] linorder_not_le [THEN iffD1])
apply (drule realpow_ge_self2, assumption)
apply (drule_tac n = n in realpow_less)
apply (assumption+)
apply (drule real_le_trans, assumption)
apply (drule_tac y = "y ^ n" in order_less_le_trans, assumption, simp) 
apply (drule_tac n = n in zero_less_one [THEN realpow_less], auto)
done

lemma nth_realpow_isLub_ex:
     "[| (0::real) < a; 0 < n |]  
      ==> \<exists>u. isLub (UNIV::real set) {x. x ^ n <= a & 0 < x} u"
by (blast intro: lemma_nth_realpow_isUb_ex lemma_nth_realpow_non_empty reals_complete)

 
subsection{*First Half -- Lemmas First*}

lemma lemma_nth_realpow_seq:
     "isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u  
           ==> u + inverse(real (Suc k)) ~: {x. x ^ n <= a & 0 < x}"
apply (safe, drule isLubD2, blast)
apply (simp add: linorder_not_less [symmetric])
done

lemma lemma_nth_realpow_isLub_gt_zero:
     "[| isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u;  
         0 < a; 0 < n |] ==> 0 < u"
apply (drule lemma_nth_realpow_non_empty, auto)
apply (drule_tac y = s in isLub_isUb [THEN isUbD])
apply (auto intro: order_less_le_trans)
done

lemma lemma_nth_realpow_isLub_ge:
     "[| isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u;  
         0 < a; 0 < n |] ==> ALL k. a <= (u + inverse(real (Suc k))) ^ n"
apply safe
apply (frule lemma_nth_realpow_seq, safe)
apply (auto elim: order_less_asym simp add: linorder_not_less [symmetric]
            iff: real_0_less_add_iff) --{*legacy iff rule!*}
apply (simp add: linorder_not_less)
apply (rule order_less_trans [of _ 0])
apply (auto intro: lemma_nth_realpow_isLub_gt_zero)
done

text{*First result we want*}
lemma realpow_nth_ge:
     "[| (0::real) < a; 0 < n;  
     isLub (UNIV::real set)  
     {x. x ^ n <= a & 0 < x} u |] ==> a <= u ^ n"
apply (frule lemma_nth_realpow_isLub_ge, safe)
apply (rule LIMSEQ_inverse_real_of_nat_add [THEN LIMSEQ_pow, THEN LIMSEQ_le_const])
apply (auto simp add: real_of_nat_def)
done

subsection{*Second Half*}

lemma less_isLub_not_isUb:
     "[| isLub (UNIV::real set) S u; x < u |]  
           ==> ~ isUb (UNIV::real set) S x"
apply safe
apply (drule isLub_le_isUb, assumption)
apply (drule order_less_le_trans, auto)
done

lemma not_isUb_less_ex:
     "~ isUb (UNIV::real set) S u ==> \<exists>x \<in> S. u < x"
apply (rule ccontr, erule contrapos_np)
apply (rule setleI [THEN isUbI])
apply (auto simp add: linorder_not_less [symmetric])
done

lemma real_mult_less_self: "0 < r ==> r * (1 + -inverse(real (Suc n))) < r"
apply (simp (no_asm) add: right_distrib)
apply (rule add_less_cancel_left [of "-r", THEN iffD1])
apply (auto intro: mult_pos_pos
            simp add: add_assoc [symmetric] neg_less_0_iff_less)
done

lemma real_of_nat_inverse_le_iff:
  "(inverse (real(Suc n)) \<le> r) = (1 \<le> r * real(Suc n))"
by (simp add: inverse_eq_divide pos_divide_le_eq)

lemma real_mult_add_one_minus_ge_zero:
     "0 < r ==>  0 <= r*(1 + -inverse(real (Suc n)))"
by (simp add: zero_le_mult_iff real_of_nat_inverse_le_iff real_0_le_add_iff)

lemma lemma_nth_realpow_isLub_le:
     "[| isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u;  
       0 < a; 0 < n |] ==> ALL k. (u*(1 + -inverse(real (Suc k)))) ^ n <= a"
apply safe
apply (frule less_isLub_not_isUb [THEN not_isUb_less_ex])
apply (rule_tac n = k in real_mult_less_self)
apply (blast intro: lemma_nth_realpow_isLub_gt_zero, safe)
apply (drule_tac n = k in
        lemma_nth_realpow_isLub_gt_zero [THEN real_mult_add_one_minus_ge_zero], assumption+)
apply (blast intro: order_trans order_less_imp_le power_mono) 
done

text{*Second result we want*}
lemma realpow_nth_le:
     "[| (0::real) < a; 0 < n;  
     isLub (UNIV::real set)  
     {x. x ^ n <= a & 0 < x} u |] ==> u ^ n <= a"
apply (frule lemma_nth_realpow_isLub_le, safe)
apply (rule LIMSEQ_inverse_real_of_nat_add_minus_mult
                [THEN LIMSEQ_pow, THEN LIMSEQ_le_const2])
apply (auto simp add: real_of_nat_def)
done

text{*The theorem at last!*}
lemma realpow_nth: "[| (0::real) < a; 0 < n |] ==> \<exists>r. r ^ n = a"
apply (frule nth_realpow_isLub_ex, auto)
apply (auto intro: realpow_nth_le realpow_nth_ge order_antisym)
done

(* positive only *)
lemma realpow_pos_nth: "[| (0::real) < a; 0 < n |] ==> \<exists>r. 0 < r & r ^ n = a"
apply (frule nth_realpow_isLub_ex, auto)
apply (auto intro: realpow_nth_le realpow_nth_ge order_antisym lemma_nth_realpow_isLub_gt_zero)
done

lemma realpow_pos_nth2: "(0::real) < a  ==> \<exists>r. 0 < r & r ^ Suc n = a"
by (blast intro: realpow_pos_nth)

(* uniqueness of nth positive root *)
lemma realpow_pos_nth_unique:
     "[| (0::real) < a; 0 < n |] ==> EX! r. 0 < r & r ^ n = a"
apply (auto intro!: realpow_pos_nth)
apply (cut_tac x = r and y = y in linorder_less_linear, auto)
apply (drule_tac x = r in realpow_less)
apply (drule_tac [4] x = y in realpow_less, auto)
done

subsection {* Nth Root *}

lemma real_root_zero [simp]: "root (Suc n) 0 = 0"
apply (simp add: root_def)
apply (safe intro!: the_equality power_0_Suc elim!: realpow_zero_zero)
done

lemma real_root_pow_pos: 
     "0 < x ==> (root (Suc n) x) ^ (Suc n) = x"
apply (simp add: root_def del: realpow_Suc)
apply (drule_tac n="Suc n" in realpow_pos_nth_unique, simp)
apply (erule theI' [THEN conjunct2])
done

lemma real_root_pow_pos2: "0 \<le> x ==> (root (Suc n) x) ^ (Suc n) = x"
by (auto dest!: real_le_imp_less_or_eq dest: real_root_pow_pos)

lemma real_root_pos: 
     "0 < x ==> root(Suc n) (x ^ (Suc n)) = x"
apply (simp add: root_def)
apply (rule the_equality)
apply (frule_tac [2] n = n in zero_less_power)
apply (auto simp add: zero_less_mult_iff)
apply (rule_tac x = u and y = x in linorder_cases)
apply (drule_tac n1 = n and x = u in zero_less_Suc [THEN [3] realpow_less])
apply (drule_tac [4] n1 = n and x = x in zero_less_Suc [THEN [3] realpow_less])
apply (auto)
done

lemma real_root_pos2: "0 \<le> x ==> root(Suc n) (x ^ (Suc n)) = x"
by (auto dest!: real_le_imp_less_or_eq real_root_pos)

lemma real_root_gt_zero:
     "0 < x ==> 0 < root (Suc n) x"
apply (simp add: root_def del: realpow_Suc)
apply (drule_tac n="Suc n" in realpow_pos_nth_unique, simp)
apply (erule theI' [THEN conjunct1])
done

lemma real_root_pos_pos: 
     "0 < x ==> 0 \<le> root(Suc n) x"
by (rule real_root_gt_zero [THEN order_less_imp_le])

lemma real_root_pos_pos_le: "0 \<le> x ==> 0 \<le> root(Suc n) x"
by (auto simp add: order_le_less real_root_gt_zero)

lemma real_root_one [simp]: "root (Suc n) 1 = 1"
apply (simp add: root_def)
apply (rule the_equality, auto)
apply (rule ccontr)
apply (rule_tac x = u and y = 1 in linorder_cases)
apply (drule_tac n = n in realpow_Suc_less_one)
apply (drule_tac [4] n = n in power_gt1_lemma)
apply (auto)
done

lemma real_root_less_mono:
     "[| 0 \<le> x; x < y |] ==> root(Suc n) x < root(Suc n) y"
apply (subgoal_tac "0 \<le> y")
apply (rule_tac n="Suc n" in power_less_imp_less_base)
apply (simp only: real_root_pow_pos2)
apply (erule real_root_pos_pos_le)
apply (erule order_trans)
apply (erule order_less_imp_le)
done

lemma real_root_le_mono:
     "[| 0 \<le> x; x \<le> y |] ==> root(Suc n) x \<le> root(Suc n) y"
apply (drule_tac y = y in order_le_imp_less_or_eq)
apply (auto dest: real_root_less_mono intro: order_less_imp_le)
done

lemma real_root_less_iff [simp]:
     "[| 0 \<le> x; 0 \<le> y |] ==> (root(Suc n) x < root(Suc n) y) = (x < y)"
apply (auto intro: real_root_less_mono)
apply (rule ccontr, drule linorder_not_less [THEN iffD1])
apply (drule_tac x = y and n = n in real_root_le_mono, auto)
done

lemma real_root_le_iff [simp]:
     "[| 0 \<le> x; 0 \<le> y |] ==> (root(Suc n) x \<le> root(Suc n) y) = (x \<le> y)"
apply (auto intro: real_root_le_mono)
apply (simp (no_asm) add: linorder_not_less [symmetric])
apply auto
apply (drule_tac x = y and n = n in real_root_less_mono, auto)
done

lemma real_root_eq_iff [simp]:
     "[| 0 \<le> x; 0 \<le> y |] ==> (root(Suc n) x = root(Suc n) y) = (x = y)"
apply (auto intro!: order_antisym [where 'a = real])
apply (rule_tac n1 = n in real_root_le_iff [THEN iffD1])
apply (rule_tac [4] n1 = n in real_root_le_iff [THEN iffD1], auto)
done

lemma real_root_pos_unique:
     "[| 0 \<le> x; 0 \<le> y; y ^ (Suc n) = x |] ==> root (Suc n) x = y"
by (auto dest: real_root_pos2 simp del: realpow_Suc)

lemma real_root_mult:
     "[| 0 \<le> x; 0 \<le> y |] 
      ==> root(Suc n) (x * y) = root(Suc n) x * root(Suc n) y"
apply (rule real_root_pos_unique)
apply (auto intro!: real_root_pos_pos_le 
            simp add: power_mult_distrib zero_le_mult_iff real_root_pow_pos2 
            simp del: realpow_Suc)
done

lemma real_root_inverse:
     "0 \<le> x ==> (root(Suc n) (inverse x) = inverse(root(Suc n) x))"
apply (rule real_root_pos_unique)
apply (auto intro: real_root_pos_pos_le 
            simp add: power_inverse [symmetric] real_root_pow_pos2 
            simp del: realpow_Suc)
done

lemma real_root_divide: 
     "[| 0 \<le> x; 0 \<le> y |]  
      ==> (root(Suc n) (x / y) = root(Suc n) x / root(Suc n) y)"
apply (simp add: divide_inverse)
apply (auto simp add: real_root_mult real_root_inverse)
done


subsection{*Square Root*}

text{*needed because 2 is a binary numeral!*}
lemma root_2_eq [simp]: "root 2 = root (Suc (Suc 0))"
by (simp only: numeral_2_eq_2)

lemma real_sqrt_zero [simp]: "sqrt 0 = 0"
by (simp add: sqrt_def)

lemma real_sqrt_one [simp]: "sqrt 1 = 1"
by (simp add: sqrt_def)

lemma real_sqrt_pow2 [simp]: "0 \<le> x ==> (sqrt x)\<twosuperior> = x"
unfolding sqrt_def numeral_2_eq_2
by (rule real_root_pow_pos2)

lemma real_sqrt_pow2_iff [iff]: "((sqrt x)\<twosuperior> = x) = (0 \<le> x)"
apply (rule iffI)
apply (erule subst)
apply (rule zero_le_power2)
apply (erule real_sqrt_pow2)
done

lemma real_sqrt_abs_abs [simp]: "(sqrt \<bar>x\<bar>)\<twosuperior> = \<bar>x\<bar>" (* TODO: delete *)
by simp

lemma sqrt_eqI: "\<lbrakk>r\<twosuperior> = a; 0 \<le> r\<rbrakk> \<Longrightarrow> sqrt a = r"
unfolding sqrt_def numeral_2_eq_2
by (erule subst, erule real_root_pos2)

lemma real_sqrt_abs [simp]: "sqrt (x\<twosuperior>) = \<bar>x\<bar>"
apply (rule sqrt_eqI)
apply (rule power2_abs)
apply (rule abs_ge_zero)
done

lemma real_pow_sqrt_eq_sqrt_pow: (* TODO: delete *)
      "0 \<le> x ==> (sqrt x)\<twosuperior> = sqrt(x\<twosuperior>)"
by simp

lemma real_pow_sqrt_eq_sqrt_abs_pow2: (* TODO: delete *)
     "0 \<le> x ==> (sqrt x)\<twosuperior> = sqrt(\<bar>x\<bar> ^ 2)" 
by simp

lemma real_sqrt_pow_abs: "0 \<le> x ==> (sqrt x)\<twosuperior> = \<bar>x\<bar>" (* TODO: delete *)
by simp

lemma not_real_square_gt_zero [simp]: "(~ (0::real) < x*x) = (x = 0)"
apply auto
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (simp add: zero_less_mult_iff)
done

lemma real_sqrt_gt_zero: "0 < x ==> 0 < sqrt(x)"
by (simp add: sqrt_def real_root_gt_zero)

lemma real_sqrt_ge_zero: "0 \<le> x ==> 0 \<le> sqrt(x)"
by (auto intro: real_sqrt_gt_zero simp add: order_le_less)


(*we need to prove something like this:
lemma "[|r ^ n = a; 0<n; 0 < a \<longrightarrow> 0 < r|] ==> root n a = r"
apply (case_tac n, simp) 
apply (simp add: root_def) 
apply (rule someI2 [of _ r], safe)
apply (auto simp del: realpow_Suc dest: power_inject_base)
*)

lemma real_sqrt_mult_distrib: 
     "[| 0 \<le> x; 0 \<le> y |] ==> sqrt(x*y) = sqrt(x) * sqrt(y)"
unfolding sqrt_def numeral_2_eq_2
by (rule real_root_mult)

lemmas real_sqrt_mult_distrib2 = real_sqrt_mult_distrib

lemma real_sqrt_abs2 [simp]: "sqrt(x*x) = \<bar>x\<bar>"
apply (subst power2_eq_square [symmetric])
apply (rule real_sqrt_abs)
done

lemma real_sqrt_pow2_gt_zero: "0 < x ==> 0 < (sqrt x)\<twosuperior>"
by simp

lemma real_sqrt_not_eq_zero: "0 < x ==> sqrt x \<noteq> 0"
apply (frule real_sqrt_pow2_gt_zero)
apply (auto simp add: numeral_2_eq_2)
done

lemma real_inv_sqrt_pow2: "0 < x ==> inverse (sqrt(x)) ^ 2 = inverse x"
by (simp add: power_inverse [symmetric])

lemma real_sqrt_eq_zero_cancel: "[| 0 \<le> x; sqrt(x) = 0|] ==> x = 0"
apply (drule real_le_imp_less_or_eq)
apply (auto dest: real_sqrt_not_eq_zero)
done

lemma real_sqrt_eq_zero_cancel_iff [simp]: "0 \<le> x ==> ((sqrt x = 0) = (x=0))"
by (auto simp add: real_sqrt_eq_zero_cancel)

lemma real_sqrt_ge_one: "1 \<le> x ==> 1 \<le> sqrt x"
apply (rule power2_le_imp_le, simp)
apply (simp add: real_sqrt_ge_zero)
done

lemma sqrt_divide_self_eq:
  assumes nneg: "0 \<le> x"
  shows "sqrt x / x = inverse (sqrt x)"
proof cases
  assume "x=0" thus ?thesis by simp
next
  assume nz: "x\<noteq>0" 
  hence pos: "0<x" using nneg by arith
  show ?thesis
  proof (rule right_inverse_eq [THEN iffD1, THEN sym]) 
    show "sqrt x / x \<noteq> 0" by (simp add: divide_inverse nneg nz) 
    show "inverse (sqrt x) / (sqrt x / x) = 1"
      by (simp add: divide_inverse mult_assoc [symmetric] 
                  power2_eq_square [symmetric] real_inv_sqrt_pow2 pos nz) 
  qed
qed


lemma real_sqrt_less_mono: "[| 0 \<le> x; x < y |] ==> sqrt(x) < sqrt(y)"
by (simp add: sqrt_def)

lemma real_sqrt_le_mono: "[| 0 \<le> x; x \<le> y |] ==> sqrt(x) \<le> sqrt(y)"
by (simp add: sqrt_def)

lemma real_sqrt_less_iff [simp]:
     "[| 0 \<le> x; 0 \<le> y |] ==> (sqrt(x) < sqrt(y)) = (x < y)"
by (simp add: sqrt_def)

lemma real_sqrt_le_iff [simp]:
     "[| 0 \<le> x; 0 \<le> y |] ==> (sqrt(x) \<le> sqrt(y)) = (x \<le> y)"
by (simp add: sqrt_def)

lemma real_sqrt_eq_iff [simp]:
     "[| 0 \<le> x; 0 \<le> y |] ==> (sqrt(x) = sqrt(y)) = (x = y)"
by (simp add: sqrt_def)

lemma real_divide_square_eq [simp]: "(((r::real) * a) / (r * r)) = a / r"
apply (simp add: divide_inverse)
apply (case_tac "r=0")
apply (auto simp add: mult_ac)
done

subsection {* Square Root of Sum of Squares *}

lemma "(sqrt (x\<twosuperior> + y\<twosuperior>))\<twosuperior> = x\<twosuperior> + y\<twosuperior>"
by (rule realpow_two_le_add_order [THEN real_sqrt_pow2_iff [THEN iffD2]])

lemma real_sqrt_mult_self_sum_ge_zero [simp]: "0 \<le> sqrt(x*x + y*y)"
by (rule real_sqrt_ge_zero [OF real_mult_self_sum_ge_zero]) 

lemma real_sqrt_sum_squares_ge_zero [simp]: "0 \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
by (auto intro!: real_sqrt_ge_zero)

lemma real_sqrt_sum_squares_mult_ge_zero [simp]:
     "0 \<le> sqrt ((x\<twosuperior> + y\<twosuperior>)*(xa\<twosuperior> + ya\<twosuperior>))"
by (auto intro!: real_sqrt_ge_zero simp add: zero_le_mult_iff)

lemma real_sqrt_sum_squares_mult_squared_eq [simp]:
     "sqrt ((x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)) ^ 2 = (x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)"
by (auto simp add: zero_le_mult_iff simp del: realpow_Suc)

lemma real_sqrt_sum_squares_ge1 [simp]: "x \<le> sqrt(x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_sum_squares_ge2 [simp]: "y \<le> sqrt(x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_sos_less_one_iff [simp]: "(sqrt(x\<twosuperior> + y\<twosuperior>) < 1) = (x\<twosuperior> + y\<twosuperior> < 1)"
apply (subst real_sqrt_one [symmetric])
apply (rule real_sqrt_less_iff, auto)
done

lemma real_sqrt_sos_eq_one_iff [simp]: "(sqrt(x\<twosuperior> + y\<twosuperior>) = 1) = (x\<twosuperior> + y\<twosuperior> = 1)"
apply (subst real_sqrt_one [symmetric])
apply (rule real_sqrt_eq_iff, auto)
done

end
