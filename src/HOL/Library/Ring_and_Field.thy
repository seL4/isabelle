(*  Title:      HOL/Library/Ring_and_Field.thy
    ID:         $Id$
    Author:     Gertrud Bauer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {*
  \title{Ring and field structures}
  \author{Gertrud Bauer and Markus Wenzel}
*}

theory Ring_and_Field = Main:

subsection {* Abstract algebraic structures *}

axclass ring \<subseteq> zero, one, plus, minus, times
  add_assoc: "(a + b) + c = a + (b + c)"
  add_commute: "a + b = b + a"
  left_zero [simp]: "0 + a = a"
  left_minus [simp]: "- a + a = 0"
  diff_minus: "a - b = a + (-b)"

  mult_assoc: "(a * b) * c = a * (b * c)"
  mult_commute: "a * b = b * a"
  left_one [simp]: "1 * a = a"

  left_distrib: "(a + b) * c = a * c + b * c"

axclass ordered_ring \<subseteq> ring, linorder
  add_left_mono: "a \<le> b ==> c + a \<le> c + b"
  mult_strict_left_mono: "a < b ==> 0 < c ==> c * a < c * b"
  abs_if: "\<bar>a\<bar> = (if a < 0 then -a else a)"

axclass field \<subseteq> ring, inverse
  left_inverse [simp]: "a \<noteq> 0 ==> inverse a * a = 1"
  divide_inverse: "b \<noteq> 0 ==> a / b = a * inverse b"

axclass ordered_field \<subseteq> ordered_ring, field

axclass division_by_zero \<subseteq> zero, inverse
  inverse_zero: "inverse 0 = 0"
  divide_zero: "a / 0 = 0"



subsection {* Derived rules *}

subsubsection {* Derived rules for addition *}

lemma right_zero [simp]: "a + 0 = (a::'a::ring)"
proof -
  have "a + 0 = 0 + a" by (simp only: add_commute)
  also have "... = a" by simp
  finally show ?thesis .
qed

lemma add_left_commute: "a + (b + c) = b + (a + (c::'a::ring))"
  by (rule mk_left_commute [of "op +", OF add_assoc add_commute])

theorems ring_add_ac = add_assoc add_commute add_left_commute

lemma right_minus [simp]: "a + -(a::'a::ring) = 0"
proof -
  have "a + -a = -a + a" by (simp add: ring_add_ac)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma right_minus_eq: "(a - b = 0) = (a = (b::'a::ring))"
proof
  have "a = a - b + b" by (simp add: diff_minus ring_add_ac)
  also assume "a - b = 0"
  finally show "a = b" by simp
next
  assume "a = b"
  thus "a - b = 0" by (simp add: diff_minus)
qed

lemma diff_self [simp]: "a - (a::'a::ring) = 0"
  by (simp add: diff_minus)

lemma add_left_cancel [simp]:
     "(a + b = a + c) = (b = (c::'a::ring))"
proof
  assume eq: "a + b = a + c"
  then have "(-a + a) + b = (-a + a) + c"
    by (simp only: eq add_assoc)
  then show "b = c" by simp
next
  assume eq: "b = c"
  then show "a + b = a + c" by simp
qed

lemma add_right_cancel [simp]:
     "(b + a = c + a) = (b = (c::'a::ring))"
  by (simp add: add_commute)

lemma minus_minus [simp]: "- (- (a::'a::ring)) = a"
  proof (rule add_left_cancel [of "-a", THEN iffD1])
    show "(-a + -(-a) = -a + a)"
    by simp
  qed

lemma equals_zero_I: "a+b = 0 ==> -a = (b::'a::ring)"
apply (rule right_minus_eq [THEN iffD1, symmetric])
apply (simp add: diff_minus add_commute) 
done

lemma minus_zero [simp]: "- 0 = (0::'a::ring)"
by (simp add: equals_zero_I)

lemma neg_equal_iff_equal [simp]: "(-a = -b) = (a = (b::'a::ring))" 
  proof 
    assume "- a = - b"
    then have "- (- a) = - (- b)"
      by simp
    then show "a=b"
      by simp
  next
    assume "a=b"
    then show "-a = -b"
      by simp
  qed

lemma neg_equal_0_iff_equal [simp]: "(-a = 0) = (a = (0::'a::ring))"
by (subst neg_equal_iff_equal [symmetric], simp)

lemma neg_0_equal_iff_equal [simp]: "(0 = -a) = (0 = (a::'a::ring))"
by (subst neg_equal_iff_equal [symmetric], simp)


subsubsection {* Derived rules for multiplication *}

lemma right_one [simp]: "a = a * (1::'a::field)"
proof -
  have "a = 1 * a" by simp
  also have "... = a * 1" by (simp add: mult_commute)
  finally show ?thesis .
qed

lemma mult_left_commute: "a * (b * c) = b * (a * (c::'a::ring))"
  by (rule mk_left_commute [of "op *", OF mult_assoc mult_commute])

theorems ring_mult_ac = mult_assoc mult_commute mult_left_commute

lemma right_inverse [simp]: "a \<noteq> 0 ==>  a * inverse (a::'a::field) = 1"
proof -
  have "a * inverse a = inverse a * a" by (simp add: ring_mult_ac)
  also assume "a \<noteq> 0"
  hence "inverse a * a = 1" by simp
  finally show ?thesis .
qed

lemma right_inverse_eq: "b \<noteq> 0 ==> (a / b = 1) = (a = (b::'a::field))"
proof
  assume neq: "b \<noteq> 0"
  {
    hence "a = (a / b) * b" by (simp add: divide_inverse ring_mult_ac)
    also assume "a / b = 1"
    finally show "a = b" by simp
  next
    assume "a = b"
    with neq show "a / b = 1" by (simp add: divide_inverse)
  }
qed

lemma divide_self [simp]: "a \<noteq> 0 ==> a / (a::'a::field) = 1"
  by (simp add: divide_inverse)

lemma mult_left_zero [simp]:
     "0 * a = (0::'a::ring)"
proof -
  have "0*a + 0*a = 0*a + 0"
    by (simp add: left_distrib [symmetric])
  then show ?thesis by (simp only: add_left_cancel)
qed

lemma mult_right_zero [simp]:
     "a * 0 = (0::'a::ring)"
  by (simp add: mult_commute)


subsubsection {* Distribution rules *}

lemma right_distrib: "a * (b + c) = a * b + a * (c::'a::ring)"
proof -
  have "a * (b + c) = (b + c) * a" by (simp add: ring_mult_ac)
  also have "... = b * a + c * a" by (simp only: left_distrib)
  also have "... = a * b + a * c" by (simp add: ring_mult_ac)
  finally show ?thesis .
qed

theorems ring_distrib = right_distrib left_distrib

lemma minus_add_distrib [simp]: "- (a + b) = -a + -(b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: ring_add_ac) 
done

lemma minus_mult_left: "- (a * b) = (-a) * (b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: left_distrib [symmetric]) 
done

lemma minus_mult_right: "- (a * b) = a * -(b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: right_distrib [symmetric]) 
done

lemma right_diff_distrib: "a * (b - c) = a * b - a * (c::'a::ring)"
by (simp add: right_distrib diff_minus 
              minus_mult_left [symmetric] minus_mult_right [symmetric]) 


subsubsection {* Ordering rules *}

lemma add_right_mono: "a \<le> (b::'a::ordered_ring) ==> a + c \<le> b + c"
by (simp add: add_commute [of _ c] add_left_mono)

lemma le_imp_neg_le: "a \<le> (b::'a::ordered_ring) ==> -b \<le> -a"
  proof -
  assume "a\<le>b"
  then have "-a+a \<le> -a+b"
    by (rule add_left_mono) 
  then have "0 \<le> -a+b"
    by simp
  then have "0 + (-b) \<le> (-a + b) + (-b)"
    by (rule add_right_mono) 
  then show ?thesis
    by (simp add: add_assoc)
  qed

lemma neg_le_iff_le [simp]: "(-b \<le> -a) = (a \<le> (b::'a::ordered_ring))"
  proof 
    assume "- b \<le> - a"
    then have "- (- a) \<le> - (- b)"
      by (rule le_imp_neg_le)
    then show "a\<le>b"
      by simp
  next
    assume "a\<le>b"
    then show "-b \<le> -a"
      by (rule le_imp_neg_le)
  qed

lemma neg_le_0_iff_le [simp]: "(-a \<le> 0) = (0 \<le> (a::'a::ordered_ring))"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_0_le_iff_le [simp]: "(0 \<le> -a) = (a \<le> (0::'a::ordered_ring))"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_less_iff_less [simp]: "(-b < -a) = (a < (b::'a::ordered_ring))"
by (force simp add: order_less_le) 

lemma neg_less_0_iff_less [simp]: "(-a < 0) = (0 < (a::'a::ordered_ring))"
by (subst neg_less_iff_less [symmetric], simp)

lemma neg_0_less_iff_less [simp]: "(0 < -a) = (a < (0::'a::ordered_ring))"
by (subst neg_less_iff_less [symmetric], simp)

lemma mult_strict_right_mono:
     "[|a < b; 0 < c|] ==> a * c < b * (c::'a::ordered_ring)"
by (simp add: mult_commute [of _ c] mult_strict_left_mono)

lemma mult_neg_left_mono:
     "[|b < a; c < 0|] ==> c * a < c * (b::'a::ordered_ring)"
 apply (drule mult_strict_left_mono [of _ _ "-c"])
apply (simp_all add: minus_mult_left [symmetric]) 
done


subsubsection{* Products of Signs *}

lemma mult_pos: "[| (0::'a::ordered_ring) < a; 0 < b |] ==> 0 < a*b"
by (drule mult_strict_left_mono [of 0 b], auto)

lemma mult_pos_neg: "[| (0::'a::ordered_ring) < a; b < 0 |] ==> a*b < 0"
by (drule mult_strict_left_mono [of b 0], auto)

end
