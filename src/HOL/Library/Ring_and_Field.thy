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


subsubsection {* Distribution rules *}

lemma right_distrib: "a * (b + c) = a * b + a * (c::'a::ring)"
proof -
  have "a * (b + c) = (b + c) * a" by (simp add: ring_mult_ac)
  also have "... = b * a + c * a" by (simp only: left_distrib)
  also have "... = a * b + a * c" by (simp add: ring_mult_ac)
  finally show ?thesis .
qed

theorems ring_distrib = right_distrib left_distrib

end
