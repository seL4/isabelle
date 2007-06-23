(*  Title:      HOL/MetisExamples/BigO.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Testing the metis method
*)

header {* Big O notation *}

theory BigO
imports SetsAndFunctions 
begin

subsection {* Definitions *}

constdefs 

  bigo :: "('a => 'b::ordered_idom) => ('a => 'b) set"    ("(1O'(_'))")
  "O(f::('a => 'b)) ==   {h. EX c. ALL x. abs (h x) <= c * abs (f x)}"

ML{*ResAtp.problem_name := "BigO__bigo_pos_const"*}
lemma bigo_pos_const: "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto);
txt{*Version 1: one-shot proof. MUCH SLOWER with types: 24 versus 6.7 seconds*}
  apply (metis abs_ge_minus_self abs_ge_zero abs_minus_cancel abs_of_nonneg equation_minus_iff Orderings.xt1(6) abs_le_mult)
  done

(*** Now various verions with an increasing modulus ***)

ML{*ResReconstruct.modulus := 1*}

lemma bigo_pos_const: "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
(*hand-modified to give 'a sort ordered_idom and X3 type 'a*)
proof (neg_clausify)
fix c x
assume 0: "\<And>A. \<bar>h A\<bar> \<le> c * \<bar>f A\<bar>"
assume 1: "c \<noteq> (0\<Colon>'a::ordered_idom)"
assume 2: "\<not> \<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>"
have 3: "\<And>X1 X3. \<bar>h X3\<bar> < X1 \<or> \<not> c * \<bar>f X3\<bar> < X1"
  by (metis order_le_less_trans 0)
have 4: "\<And>X3. (1\<Colon>'a) * X3 \<le> X3 \<or> \<not> (1\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis mult_le_cancel_right2 order_refl)
have 5: "\<And>X3. (1\<Colon>'a) * X3 \<le> X3"
  by (metis 4 order_refl)
have 6: "\<And>X3. \<bar>0\<Colon>'a\<bar> = \<bar>X3\<bar> * (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (0\<Colon>'a)"
  by (metis abs_mult_pos mult_cancel_right1)
have 7: "\<bar>0\<Colon>'a\<bar> = (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (0\<Colon>'a)"
  by (metis 6 mult_cancel_right1)
have 8: "\<bar>0\<Colon>'a\<bar> = (0\<Colon>'a)"
  by (metis 7 order_refl)
have 9: "\<not> (0\<Colon>'a) < (0\<Colon>'a)"
  by (metis abs_not_less_zero 8)
have 10: "\<bar>(1\<Colon>'a) * (0\<Colon>'a)\<bar> = - ((1\<Colon>'a) * (0\<Colon>'a))"
  by (metis abs_of_nonpos 5)
have 11: "(0\<Colon>'a) = - ((1\<Colon>'a) * (0\<Colon>'a))"
  by (metis 10 mult_cancel_right1 8)
have 12: "(0\<Colon>'a) = - (0\<Colon>'a)"
  by (metis 11 mult_cancel_right1)
have 13: "\<And>X3. \<bar>X3\<bar> = X3 \<or> X3 \<le> (0\<Colon>'a)"
  by (metis abs_of_nonneg linorder_linear)
have 14: "c \<le> (0\<Colon>'a) \<or> \<not> \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  by (metis 2 13)
have 15: "c \<le> (0\<Colon>'a)"
  by (metis 14 0)
have 16: "c = (0\<Colon>'a) \<or> c < (0\<Colon>'a)"
  by (metis linorder_antisym_conv2 15)
have 17: "\<bar>c\<bar> = - c"
  by (metis abs_of_nonpos 15)
have 18: "c < (0\<Colon>'a)"
  by (metis 16 1)
have 19: "\<not> \<bar>h x\<bar> \<le> - c * \<bar>f x\<bar>"
  by (metis 2 17)
have 20: "\<And>X3. X3 * (1\<Colon>'a) = X3"
  by (metis mult_cancel_right1 AC_mult.f.commute)
have 21: "\<And>X3. (0\<Colon>'a) \<le> X3 * X3"
  by (metis zero_le_square AC_mult.f.commute)
have 22: "(0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis 21 mult_cancel_left1)
have 23: "\<And>X3. (0\<Colon>'a) = X3 \<or> (0\<Colon>'a) \<noteq> - X3"
  by (metis neg_equal_iff_equal 12)
have 24: "\<And>X3. (0\<Colon>'a) = - X3 \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis 23 minus_equation_iff)
have 25: "\<And>X3. \<bar>0\<Colon>'a\<bar> = \<bar>X3\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis abs_minus_cancel 24)
have 26: "\<And>X3. (0\<Colon>'a) = \<bar>X3\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis 25 8)
have 27: "\<And>X1 X3. (0\<Colon>'a) * \<bar>X1\<bar> = \<bar>X3 * X1\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis abs_mult 26)
have 28: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis 27 mult_cancel_left1)
have 29: "\<And>X1 X3. (0\<Colon>'a) = X3 * X1 \<or> (0\<Colon>'a) < (0\<Colon>'a) \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis zero_less_abs_iff 28)
have 30: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis 29 9)
have 31: "\<And>X1 X3. (0\<Colon>'a) = X1 * X3 \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis AC_mult.f.commute 30)
have 32: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<bar>X1\<bar> \<noteq> (0\<Colon>'a)"
  by (metis abs_mult 31)
have 33: "\<And>X3::'a. \<bar>X3 * X3\<bar> = X3 * X3"
  by (metis abs_mult_self abs_mult AC_mult.f.commute)
have 34: "\<And>X3. (0\<Colon>'a) \<le> \<bar>X3\<bar> \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_ge_zero abs_mult_pos 20)
have 35: "\<And>X3. (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis 34 22)
have 36: "\<And>X3. X3 * (1\<Colon>'a) = (0\<Colon>'a) \<or> \<bar>X3\<bar> \<noteq> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_eq_0 abs_mult_pos 20)
have 37: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<bar>X3\<bar> \<noteq> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis 36 20)
have 38: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<bar>X3\<bar> \<noteq> (0\<Colon>'a)"
  by (metis 37 22)
have 39: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> \<bar>X1\<bar> \<noteq> (0\<Colon>'a)"
  by (metis 38 32)
have 40: "\<And>X3::'a. \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar> \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_idempotent abs_mult_pos 20)
have 41: "\<And>X3::'a. \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar>"
  by (metis 40 22)
have 42: "\<And>X3. \<not> \<bar>X3\<bar> < (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_not_less_zero abs_mult_pos 20)
have 43: "\<And>X3. \<not> \<bar>X3\<bar> < (0\<Colon>'a)"
  by (metis 42 22)
have 44: "\<And>X3. X3 * (1\<Colon>'a) = (0\<Colon>'a) \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_le_zero_iff abs_mult_pos 20)
have 45: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis 44 20)
have 46: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a)"
  by (metis 45 22)
have 47: "\<And>X3. X3 * X3 = (0\<Colon>'a) \<or> \<not> X3 * X3 \<le> (0\<Colon>'a)"
  by (metis 46 33)
have 48: "\<And>X3. X3 * X3 = (0\<Colon>'a) \<or> \<not> X3 \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> X3"
  by (metis 47 mult_le_0_iff)
have 49: "\<And>X3. \<bar>X3\<bar> = (0\<Colon>'a) \<or> \<not> X3 \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> X3"
  by (metis mult_eq_0_iff abs_mult_self 48)
have 50: "\<And>X1 X3.
   (0\<Colon>'a) * \<bar>X1\<bar> = \<bar>\<bar>X3 * X1\<bar>\<bar> \<or>
   \<not> (0\<Colon>'a) \<le> \<bar>X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis abs_mult_pos abs_mult 49)
have 51: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> \<not> X1 \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> X1"
  by (metis 39 49)
have 52: "\<And>X1 X3.
   (0\<Colon>'a) = \<bar>\<bar>X3 * X1\<bar>\<bar> \<or>
   \<not> (0\<Colon>'a) \<le> \<bar>X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis 50 mult_cancel_left1)
have 53: "\<And>X1 X3.
   (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<not> (0\<Colon>'a) \<le> \<bar>X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis 52 41)
have 54: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis 53 35)
have 55: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a)"
  by (metis 54 35)
have 56: "\<And>X1 X3. \<bar>X1 * X3\<bar> = (0\<Colon>'a) \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a)"
  by (metis 55 AC_mult.f.commute)
have 57: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> \<not> \<bar>X1\<bar> \<le> (0\<Colon>'a)"
  by (metis 38 56)
have 58: "\<And>X3. \<bar>h X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> \<bar>f X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> \<bar>f X3\<bar>"
  by (metis 0 51)
have 59: "\<And>X3. \<bar>h X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> \<bar>f X3\<bar> \<le> (0\<Colon>'a)"
  by (metis 58 35)
have 60: "\<And>X3. \<bar>h X3\<bar> \<le> (0\<Colon>'a) \<or> (0\<Colon>'a) < \<bar>f X3\<bar>"
  by (metis 59 linorder_not_le)
have 61: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> (0\<Colon>'a) < \<bar>X1\<bar>"
  by (metis 57 linorder_not_le)
have 62: "(0\<Colon>'a) < \<bar>\<bar>f x\<bar>\<bar> \<or> \<not> \<bar>h x\<bar> \<le> (0\<Colon>'a)"
  by (metis 19 61)
have 63: "(0\<Colon>'a) < \<bar>f x\<bar> \<or> \<not> \<bar>h x\<bar> \<le> (0\<Colon>'a)"
  by (metis 62 41)
have 64: "(0\<Colon>'a) < \<bar>f x\<bar>"
  by (metis 63 60)
have 65: "\<And>X3. \<bar>h X3\<bar> < (0\<Colon>'a) \<or> \<not> c < (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) < \<bar>f X3\<bar>"
  by (metis 3 mult_less_0_iff)
have 66: "\<And>X3. \<bar>h X3\<bar> < (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) < \<bar>f X3\<bar>"
  by (metis 65 18)
have 67: "\<And>X3. \<not> (0\<Colon>'a) < \<bar>f X3\<bar>"
  by (metis 66 43)
show "False"
  by (metis 67 64)
qed

lemma (*bigo_pos_const:*) "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto);
ML{*ResReconstruct.modulus:=2*}
proof (neg_clausify)
fix c x
assume 0: "\<And>A. \<bar>h A\<bar> \<le> c * \<bar>f A\<bar>"
assume 1: "c \<noteq> (0\<Colon>'a::ordered_idom)"
assume 2: "\<not> \<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>"
have 3: "\<And>X3. (1\<Colon>'a) * X3 \<le> X3"
  by (metis mult_le_cancel_right2 order_refl order_refl)
have 4: "\<bar>0\<Colon>'a\<bar> = (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (0\<Colon>'a)"
  by (metis abs_mult_pos mult_cancel_right1 mult_cancel_right1)
have 5: "\<not> (0\<Colon>'a) < (0\<Colon>'a)"
  by (metis abs_not_less_zero 4 order_refl)
have 6: "(0\<Colon>'a) = - ((1\<Colon>'a) * (0\<Colon>'a))"
  by (metis abs_of_nonpos 3 mult_cancel_right1 4 order_refl)
have 7: "\<And>X3. \<bar>X3\<bar> = X3 \<or> X3 \<le> (0\<Colon>'a)"
  by (metis abs_of_nonneg linorder_linear)
have 8: "c \<le> (0\<Colon>'a)"
  by (metis 2 7 0)
have 9: "\<bar>c\<bar> = - c"
  by (metis abs_of_nonpos 8)
have 10: "\<not> \<bar>h x\<bar> \<le> - c * \<bar>f x\<bar>"
  by (metis 2 9)
have 11: "\<And>X3. X3 * (1\<Colon>'a) = X3"
  by (metis mult_cancel_right1 AC_mult.f.commute)
have 12: "(0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis zero_le_square AC_mult.f.commute mult_cancel_left1)
have 13: "\<And>X3. (0\<Colon>'a) = - X3 \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis neg_equal_iff_equal 6 mult_cancel_right1 minus_equation_iff)
have 14: "\<And>X3. (0\<Colon>'a) = \<bar>X3\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis abs_minus_cancel 13 4 order_refl)
have 15: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis abs_mult 14 mult_cancel_left1)
have 16: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis zero_less_abs_iff 15 5)
have 17: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<bar>X1\<bar> \<noteq> (0\<Colon>'a)"
  by (metis abs_mult AC_mult.f.commute 16)
have 18: "\<And>X3. (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis abs_ge_zero abs_mult_pos 11 12)
have 19: "\<And>X3. X3 * (1\<Colon>'a) = (0\<Colon>'a) \<or> \<bar>X3\<bar> \<noteq> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_eq_0 abs_mult_pos 11)
have 20: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<bar>X3\<bar> \<noteq> (0\<Colon>'a)"
  by (metis 19 11 12)
have 21: "\<And>X3::'a. \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar> \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_idempotent abs_mult_pos 11)
have 22: "\<And>X3. \<not> \<bar>X3\<bar> < (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_not_less_zero abs_mult_pos 11)
have 23: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_le_zero_iff abs_mult_pos 11 11)
have 24: "\<And>X3. X3 * X3 = (0\<Colon>'a) \<or> \<not> X3 * X3 \<le> (0\<Colon>'a)"
  by (metis 23 12 abs_mult_self abs_mult AC_mult.f.commute)
have 25: "\<And>X3. \<bar>X3\<bar> = (0\<Colon>'a) \<or> \<not> X3 \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> X3"
  by (metis mult_eq_0_iff abs_mult_self 24 mult_le_0_iff)
have 26: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> \<not> X1 \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> X1"
  by (metis 20 17 25)
have 27: "\<And>X1 X3.
   (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<not> (0\<Colon>'a) \<le> \<bar>X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis abs_mult_pos abs_mult 25 mult_cancel_left1 21 12)
have 28: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a)"
  by (metis 27 18 18)
have 29: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> \<not> \<bar>X1\<bar> \<le> (0\<Colon>'a)"
  by (metis 20 28 AC_mult.f.commute)
have 30: "\<And>X3. \<bar>h X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> \<bar>f X3\<bar> \<le> (0\<Colon>'a)"
  by (metis 0 26 18)
have 31: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> (0\<Colon>'a) < \<bar>X1\<bar>"
  by (metis 29 linorder_not_le)
have 32: "(0\<Colon>'a) < \<bar>f x\<bar> \<or> \<not> \<bar>h x\<bar> \<le> (0\<Colon>'a)"
  by (metis 10 31 21 12)
have 33: "\<And>X3. \<bar>h X3\<bar> < (0\<Colon>'a) \<or> \<not> c < (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) < \<bar>f X3\<bar>"
  by (metis order_le_less_trans 0 mult_less_0_iff)
have 34: "\<And>X3. \<not> (0\<Colon>'a) < \<bar>f X3\<bar>"
  by (metis 33 linorder_antisym_conv2 8 1 22 12)
show "False"
  by (metis 34 32 30 linorder_not_le)
qed

lemma (*bigo_pos_const:*) "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto);
ML{*ResReconstruct.modulus:=3*}
proof (neg_clausify)
fix c x
assume 0: "\<And>A\<Colon>'b\<Colon>type.
   \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) A\<bar>
   \<le> (c\<Colon>'a\<Colon>ordered_idom) * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) A\<bar>"
assume 1: "(c\<Colon>'a\<Colon>ordered_idom) \<noteq> (0\<Colon>'a\<Colon>ordered_idom)"
assume 2: "\<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>
  \<le> \<bar>c\<Colon>'a\<Colon>ordered_idom\<bar> * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
have 3: "\<And>X3\<Colon>'a\<Colon>ordered_idom. (1\<Colon>'a\<Colon>ordered_idom) * X3 \<le> X3"
  by (metis mult_le_cancel_right2 order_refl order_refl)
have 4: "\<bar>0\<Colon>'a\<Colon>ordered_idom\<bar> = (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_mult_pos mult_cancel_right1 mult_cancel_right1 order_refl)
have 5: "(0\<Colon>'a\<Colon>ordered_idom) = - ((1\<Colon>'a\<Colon>ordered_idom) * (0\<Colon>'a\<Colon>ordered_idom))"
  by (metis abs_of_nonpos 3 mult_cancel_right1 4)
have 6: "(c\<Colon>'a\<Colon>ordered_idom) \<le> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis 2 abs_of_nonneg linorder_linear 0)
have 7: "(c\<Colon>'a\<Colon>ordered_idom) < (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis linorder_antisym_conv2 6 1)
have 8: "\<And>X3\<Colon>'a\<Colon>ordered_idom. X3 * (1\<Colon>'a\<Colon>ordered_idom) = X3"
  by (metis mult_cancel_right1 AC_mult.f.commute)
have 9: "\<And>X3\<Colon>'a\<Colon>ordered_idom. (0\<Colon>'a\<Colon>ordered_idom) = X3 \<or> (0\<Colon>'a\<Colon>ordered_idom) \<noteq> - X3"
  by (metis neg_equal_iff_equal 5 mult_cancel_right1)
have 10: "\<And>X3\<Colon>'a\<Colon>ordered_idom. (0\<Colon>'a\<Colon>ordered_idom) = \<bar>X3\<bar> \<or> X3 \<noteq> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_minus_cancel 9 minus_equation_iff 4)
have 11: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X3\<Colon>'a\<Colon>ordered_idom.
   (0\<Colon>'a\<Colon>ordered_idom) * \<bar>X1\<bar> = \<bar>X3 * X1\<bar> \<or> X3 \<noteq> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_mult 10)
have 12: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X3\<Colon>'a\<Colon>ordered_idom.
   X3 * X1 = (0\<Colon>'a\<Colon>ordered_idom) \<or> X3 \<noteq> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis zero_less_abs_iff 11 mult_cancel_left1 abs_not_less_zero 4)
have 13: "\<And>X3\<Colon>'a\<Colon>ordered_idom. \<bar>X3 * X3\<bar> = X3 * X3"
  by (metis abs_mult_self abs_mult AC_mult.f.commute)
have 14: "\<And>X3\<Colon>'a\<Colon>ordered_idom. (0\<Colon>'a\<Colon>ordered_idom) \<le> \<bar>X3\<bar>"
  by (metis abs_ge_zero abs_mult_pos 8 zero_le_square AC_mult.f.commute mult_cancel_left1)
have 15: "\<And>X3\<Colon>'a\<Colon>ordered_idom.
   X3 = (0\<Colon>'a\<Colon>ordered_idom) \<or>
   \<bar>X3\<bar> \<noteq> (0\<Colon>'a\<Colon>ordered_idom) \<or> \<not> (0\<Colon>'a\<Colon>ordered_idom) \<le> (1\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_eq_0 abs_mult_pos 8 8)
have 16: "\<And>X3\<Colon>'a\<Colon>ordered_idom.
   \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar> \<or> \<not> (0\<Colon>'a\<Colon>ordered_idom) \<le> (1\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_idempotent abs_mult_pos 8)
have 17: "\<And>X3\<Colon>'a\<Colon>ordered_idom. \<not> \<bar>X3\<bar> < (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_not_less_zero abs_mult_pos 8 zero_le_square AC_mult.f.commute mult_cancel_left1)
have 18: "\<And>X3\<Colon>'a\<Colon>ordered_idom.
   X3 = (0\<Colon>'a\<Colon>ordered_idom) \<or>
   \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or>
   \<not> (0\<Colon>'a\<Colon>ordered_idom) \<le> (1\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_le_zero_iff abs_mult_pos 8 8)
have 19: "\<And>X3\<Colon>'a\<Colon>ordered_idom.
   X3 * X3 = (0\<Colon>'a\<Colon>ordered_idom) \<or>
   \<not> X3 \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or> \<not> (0\<Colon>'a\<Colon>ordered_idom) \<le> X3"
  by (metis 18 zero_le_square AC_mult.f.commute mult_cancel_left1 13 mult_le_0_iff)
have 20: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X3\<Colon>'a\<Colon>ordered_idom.
   X3 * X1 = (0\<Colon>'a\<Colon>ordered_idom) \<or>
   \<not> X1 \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or> \<not> (0\<Colon>'a\<Colon>ordered_idom) \<le> X1"
  by (metis 15 zero_le_square AC_mult.f.commute mult_cancel_left1 abs_mult AC_mult.f.commute 12 mult_eq_0_iff abs_mult_self 19)
have 21: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X3\<Colon>'a\<Colon>ordered_idom.
   (0\<Colon>'a\<Colon>ordered_idom) = \<bar>X3 * X1\<bar> \<or>
   \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or> \<not> (0\<Colon>'a\<Colon>ordered_idom) \<le> \<bar>X3\<bar>"
  by (metis abs_mult_pos abs_mult mult_eq_0_iff abs_mult_self 19 mult_cancel_left1 16 zero_le_square AC_mult.f.commute mult_cancel_left1 14)
have 22: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X3\<Colon>'a\<Colon>ordered_idom.
   X3 * X1 = (0\<Colon>'a\<Colon>ordered_idom) \<or> \<not> \<bar>X1\<bar> \<le> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis 15 zero_le_square AC_mult.f.commute mult_cancel_left1 21 14 AC_mult.f.commute)
have 23: "\<And>X3\<Colon>'b\<Colon>type.
   \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X3\<bar> \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or>
   (0\<Colon>'a\<Colon>ordered_idom) < \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X3\<bar>"
  by (metis 0 20 14 linorder_not_le)
have 24: "(0\<Colon>'a\<Colon>ordered_idom) < \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar> \<or>
\<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar> \<le> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis 2 abs_of_nonpos 6 22 linorder_not_le 16 zero_le_square AC_mult.f.commute mult_cancel_left1)
have 25: "\<And>X3\<Colon>'b\<Colon>type.
   \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X3\<bar> < (0\<Colon>'a\<Colon>ordered_idom) \<or>
   \<not> (0\<Colon>'a\<Colon>ordered_idom) < \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X3\<bar>"
  by (metis order_le_less_trans 0 mult_less_0_iff 7)
show "False"
  by (metis 25 17 24 23)
qed

lemma (*bigo_pos_const:*) "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto);
ML{*ResReconstruct.modulus:=4*}
ML{*ResReconstruct.recon_sorts:=false*}
proof (neg_clausify)
fix c x
assume 0: "\<And>A. \<bar>h A\<bar> \<le> c * \<bar>f A\<bar>"
assume 1: "c \<noteq> (0\<Colon>'a)"
assume 2: "\<not> \<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>"
have 3: "\<And>X3. (1\<Colon>'a) * X3 \<le> X3"
  by (metis mult_le_cancel_right2 order_refl order_refl)
have 4: "\<not> (0\<Colon>'a) < (0\<Colon>'a)"
  by (metis abs_not_less_zero abs_mult_pos mult_cancel_right1 mult_cancel_right1 order_refl)
have 5: "c \<le> (0\<Colon>'a)"
  by (metis 2 abs_of_nonneg linorder_linear 0)
have 6: "\<not> \<bar>h x\<bar> \<le> - c * \<bar>f x\<bar>"
  by (metis 2 abs_of_nonpos 5)
have 7: "(0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis zero_le_square AC_mult.f.commute mult_cancel_left1)
have 8: "\<And>X3. (0\<Colon>'a) = \<bar>X3\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis abs_minus_cancel neg_equal_iff_equal abs_of_nonpos 3 mult_cancel_right1 abs_mult_pos mult_cancel_right1 mult_cancel_right1 order_refl mult_cancel_right1 minus_equation_iff abs_mult_pos mult_cancel_right1 mult_cancel_right1 order_refl)
have 9: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> X3 \<noteq> (0\<Colon>'a)"
  by (metis abs_mult 8 mult_cancel_left1)
have 10: "\<And>X1 X3. (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<bar>X1\<bar> \<noteq> (0\<Colon>'a)"
  by (metis abs_mult AC_mult.f.commute zero_less_abs_iff 9 4)
have 11: "\<And>X3. (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis abs_ge_zero abs_mult_pos mult_cancel_right1 AC_mult.f.commute 7)
have 12: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<bar>X3\<bar> \<noteq> (0\<Colon>'a)"
  by (metis abs_eq_0 abs_mult_pos mult_cancel_right1 AC_mult.f.commute mult_cancel_right1 AC_mult.f.commute 7)
have 13: "\<And>X3. \<not> \<bar>X3\<bar> < (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_not_less_zero abs_mult_pos mult_cancel_right1 AC_mult.f.commute)
have 14: "\<And>X3. X3 = (0\<Colon>'a) \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> (1\<Colon>'a)"
  by (metis abs_le_zero_iff abs_mult_pos mult_cancel_right1 AC_mult.f.commute mult_cancel_right1 AC_mult.f.commute)
have 15: "\<And>X3. \<bar>X3\<bar> = (0\<Colon>'a) \<or> \<not> X3 \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> X3"
  by (metis mult_eq_0_iff abs_mult_self 14 7 abs_mult_self abs_mult AC_mult.f.commute mult_le_0_iff)
have 16: "\<And>X1 X3.
   (0\<Colon>'a) = \<bar>X3 * X1\<bar> \<or> \<not> (0\<Colon>'a) \<le> \<bar>X1\<bar> \<or> \<not> \<bar>X3\<bar> \<le> (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) \<le> \<bar>X3\<bar>"
  by (metis abs_mult_pos abs_mult 15 mult_cancel_left1 abs_idempotent abs_mult_pos mult_cancel_right1 AC_mult.f.commute 7)
have 17: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> \<not> \<bar>X1\<bar> \<le> (0\<Colon>'a)"
  by (metis 12 16 11 11 AC_mult.f.commute)
have 18: "\<And>X1 X3. X3 * X1 = (0\<Colon>'a) \<or> (0\<Colon>'a) < \<bar>X1\<bar>"
  by (metis 17 linorder_not_le)
have 19: "\<And>X3. \<bar>h X3\<bar> < (0\<Colon>'a) \<or> \<not> c < (0\<Colon>'a) \<or> \<not> (0\<Colon>'a) < \<bar>f X3\<bar>"
  by (metis order_le_less_trans 0 mult_less_0_iff)
show "False"
  by (metis 19 linorder_antisym_conv2 5 1 13 7 6 18 abs_idempotent abs_mult_pos mult_cancel_right1 AC_mult.f.commute 7 0 12 10 15 11 linorder_not_le)
qed


ML{*ResReconstruct.modulus:=1*}
ML{*ResReconstruct.recon_sorts:=true*}

lemma bigo_alt_def: "O(f) = 
    {h. EX c. (0 < c & (ALL x. abs (h x) <= c * abs (f x)))}"
by (auto simp add: bigo_def bigo_pos_const)

ML{*ResAtp.problem_name := "BigO__bigo_elt_subset"*}
lemma bigo_elt_subset [intro]: "f : O(g) ==> O(f) <= O(g)"
  apply (auto simp add: bigo_alt_def)
  apply (rule_tac x = "ca * c" in exI)
  apply (rule conjI)
  apply (rule mult_pos_pos)
  apply (assumption)+ 
(*sledgehammer*);
  apply (rule allI)
  apply (drule_tac x = "xa" in spec)+
  apply (subgoal_tac "ca * abs(f xa) <= ca * (c * abs(g xa))");
  apply (erule order_trans)
  apply (simp add: mult_ac)
  apply (rule mult_left_mono, assumption)
  apply (rule order_less_imp_le, assumption);
done


ML{*ResAtp.problem_name := "BigO__bigo_refl"*}
lemma bigo_refl [intro]: "f : O(f)"
  apply(auto simp add: bigo_def)
proof (neg_clausify)
fix x
assume 0: "\<And>mes_pSG\<Colon>'b\<Colon>ordered_idom.
   \<not> \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) mes_pSG)\<bar>
     \<le> mes_pSG * \<bar>f (x mes_pSG)\<bar>"
have 1: "\<And>X3\<Colon>'b. X3 \<le> (1\<Colon>'b) * X3 \<or> \<not> (1\<Colon>'b) \<le> (1\<Colon>'b)"
  by (metis Ring_and_Field.mult_le_cancel_right1 order_refl)
have 2: "\<And>X3\<Colon>'b. X3 \<le> (1\<Colon>'b) * X3"
  by (metis 1 order_refl)
show 3: "False"
  by (metis 0 2)
qed

ML{*ResAtp.problem_name := "BigO__bigo_zero"*}
lemma bigo_zero: "0 : O(g)"
  apply (auto simp add: bigo_def func_zero)
proof (neg_clausify)
fix x
assume 0: "\<And>mes_mVM\<Colon>'b\<Colon>ordered_idom.
   \<not> (0\<Colon>'b\<Colon>ordered_idom)
     \<le> mes_mVM *
       \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom)
         ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) mes_mVM)\<bar>"
have 1: "(0\<Colon>'b\<Colon>ordered_idom) < (0\<Colon>'b\<Colon>ordered_idom)"
  by (metis 0 Ring_and_Field.mult_le_cancel_left1)
show 2: "False"
  by (metis Orderings.linorder_class.neq_iff 1)
qed

lemma bigo_zero2: "O(%x.0) = {%x.0}"
  apply (auto simp add: bigo_def) 
  apply (rule ext)
  apply auto
done

lemma bigo_plus_self_subset [intro]: 
  "O(f) + O(f) <= O(f)"
  apply (auto simp add: bigo_alt_def set_plus)
  apply (rule_tac x = "c + ca" in exI)
  apply auto
  apply (simp add: ring_distribs func_plus)
  apply (blast intro:order_trans abs_triangle_ineq add_mono elim:) 
done

lemma bigo_plus_idemp [simp]: "O(f) + O(f) = O(f)"
  apply (rule equalityI)
  apply (rule bigo_plus_self_subset)
  apply (rule set_zero_plus2) 
  apply (rule bigo_zero)
done

lemma bigo_plus_subset [intro]: "O(f + g) <= O(f) + O(g)"
  apply (rule subsetI)
  apply (auto simp add: bigo_def bigo_pos_const func_plus set_plus)
  apply (subst bigo_pos_const [symmetric])+
  apply (rule_tac x = 
    "%n. if abs (g n) <= (abs (f n)) then x n else 0" in exI)
  apply (rule conjI)
  apply (rule_tac x = "c + c" in exI)
  apply (clarsimp)
  apply (auto)
  apply (subgoal_tac "c * abs (f xa + g xa) <= (c + c) * abs (f xa)")
  apply (erule_tac x = xa in allE)
  apply (erule order_trans)
  apply (simp)
  apply (subgoal_tac "c * abs (f xa + g xa) <= c * (abs (f xa) + abs (g xa))")
  apply (erule order_trans)
  apply (simp add: ring_distribs)
  apply (rule mult_left_mono)
  apply assumption
  apply (simp add: order_less_le)
  apply (rule mult_left_mono)
  apply (simp add: abs_triangle_ineq)
  apply (simp add: order_less_le)
  apply (rule mult_nonneg_nonneg)
  apply (rule add_nonneg_nonneg)
  apply auto
  apply (rule_tac x = "%n. if (abs (f n)) <  abs (g n) then x n else 0" 
     in exI)
  apply (rule conjI)
  apply (rule_tac x = "c + c" in exI)
  apply auto
  apply (subgoal_tac "c * abs (f xa + g xa) <= (c + c) * abs (g xa)")
  apply (erule_tac x = xa in allE)
  apply (erule order_trans)
  apply (simp)
  apply (subgoal_tac "c * abs (f xa + g xa) <= c * (abs (f xa) + abs (g xa))")
  apply (erule order_trans)
  apply (simp add: ring_distribs)
  apply (rule mult_left_mono)
  apply (simp add: order_less_le)
  apply (simp add: order_less_le)
  apply (rule mult_left_mono)
  apply (rule abs_triangle_ineq)
  apply (simp add: order_less_le)
  apply (rule mult_nonneg_nonneg)
  apply (rule add_nonneg_nonneg)
  apply (erule order_less_imp_le)+
  apply simp
  apply (rule ext)
  apply (auto simp add: if_splits linorder_not_le)
done

lemma bigo_plus_subset2 [intro]: "A <= O(f) ==> B <= O(f) ==> A + B <= O(f)"
  apply (subgoal_tac "A + B <= O(f) + O(f)")
  apply (erule order_trans)
  apply simp
  apply (auto del: subsetI simp del: bigo_plus_idemp)
done

ML{*ResAtp.problem_name := "BigO__bigo_plus_eq"*}
lemma bigo_plus_eq: "ALL x. 0 <= f x ==> ALL x. 0 <= g x ==> 
  O(f + g) = O(f) + O(g)"
  apply (rule equalityI)
  apply (rule bigo_plus_subset)
  apply (simp add: bigo_alt_def set_plus func_plus)
  apply clarify 
(*sledgehammer*); 
  apply (rule_tac x = "max c ca" in exI)
  apply (rule conjI)
  apply (subgoal_tac "c <= max c ca")
  apply (erule order_less_le_trans)
  apply assumption
  apply (rule le_maxI1)
  apply clarify
  apply (drule_tac x = "xa" in spec)+
  apply (subgoal_tac "0 <= f xa + g xa")
  apply (simp add: ring_distribs)
  apply (subgoal_tac "abs(a xa + b xa) <= abs(a xa) + abs(b xa)")
  apply (subgoal_tac "abs(a xa) + abs(b xa) <= 
      max c ca * f xa + max c ca * g xa")
  apply (blast intro: order_trans)
  defer 1
  apply (rule abs_triangle_ineq)
  apply (rule add_nonneg_nonneg)
  apply assumption+
  apply (rule add_mono)
ML{*ResAtp.problem_name := "BigO__bigo_plus_eq_simpler"*} 
(*sledgehammer...fails*); 
  apply (subgoal_tac "c * f xa <= max c ca * f xa")
  apply (blast intro: order_trans)
  apply (rule mult_right_mono)
  apply (rule le_maxI1)
  apply assumption
  apply (subgoal_tac "ca * g xa <= max c ca * g xa")
  apply (blast intro: order_trans)
  apply (rule mult_right_mono)
  apply (rule le_maxI2)
  apply assumption
done

ML{*ResAtp.problem_name := "BigO__bigo_bounded_alt"*}
lemma bigo_bounded_alt: "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> 
    f : O(g)" 
  apply (auto simp add: bigo_def)
(*Version 1: one-shot proof*)
  apply (metis OrderedGroup.abs_ge_self  OrderedGroup.abs_le_D1  OrderedGroup.abs_of_nonneg  Orderings.linorder_class.not_less  order_less_le  Orderings.xt1(12)  Ring_and_Field.abs_mult)
  done

lemma bigo_bounded_alt: "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> 
    f : O(g)" 
  apply (auto simp add: bigo_def)
(*Version 2: single-step proof*)
proof (neg_clausify)
fix x
assume 0: "\<And>mes_mbt\<Colon>'a.
   (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) mes_mbt
   \<le> (c\<Colon>'b\<Colon>ordered_idom) * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) mes_mbt"
assume 1: "\<And>mes_mbs\<Colon>'b\<Colon>ordered_idom.
   \<not> (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) mes_mbs)
     \<le> mes_mbs * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x mes_mbs)\<bar>"
have 2: "\<And>X3\<Colon>'a.
   (c\<Colon>'b\<Colon>ordered_idom) * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) X3 =
   (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) X3 \<or>
   \<not> c * g X3 \<le> f X3"
  by (metis Lattices.min_max.less_eq_less_inf.antisym_intro 0)
have 3: "\<And>X3\<Colon>'b\<Colon>ordered_idom.
   \<not> (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>X3\<bar>)
     \<le> \<bar>X3 * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>X3\<bar>)\<bar>"
  by (metis 1 Ring_and_Field.abs_mult)
have 4: "\<And>X3\<Colon>'b\<Colon>ordered_idom. (1\<Colon>'b\<Colon>ordered_idom) * X3 = X3"
  by (metis Ring_and_Field.mult_cancel_left2 Finite_Set.AC_mult.f.commute)
have 5: "\<And>X3\<Colon>'b\<Colon>ordered_idom. X3 * (1\<Colon>'b\<Colon>ordered_idom) = X3"
  by (metis Ring_and_Field.mult_cancel_right2 Finite_Set.AC_mult.f.commute)
have 6: "\<And>X3\<Colon>'b\<Colon>ordered_idom. \<bar>X3\<bar> * \<bar>X3\<bar> = X3 * X3"
  by (metis Ring_and_Field.abs_mult_self Finite_Set.AC_mult.f.commute)
have 7: "\<And>X3\<Colon>'b\<Colon>ordered_idom. (0\<Colon>'b\<Colon>ordered_idom) \<le> X3 * X3"
  by (metis Ring_and_Field.zero_le_square Finite_Set.AC_mult.f.commute)
have 8: "(0\<Colon>'b\<Colon>ordered_idom) \<le> (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis 7 Ring_and_Field.mult_cancel_left2)
have 9: "\<And>X3\<Colon>'b\<Colon>ordered_idom. X3 * X3 = \<bar>X3 * X3\<bar>"
  by (metis Ring_and_Field.abs_mult 6)
have 10: "\<bar>1\<Colon>'b\<Colon>ordered_idom\<bar> = (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis 9 4)
have 11: "\<And>X3\<Colon>'b\<Colon>ordered_idom. \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar> * \<bar>1\<Colon>'b\<Colon>ordered_idom\<bar>"
  by (metis Ring_and_Field.abs_mult OrderedGroup.abs_idempotent 5)
have 12: "\<And>X3\<Colon>'b\<Colon>ordered_idom. \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar>"
  by (metis 11 10 5)
have 13: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom.
   X3 * (1\<Colon>'b\<Colon>ordered_idom) \<le> X1 \<or>
   \<not> \<bar>X3\<bar> \<le> X1 \<or> \<not> (0\<Colon>'b\<Colon>ordered_idom) \<le> (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis OrderedGroup.abs_le_D1 Ring_and_Field.abs_mult_pos 5)
have 14: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom.
   X3 \<le> X1 \<or> \<not> \<bar>X3\<bar> \<le> X1 \<or> \<not> (0\<Colon>'b\<Colon>ordered_idom) \<le> (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis 13 5)
have 15: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. X3 \<le> X1 \<or> \<not> \<bar>X3\<bar> \<le> X1"
  by (metis 14 8)
have 16: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. X3 \<le> X1 \<or> X1 \<le> \<bar>X3\<bar>"
  by (metis 15 Orderings.linorder_class.less_eq_less.linear)
have 17: "\<And>X3\<Colon>'b\<Colon>ordered_idom.
   X3 * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>X3\<bar>)
   \<le> (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>X3\<bar>)"
  by (metis 3 16)
have 18: "(c\<Colon>'b\<Colon>ordered_idom) *
(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>c\<bar>) =
(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>c\<bar>)"
  by (metis 2 17)
have 19: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. \<bar>X3 * X1\<bar> \<le> \<bar>\<bar>X3\<bar>\<bar> * \<bar>\<bar>X1\<bar>\<bar>"
  by (metis 15 Ring_and_Field.abs_le_mult Ring_and_Field.abs_mult)
have 20: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. \<bar>X3 * X1\<bar> \<le> \<bar>X3\<bar> * \<bar>X1\<bar>"
  by (metis 19 12 12)
have 21: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. X3 * X1 \<le> \<bar>X3\<bar> * \<bar>X1\<bar>"
  by (metis 15 20)
have 22: "(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom)
 ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>c\<Colon>'b\<Colon>ordered_idom\<bar>)
\<le> \<bar>c\<bar> * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>c\<bar>)\<bar>"
  by (metis 21 18)
show 23: "False"
  by (metis 22 1)
qed


text{*So here is the easier (and more natural) problem using transitivity*}
ML{*ResAtp.problem_name := "BigO__bigo_bounded_alt_trans"*}
lemma "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> f : O(g)" 
  apply (auto simp add: bigo_def)
  (*Version 1: one-shot proof*) 
apply (metis Orderings.leD Orderings.leI abs_ge_self abs_le_D1 abs_mult abs_of_nonneg order_le_less xt1(12));
  done

text{*So here is the easier (and more natural) problem using transitivity*}
ML{*ResAtp.problem_name := "BigO__bigo_bounded_alt_trans"*}
lemma "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> f : O(g)" 
  apply (auto simp add: bigo_def)
(*Version 2: single-step proof*)
proof (neg_clausify)
fix x
assume 0: "\<And>mes_mb9\<Colon>'a.
   (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) mes_mb9
   \<le> (c\<Colon>'b\<Colon>ordered_idom) * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) mes_mb9"
assume 1: "\<And>mes_mb8\<Colon>'b\<Colon>ordered_idom.
   \<not> (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) mes_mb8)
     \<le> mes_mb8 * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x mes_mb8)\<bar>"
have 2: "\<And>X3\<Colon>'a.
   (c\<Colon>'b\<Colon>ordered_idom) * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) X3 =
   (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) X3 \<or>
   \<not> c * g X3 \<le> f X3"
  by (metis Lattices.min_max.less_eq_less_inf.antisym_intro 0)
have 3: "\<And>X3\<Colon>'b\<Colon>ordered_idom.
   \<not> (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>X3\<bar>)
     \<le> \<bar>X3 * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>X3\<bar>)\<bar>"
  by (metis 1 Ring_and_Field.abs_mult)
have 4: "\<And>X3\<Colon>'b\<Colon>ordered_idom. (1\<Colon>'b\<Colon>ordered_idom) * X3 = X3"
  by (metis Ring_and_Field.mult_cancel_left2 Finite_Set.AC_mult.f.commute)
have 5: "\<And>X3\<Colon>'b\<Colon>ordered_idom. X3 * (1\<Colon>'b\<Colon>ordered_idom) = X3"
  by (metis Ring_and_Field.mult_cancel_right2 Finite_Set.AC_mult.f.commute)
have 6: "\<And>X3\<Colon>'b\<Colon>ordered_idom. \<bar>X3\<bar> * \<bar>X3\<bar> = X3 * X3"
  by (metis Ring_and_Field.abs_mult_self Finite_Set.AC_mult.f.commute)
have 7: "\<And>X3\<Colon>'b\<Colon>ordered_idom. (0\<Colon>'b\<Colon>ordered_idom) \<le> X3 * X3"
  by (metis Ring_and_Field.zero_le_square Finite_Set.AC_mult.f.commute)
have 8: "(0\<Colon>'b\<Colon>ordered_idom) \<le> (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis 7 Ring_and_Field.mult_cancel_left2)
have 9: "\<And>X3\<Colon>'b\<Colon>ordered_idom. X3 * X3 = \<bar>X3 * X3\<bar>"
  by (metis Ring_and_Field.abs_mult 6)
have 10: "\<bar>1\<Colon>'b\<Colon>ordered_idom\<bar> = (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis 9 4)
have 11: "\<And>X3\<Colon>'b\<Colon>ordered_idom. \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar> * \<bar>1\<Colon>'b\<Colon>ordered_idom\<bar>"
  by (metis Ring_and_Field.abs_mult OrderedGroup.abs_idempotent 5)
have 12: "\<And>X3\<Colon>'b\<Colon>ordered_idom. \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar>"
  by (metis 11 10 5)
have 13: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom.
   X3 * (1\<Colon>'b\<Colon>ordered_idom) \<le> X1 \<or>
   \<not> \<bar>X3\<bar> \<le> X1 \<or> \<not> (0\<Colon>'b\<Colon>ordered_idom) \<le> (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis OrderedGroup.abs_le_D1 Ring_and_Field.abs_mult_pos 5)
have 14: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom.
   X3 \<le> X1 \<or> \<not> \<bar>X3\<bar> \<le> X1 \<or> \<not> (0\<Colon>'b\<Colon>ordered_idom) \<le> (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis 13 5)
have 15: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. X3 \<le> X1 \<or> \<not> \<bar>X3\<bar> \<le> X1"
  by (metis 14 8)
have 16: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. X3 \<le> X1 \<or> X1 \<le> \<bar>X3\<bar>"
  by (metis 15 Orderings.linorder_class.less_eq_less.linear)
have 17: "\<And>X3\<Colon>'b\<Colon>ordered_idom.
   X3 * (g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>X3\<bar>)
   \<le> (f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>X3\<bar>)"
  by (metis 3 16)
have 18: "(c\<Colon>'b\<Colon>ordered_idom) *
(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>c\<bar>) =
(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>c\<bar>)"
  by (metis 2 17)
have 19: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. \<bar>X3 * X1\<bar> \<le> \<bar>\<bar>X3\<bar>\<bar> * \<bar>\<bar>X1\<bar>\<bar>"
  by (metis 15 Ring_and_Field.abs_le_mult Ring_and_Field.abs_mult)
have 20: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. \<bar>X3 * X1\<bar> \<le> \<bar>X3\<bar> * \<bar>X1\<bar>"
  by (metis 19 12 12)
have 21: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X3\<Colon>'b\<Colon>ordered_idom. X3 * X1 \<le> \<bar>X3\<bar> * \<bar>X1\<bar>"
  by (metis 15 20)
have 22: "(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom)
 ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) \<bar>c\<Colon>'b\<Colon>ordered_idom\<bar>)
\<le> \<bar>c\<bar> * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>c\<bar>)\<bar>"
  by (metis 21 18)
show 23: "False"
  by (metis 22 1)
qed


lemma bigo_bounded: "ALL x. 0 <= f x ==> ALL x. f x <= g x ==> 
    f : O(g)" 
  apply (erule bigo_bounded_alt [of f 1 g])
  apply simp
done

ML{*ResAtp.problem_name := "BigO__bigo_bounded2"*}
lemma bigo_bounded2: "ALL x. lb x <= f x ==> ALL x. f x <= lb x + g x ==>
    f : lb +o O(g)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_bounded)
  apply (auto simp add: diff_minus func_minus func_plus)
  prefer 2
  apply (drule_tac x = x in spec)+ 
  apply arith (*not clear that it's provable otherwise*) 
proof (neg_clausify)
fix x
assume 0: "\<And>y. lb y \<le> f y"
assume 1: "\<not> (0\<Colon>'b) \<le> f x + - lb x"
have 2: "\<And>X3. (0\<Colon>'b) + X3 = X3"
  by (metis diff_eq_eq right_minus_eq)
have 3: "\<not> (0\<Colon>'b) \<le> f x - lb x"
  by (metis 1 compare_rls(1))
have 4: "\<not> (0\<Colon>'b) + lb x \<le> f x"
  by (metis 3 le_diff_eq)
show "False"
  by (metis 4 2 0)
qed

ML{*ResAtp.problem_name := "BigO__bigo_abs"*}
lemma bigo_abs: "(%x. abs(f x)) =o O(f)" 
  apply (unfold bigo_def)
  apply auto
proof (neg_clausify)
fix x
assume 0: "!!mes_o43::'b::ordered_idom.
   ~ abs ((f::'a::type => 'b::ordered_idom)
           ((x::'b::ordered_idom => 'a::type) mes_o43))
     <= mes_o43 * abs (f (x mes_o43))"
have 1: "!!X3::'b::ordered_idom.
   X3 <= (1::'b::ordered_idom) * X3 |
   ~ (1::'b::ordered_idom) <= (1::'b::ordered_idom)"
  by (metis mult_le_cancel_right1 order_refl)
have 2: "!!X3::'b::ordered_idom. X3 <= (1::'b::ordered_idom) * X3"
  by (metis 1 order_refl)
show "False"
  by (metis 0 2)
qed

ML{*ResAtp.problem_name := "BigO__bigo_abs2"*}
lemma bigo_abs2: "f =o O(%x. abs(f x))"
  apply (unfold bigo_def)
  apply auto
proof (neg_clausify)
fix x
assume 0: "\<And>mes_o4C\<Colon>'b\<Colon>ordered_idom.
   \<not> \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a) mes_o4C)\<bar>
     \<le> mes_o4C * \<bar>f (x mes_o4C)\<bar>"
have 1: "\<And>X3\<Colon>'b\<Colon>ordered_idom.
   X3 \<le> (1\<Colon>'b\<Colon>ordered_idom) * X3 \<or>
   \<not> (1\<Colon>'b\<Colon>ordered_idom) \<le> (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis mult_le_cancel_right1 order_refl)
have 2: "\<And>X3\<Colon>'b\<Colon>ordered_idom. X3 \<le> (1\<Colon>'b\<Colon>ordered_idom) * X3"
  by (metis 1 order_refl)
show "False"
  by (metis 0 2)
qed
 
lemma bigo_abs3: "O(f) = O(%x. abs(f x))"
  apply (rule equalityI)
  apply (rule bigo_elt_subset)
  apply (rule bigo_abs2)
  apply (rule bigo_elt_subset)
  apply (rule bigo_abs)
done

lemma bigo_abs4: "f =o g +o O(h) ==> 
    (%x. abs (f x)) =o (%x. abs (g x)) +o O(h)"
  apply (drule set_plus_imp_minus)
  apply (rule set_minus_imp_plus)
  apply (subst func_diff)
proof -
  assume a: "f - g : O(h)"
  have "(%x. abs (f x) - abs (g x)) =o O(%x. abs(abs (f x) - abs (g x)))"
    by (rule bigo_abs2)
  also have "... <= O(%x. abs (f x - g x))"
    apply (rule bigo_elt_subset)
    apply (rule bigo_bounded)
    apply force
    apply (rule allI)
    apply (rule abs_triangle_ineq3)
    done
  also have "... <= O(f - g)"
    apply (rule bigo_elt_subset)
    apply (subst func_diff)
    apply (rule bigo_abs)
    done
  also have "... <= O(h)"
    using a by (rule bigo_elt_subset)
  finally show "(%x. abs (f x) - abs (g x)) : O(h)".
qed

lemma bigo_abs5: "f =o O(g) ==> (%x. abs(f x)) =o O(g)" 
by (unfold bigo_def, auto)

lemma bigo_elt_subset2 [intro]: "f : g +o O(h) ==> O(f) <= O(g) + O(h)"
proof -
  assume "f : g +o O(h)"
  also have "... <= O(g) + O(h)"
    by (auto del: subsetI)
  also have "... = O(%x. abs(g x)) + O(%x. abs(h x))"
    apply (subst bigo_abs3 [symmetric])+
    apply (rule refl)
    done
  also have "... = O((%x. abs(g x)) + (%x. abs(h x)))"
    by (rule bigo_plus_eq [symmetric], auto)
  finally have "f : ...".
  then have "O(f) <= ..."
    by (elim bigo_elt_subset)
  also have "... = O(%x. abs(g x)) + O(%x. abs(h x))"
    by (rule bigo_plus_eq, auto)
  finally show ?thesis
    by (simp add: bigo_abs3 [symmetric])
qed

ML{*ResAtp.problem_name := "BigO__bigo_mult"*}
lemma bigo_mult [intro]: "O(f)*O(g) <= O(f * g)"
  apply (rule subsetI)
  apply (subst bigo_def)
  apply (auto simp del: abs_mult mult_ac
              simp add: bigo_alt_def set_times func_times)
(*sledgehammer*); 
  apply (rule_tac x = "c * ca" in exI)
  apply(rule allI)
  apply(erule_tac x = x in allE)+
  apply(subgoal_tac "c * ca * abs(f x * g x) = 
      (c * abs(f x)) * (ca * abs(g x))")
ML{*ResAtp.problem_name := "BigO__bigo_mult_simpler"*}
prefer 2 
apply (metis  Finite_Set.AC_mult.f.assoc  Finite_Set.AC_mult.f.left_commute  OrderedGroup.abs_of_pos  OrderedGroup.mult_left_commute  Ring_and_Field.abs_mult  Ring_and_Field.mult_pos_pos)
  apply(erule ssubst) 
  apply (subst abs_mult)
(*not qute BigO__bigo_mult_simpler_1 (a hard problem!) as abs_mult has
  just been done*)
proof (neg_clausify)
fix a c b ca x
assume 0: "(0\<Colon>'b\<Colon>ordered_idom) < (c\<Colon>'b\<Colon>ordered_idom)"
assume 1: "\<bar>(a\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x\<Colon>'a)\<bar>
\<le> (c\<Colon>'b\<Colon>ordered_idom) * \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>"
assume 2: "\<bar>(b\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x\<Colon>'a)\<bar>
\<le> (ca\<Colon>'b\<Colon>ordered_idom) * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>"
assume 3: "\<not> \<bar>(a\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x\<Colon>'a)\<bar> *
  \<bar>(b\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>
  \<le> (c\<Colon>'b\<Colon>ordered_idom) * \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar> *
    ((ca\<Colon>'b\<Colon>ordered_idom) * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>)"
have 4: "\<bar>c\<Colon>'b\<Colon>ordered_idom\<bar> = c"
  by (metis OrderedGroup.abs_of_pos 0)
have 5: "\<And>X1\<Colon>'b\<Colon>ordered_idom. (c\<Colon>'b\<Colon>ordered_idom) * \<bar>X1\<bar> = \<bar>c * X1\<bar>"
  by (metis Ring_and_Field.abs_mult 4)
have 6: "(0\<Colon>'b\<Colon>ordered_idom) = (1\<Colon>'b\<Colon>ordered_idom) \<or>
(0\<Colon>'b\<Colon>ordered_idom) < (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis OrderedGroup.abs_not_less_zero Ring_and_Field.abs_one Ring_and_Field.linorder_neqE_ordered_idom)
have 7: "(0\<Colon>'b\<Colon>ordered_idom) < (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis 6 Ring_and_Field.one_neq_zero)
have 8: "\<bar>1\<Colon>'b\<Colon>ordered_idom\<bar> = (1\<Colon>'b\<Colon>ordered_idom)"
  by (metis OrderedGroup.abs_of_pos 7)
have 9: "\<And>X1\<Colon>'b\<Colon>ordered_idom. (0\<Colon>'b\<Colon>ordered_idom) \<le> (c\<Colon>'b\<Colon>ordered_idom) * \<bar>X1\<bar>"
  by (metis OrderedGroup.abs_ge_zero 5)
have 10: "\<And>X1\<Colon>'b\<Colon>ordered_idom. X1 * (1\<Colon>'b\<Colon>ordered_idom) = X1"
  by (metis Ring_and_Field.mult_cancel_right2 Finite_Set.AC_mult.f.commute)
have 11: "\<And>X1\<Colon>'b\<Colon>ordered_idom. \<bar>\<bar>X1\<bar>\<bar> = \<bar>X1\<bar> * \<bar>1\<Colon>'b\<Colon>ordered_idom\<bar>"
  by (metis Ring_and_Field.abs_mult OrderedGroup.abs_idempotent 10)
have 12: "\<And>X1\<Colon>'b\<Colon>ordered_idom. \<bar>\<bar>X1\<bar>\<bar> = \<bar>X1\<bar>"
  by (metis 11 8 10)
have 13: "\<And>X1\<Colon>'b\<Colon>ordered_idom. (0\<Colon>'b\<Colon>ordered_idom) \<le> \<bar>X1\<bar>"
  by (metis OrderedGroup.abs_ge_zero 12)
have 14: "\<not> (0\<Colon>'b\<Colon>ordered_idom)
  \<le> (c\<Colon>'b\<Colon>ordered_idom) * \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x\<Colon>'a)\<bar> \<or>
\<not> (0\<Colon>'b\<Colon>ordered_idom) \<le> \<bar>(b\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar> \<or>
\<not> \<bar>b x\<bar> \<le> (ca\<Colon>'b\<Colon>ordered_idom) * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar> \<or>
\<not> \<bar>(a\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar> \<le> c * \<bar>f x\<bar>"
  by (metis 3 Ring_and_Field.mult_mono)
have 15: "\<not> (0\<Colon>'b\<Colon>ordered_idom) \<le> \<bar>(b\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x\<Colon>'a)\<bar> \<or>
\<not> \<bar>b x\<bar> \<le> (ca\<Colon>'b\<Colon>ordered_idom) * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar> \<or>
\<not> \<bar>(a\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>
  \<le> (c\<Colon>'b\<Colon>ordered_idom) * \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>"
  by (metis 14 9)
have 16: "\<not> \<bar>(b\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x\<Colon>'a)\<bar>
  \<le> (ca\<Colon>'b\<Colon>ordered_idom) * \<bar>(g\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar> \<or>
\<not> \<bar>(a\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>
  \<le> (c\<Colon>'b\<Colon>ordered_idom) * \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>"
  by (metis 15 13)
have 17: "\<not> \<bar>(a\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) (x\<Colon>'a)\<bar>
  \<le> (c\<Colon>'b\<Colon>ordered_idom) * \<bar>(f\<Colon>'a \<Rightarrow> 'b\<Colon>ordered_idom) x\<bar>"
  by (metis 16 2)
show 18: "False"
  by (metis 17 1)
qed


ML{*ResAtp.problem_name := "BigO__bigo_mult2"*}
lemma bigo_mult2 [intro]: "f *o O(g) <= O(f * g)"
  apply (auto simp add: bigo_def elt_set_times_def func_times abs_mult)
(*sledgehammer*); 
  apply (rule_tac x = c in exI)
  apply clarify
  apply (drule_tac x = x in spec)
ML{*ResAtp.problem_name := "BigO__bigo_mult2_simpler"*}
(*sledgehammer*); 
  apply (subgoal_tac "abs(f x) * abs(b x) <= abs(f x) * (c * abs(g x))")
  apply (simp add: mult_ac)
  apply (rule mult_left_mono, assumption)
  apply (rule abs_ge_zero)
done

ML{*ResAtp.problem_name:="BigO__bigo_mult3"*}
lemma bigo_mult3: "f : O(h) ==> g : O(j) ==> f * g : O(h * j)"
by (metis bigo_mult set_times_intro subset_iff)

ML{*ResAtp.problem_name:="BigO__bigo_mult4"*}
lemma bigo_mult4 [intro]:"f : k +o O(h) ==> g * f : (g * k) +o O(g * h)"
by (metis bigo_mult2 set_plus_mono_b set_times_intro2 set_times_plus_distrib)


lemma bigo_mult5: "ALL x. f x ~= 0 ==>
    O(f * g) <= (f::'a => ('b::ordered_field)) *o O(g)"
proof -
  assume "ALL x. f x ~= 0"
  show "O(f * g) <= f *o O(g)"
  proof
    fix h
    assume "h : O(f * g)"
    then have "(%x. 1 / (f x)) * h : (%x. 1 / f x) *o O(f * g)"
      by auto
    also have "... <= O((%x. 1 / f x) * (f * g))"
      by (rule bigo_mult2)
    also have "(%x. 1 / f x) * (f * g) = g"
      apply (simp add: func_times) 
      apply (rule ext)
      apply (simp add: prems nonzero_divide_eq_eq mult_ac)
      done
    finally have "(%x. (1::'b) / f x) * h : O(g)".
    then have "f * ((%x. (1::'b) / f x) * h) : f *o O(g)"
      by auto
    also have "f * ((%x. (1::'b) / f x) * h) = h"
      apply (simp add: func_times) 
      apply (rule ext)
      apply (simp add: prems nonzero_divide_eq_eq mult_ac)
      done
    finally show "h : f *o O(g)".
  qed
qed

ML{*ResAtp.problem_name := "BigO__bigo_mult6"*}
lemma bigo_mult6: "ALL x. f x ~= 0 ==>
    O(f * g) = (f::'a => ('b::ordered_field)) *o O(g)"
by (metis bigo_mult2 bigo_mult5 order_antisym)

(*proof requires relaxing relevance: 2007-01-25*)
ML{*ResAtp.problem_name := "BigO__bigo_mult7"*}
  declare bigo_mult6 [simp]
lemma bigo_mult7: "ALL x. f x ~= 0 ==>
    O(f * g) <= O(f::'a => ('b::ordered_field)) * O(g)"
(*sledgehammer*)
  apply (subst bigo_mult6)
  apply assumption
  apply (rule set_times_mono3) 
  apply (rule bigo_refl)
done
  declare bigo_mult6 [simp del]

ML{*ResAtp.problem_name := "BigO__bigo_mult8"*}
  declare bigo_mult7[intro!]
lemma bigo_mult8: "ALL x. f x ~= 0 ==>
    O(f * g) = O(f::'a => ('b::ordered_field)) * O(g)"
by (metis bigo_mult bigo_mult7 order_antisym_conv)

lemma bigo_minus [intro]: "f : O(g) ==> - f : O(g)"
  by (auto simp add: bigo_def func_minus)

lemma bigo_minus2: "f : g +o O(h) ==> -f : -g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (drule set_plus_imp_minus)
  apply (drule bigo_minus)
  apply (simp add: diff_minus)
done

lemma bigo_minus3: "O(-f) = O(f)"
  by (auto simp add: bigo_def func_minus abs_minus_cancel)

lemma bigo_plus_absorb_lemma1: "f : O(g) ==> f +o O(g) <= O(g)"
proof -
  assume a: "f : O(g)"
  show "f +o O(g) <= O(g)"
  proof -
    have "f : O(f)" by auto
    then have "f +o O(g) <= O(f) + O(g)"
      by (auto del: subsetI)
    also have "... <= O(g) + O(g)"
    proof -
      from a have "O(f) <= O(g)" by (auto del: subsetI)
      thus ?thesis by (auto del: subsetI)
    qed
    also have "... <= O(g)" by (simp add: bigo_plus_idemp)
    finally show ?thesis .
  qed
qed

lemma bigo_plus_absorb_lemma2: "f : O(g) ==> O(g) <= f +o O(g)"
proof -
  assume a: "f : O(g)"
  show "O(g) <= f +o O(g)"
  proof -
    from a have "-f : O(g)" by auto
    then have "-f +o O(g) <= O(g)" by (elim bigo_plus_absorb_lemma1)
    then have "f +o (-f +o O(g)) <= f +o O(g)" by auto
    also have "f +o (-f +o O(g)) = O(g)"
      by (simp add: set_plus_rearranges)
    finally show ?thesis .
  qed
qed

ML{*ResAtp.problem_name:="BigO__bigo_plus_absorb"*}
lemma bigo_plus_absorb [simp]: "f : O(g) ==> f +o O(g) = O(g)"
by (metis bigo_plus_absorb_lemma1 bigo_plus_absorb_lemma2 order_eq_iff);

lemma bigo_plus_absorb2 [intro]: "f : O(g) ==> A <= O(g) ==> f +o A <= O(g)"
  apply (subgoal_tac "f +o A <= f +o O(g)")
  apply force+
done

lemma bigo_add_commute_imp: "f : g +o O(h) ==> g : f +o O(h)"
  apply (subst set_minus_plus [symmetric])
  apply (subgoal_tac "g - f = - (f - g)")
  apply (erule ssubst)
  apply (rule bigo_minus)
  apply (subst set_minus_plus)
  apply assumption
  apply  (simp add: diff_minus add_ac)
done

lemma bigo_add_commute: "(f : g +o O(h)) = (g : f +o O(h))"
  apply (rule iffI)
  apply (erule bigo_add_commute_imp)+
done

lemma bigo_const1: "(%x. c) : O(%x. 1)"
by (auto simp add: bigo_def mult_ac)

declare bigo_const1 [skolem]

ML{*ResAtp.problem_name:="BigO__bigo_const2"*}
lemma (*bigo_const2 [intro]:*) "O(%x. c) <= O(%x. 1)"
by (metis bigo_const1 bigo_elt_subset);

lemma bigo_const2 [intro]: "O(%x. c) <= O(%x. 1)"; 
(*??FAILS because the two occurrences of COMBK have different polymorphic types
proof (neg_clausify)
assume 0: "\<not> O(COMBK (c\<Colon>'b\<Colon>ordered_idom)) \<subseteq> O(COMBK (1\<Colon>'b\<Colon>ordered_idom))"
have 1: "COMBK (c\<Colon>'b\<Colon>ordered_idom) \<notin> O(COMBK (1\<Colon>'b\<Colon>ordered_idom))"
apply (rule notI) 
apply (rule 0 [THEN notE]) 
apply (rule bigo_elt_subset) 
apply assumption; 
sorry
  by (metis 0 bigo_elt_subset)  loops??
show "False"
  by (metis 1 bigo_const1)
qed
*)
  apply (rule bigo_elt_subset)
  apply (rule bigo_const1)
done

declare bigo_const2 [skolem]

ML{*ResAtp.problem_name := "BigO__bigo_const3"*}
lemma bigo_const3: "(c::'a::ordered_field) ~= 0 ==> (%x. 1) : O(%x. c)"
apply (simp add: bigo_def)
proof (neg_clausify)
assume 0: "(c\<Colon>'a\<Colon>ordered_field) \<noteq> (0\<Colon>'a\<Colon>ordered_field)"
assume 1: "\<And>mes_md\<Colon>'a\<Colon>ordered_field. \<not> (1\<Colon>'a\<Colon>ordered_field) \<le> mes_md * \<bar>c\<Colon>'a\<Colon>ordered_field\<bar>"
have 2: "(0\<Colon>'a\<Colon>ordered_field) = \<bar>c\<Colon>'a\<Colon>ordered_field\<bar> \<or>
\<not> (1\<Colon>'a\<Colon>ordered_field) \<le> (1\<Colon>'a\<Colon>ordered_field)"
  by (metis 1 field_inverse)
have 3: "\<bar>c\<Colon>'a\<Colon>ordered_field\<bar> = (0\<Colon>'a\<Colon>ordered_field)"
  by (metis 2 order_refl)
have 4: "(0\<Colon>'a\<Colon>ordered_field) = (c\<Colon>'a\<Colon>ordered_field)"
  by (metis OrderedGroup.abs_eq_0 3)
show 5: "False"
  by (metis 4 0)
qed

lemma bigo_const4: "(c::'a::ordered_field) ~= 0 ==> O(%x. 1) <= O(%x. c)"
by (rule bigo_elt_subset, rule bigo_const3, assumption)

lemma bigo_const [simp]: "(c::'a::ordered_field) ~= 0 ==> 
    O(%x. c) = O(%x. 1)"
by (rule equalityI, rule bigo_const2, rule bigo_const4, assumption)

ML{*ResAtp.problem_name := "BigO__bigo_const_mult1"*}
lemma bigo_const_mult1: "(%x. c * f x) : O(f)"
  apply (simp add: bigo_def abs_mult) 
proof (neg_clausify)
fix x
assume 0: "\<And>mes_vAL\<Colon>'b.
   \<not> \<bar>c\<Colon>'b\<bar> *
     \<bar>(f\<Colon>'a \<Rightarrow> 'b) ((x\<Colon>'b \<Rightarrow> 'a) mes_vAL)\<bar>
     \<le> mes_vAL * \<bar>f (x mes_vAL)\<bar>"
have 1: "\<And>Y\<Colon>'b. Y \<le> Y"
  by (metis order_refl)
show 2: "False"
  by (metis 0 1)
qed

lemma bigo_const_mult2: "O(%x. c * f x) <= O(f)"
by (rule bigo_elt_subset, rule bigo_const_mult1)

ML{*ResAtp.problem_name := "BigO__bigo_const_mult3"*}
lemma bigo_const_mult3: "(c::'a::ordered_field) ~= 0 ==> f : O(%x. c * f x)"
  apply (simp add: bigo_def)
(*sledgehammer*); 
  apply (rule_tac x = "abs(inverse c)" in exI)
  apply (simp only: abs_mult [symmetric] mult_assoc [symmetric])
apply (subst left_inverse) 
apply (auto ); 
done

lemma bigo_const_mult4: "(c::'a::ordered_field) ~= 0 ==> 
    O(f) <= O(%x. c * f x)"
by (rule bigo_elt_subset, rule bigo_const_mult3, assumption)

lemma bigo_const_mult [simp]: "(c::'a::ordered_field) ~= 0 ==> 
    O(%x. c * f x) = O(f)"
by (rule equalityI, rule bigo_const_mult2, erule bigo_const_mult4)

ML{*ResAtp.problem_name := "BigO__bigo_const_mult5"*}
lemma bigo_const_mult5 [simp]: "(c::'a::ordered_field) ~= 0 ==> 
    (%x. c) *o O(f) = O(f)"
  apply (auto del: subsetI)
  apply (rule order_trans)
  apply (rule bigo_mult2)
  apply (simp add: func_times)
  apply (auto intro!: subsetI simp add: bigo_def elt_set_times_def func_times)
  apply (rule_tac x = "%y. inverse c * x y" in exI)
apply (rename_tac g d) 
apply safe;
apply (rule_tac [2] ext) 
(*sledgehammer*); 
  apply (simp_all del: mult_assoc add: mult_assoc [symmetric] abs_mult)
  apply (rule_tac x = "abs (inverse c) * d" in exI)
  apply (rule allI)
  apply (subst mult_assoc)
  apply (rule mult_left_mono)
  apply (erule spec)
apply (simp add: ); 
done


ML{*ResAtp.problem_name := "BigO__bigo_const_mult6"*}
lemma bigo_const_mult6 [intro]: "(%x. c) *o O(f) <= O(f)"
  apply (auto intro!: subsetI
    simp add: bigo_def elt_set_times_def func_times
    simp del: abs_mult mult_ac)
(*sledgehammer*); 
  apply (rule_tac x = "ca * (abs c)" in exI)
  apply (rule allI)
  apply (subgoal_tac "ca * abs(c) * abs(f x) = abs(c) * (ca * abs(f x))")
  apply (erule ssubst)
  apply (subst abs_mult)
  apply (rule mult_left_mono)
  apply (erule spec)
  apply simp
  apply(simp add: mult_ac)
done

lemma bigo_const_mult7 [intro]: "f =o O(g) ==> (%x. c * f x) =o O(g)"
proof -
  assume "f =o O(g)"
  then have "(%x. c) * f =o (%x. c) *o O(g)"
    by auto
  also have "(%x. c) * f = (%x. c * f x)"
    by (simp add: func_times)
  also have "(%x. c) *o O(g) <= O(g)"
    by (auto del: subsetI)
  finally show ?thesis .
qed

lemma bigo_compose1: "f =o O(g) ==> (%x. f(k x)) =o O(%x. g(k x))"
by (unfold bigo_def, auto)

lemma bigo_compose2: "f =o g +o O(h) ==> (%x. f(k x)) =o (%x. g(k x)) +o 
    O(%x. h(k x))"
  apply (simp only: set_minus_plus [symmetric] diff_minus func_minus
      func_plus)
  apply (erule bigo_compose1)
done

subsection {* Setsum *}

lemma bigo_setsum_main: "ALL x. ALL y : A x. 0 <= h x y ==> 
    EX c. ALL x. ALL y : A x. abs(f x y) <= c * (h x y) ==>
      (%x. SUM y : A x. f x y) =o O(%x. SUM y : A x. h x y)"  
  apply (auto simp add: bigo_def)
  apply (rule_tac x = "abs c" in exI)
  apply (subst abs_of_nonneg) back back
  apply (rule setsum_nonneg)
  apply force
  apply (subst setsum_right_distrib)
  apply (rule allI)
  apply (rule order_trans)
  apply (rule setsum_abs)
  apply (rule setsum_mono)
apply (blast intro: order_trans mult_right_mono abs_ge_self) 
done

ML{*ResAtp.problem_name := "BigO__bigo_setsum1"*}
lemma bigo_setsum1: "ALL x y. 0 <= h x y ==> 
    EX c. ALL x y. abs(f x y) <= c * (h x y) ==>
      (%x. SUM y : A x. f x y) =o O(%x. SUM y : A x. h x y)"
  apply (rule bigo_setsum_main)
(*sledgehammer*); 
  apply force
  apply clarsimp
  apply (rule_tac x = c in exI)
  apply force
done

lemma bigo_setsum2: "ALL y. 0 <= h y ==> 
    EX c. ALL y. abs(f y) <= c * (h y) ==>
      (%x. SUM y : A x. f y) =o O(%x. SUM y : A x. h y)"
by (rule bigo_setsum1, auto)  

ML{*ResAtp.problem_name := "BigO__bigo_setsum3"*}
lemma bigo_setsum3: "f =o O(h) ==>
    (%x. SUM y : A x. (l x y) * f(k x y)) =o
      O(%x. SUM y : A x. abs(l x y * h(k x y)))"
  apply (rule bigo_setsum1)
  apply (rule allI)+
  apply (rule abs_ge_zero)
  apply (unfold bigo_def)
  apply (auto simp add: abs_mult);
(*sledgehammer*); 
  apply (rule_tac x = c in exI)
  apply (rule allI)+
  apply (subst mult_left_commute)
  apply (rule mult_left_mono)
  apply (erule spec)
  apply (rule abs_ge_zero)
done

lemma bigo_setsum4: "f =o g +o O(h) ==>
    (%x. SUM y : A x. l x y * f(k x y)) =o
      (%x. SUM y : A x. l x y * g(k x y)) +o
        O(%x. SUM y : A x. abs(l x y * h(k x y)))"
  apply (rule set_minus_imp_plus)
  apply (subst func_diff)
  apply (subst setsum_subtractf [symmetric])
  apply (subst right_diff_distrib [symmetric])
  apply (rule bigo_setsum3)
  apply (subst func_diff [symmetric])
  apply (erule set_plus_imp_minus)
done

ML{*ResAtp.problem_name := "BigO__bigo_setsum5"*}
lemma bigo_setsum5: "f =o O(h) ==> ALL x y. 0 <= l x y ==> 
    ALL x. 0 <= h x ==>
      (%x. SUM y : A x. (l x y) * f(k x y)) =o
        O(%x. SUM y : A x. (l x y) * h(k x y))" 
  apply (subgoal_tac "(%x. SUM y : A x. (l x y) * h(k x y)) = 
      (%x. SUM y : A x. abs((l x y) * h(k x y)))")
  apply (erule ssubst)
  apply (erule bigo_setsum3)
  apply (rule ext)
  apply (rule setsum_cong2)
  apply (thin_tac "f \<in> O(h)") 
(*sledgehammer*); 
  apply (subst abs_of_nonneg)
  apply (rule mult_nonneg_nonneg)
  apply auto
done

lemma bigo_setsum6: "f =o g +o O(h) ==> ALL x y. 0 <= l x y ==>
    ALL x. 0 <= h x ==>
      (%x. SUM y : A x. (l x y) * f(k x y)) =o
        (%x. SUM y : A x. (l x y) * g(k x y)) +o
          O(%x. SUM y : A x. (l x y) * h(k x y))" 
  apply (rule set_minus_imp_plus)
  apply (subst func_diff)
  apply (subst setsum_subtractf [symmetric])
  apply (subst right_diff_distrib [symmetric])
  apply (rule bigo_setsum5)
  apply (subst func_diff [symmetric])
  apply (drule set_plus_imp_minus)
  apply auto
done

subsection {* Misc useful stuff *}

lemma bigo_useful_intro: "A <= O(f) ==> B <= O(f) ==>
  A + B <= O(f)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_mono2)
  apply assumption+
done

lemma bigo_useful_add: "f =o O(h) ==> g =o O(h) ==> f + g =o O(h)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_intro)
  apply assumption+
done
  
lemma bigo_useful_const_mult: "(c::'a::ordered_field) ~= 0 ==> 
    (%x. c) * f =o O(h) ==> f =o O(h)"
  apply (rule subsetD)
  apply (subgoal_tac "(%x. 1 / c) *o O(h) <= O(h)")
  apply assumption
  apply (rule bigo_const_mult6)
  apply (subgoal_tac "f = (%x. 1 / c) * ((%x. c) * f)")
  apply (erule ssubst)
  apply (erule set_times_intro2)
  apply (simp add: func_times) 
done

ML{*ResAtp.problem_name := "BigO__bigo_fix"*}
lemma bigo_fix: "(%x. f ((x::nat) + 1)) =o O(%x. h(x + 1)) ==> f 0 = 0 ==>
    f =o O(h)"
  apply (simp add: bigo_alt_def)
(*sledgehammer*); 
  apply clarify
  apply (rule_tac x = c in exI)
  apply safe
  apply (case_tac "x = 0")
prefer 2
  apply (subgoal_tac "x = Suc (x - 1)")
  apply (erule ssubst) back
  apply (erule spec)
  apply (rule Suc_pred') 
  apply simp
apply (metis OrderedGroup.abs_ge_zero  OrderedGroup.abs_zero  order_less_le  Ring_and_Field.split_mult_pos_le) 
  done


lemma bigo_fix2: 
    "(%x. f ((x::nat) + 1)) =o (%x. g(x + 1)) +o O(%x. h(x + 1)) ==> 
       f 0 = g 0 ==> f =o g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_fix)
  apply (subst func_diff)
  apply (subst func_diff [symmetric])
  apply (rule set_plus_imp_minus)
  apply simp
  apply (simp add: func_diff)
done

subsection {* Less than or equal to *}

constdefs 
  lesso :: "('a => 'b::ordered_idom) => ('a => 'b) => ('a => 'b)"
      (infixl "<o" 70)
  "f <o g == (%x. max (f x - g x) 0)"

lemma bigo_lesseq1: "f =o O(h) ==> ALL x. abs (g x) <= abs (f x) ==>
    g =o O(h)"
  apply (unfold bigo_def)
  apply clarsimp
apply (blast intro: order_trans) 
done

lemma bigo_lesseq2: "f =o O(h) ==> ALL x. abs (g x) <= f x ==>
      g =o O(h)"
  apply (erule bigo_lesseq1)
apply (blast intro: abs_ge_self order_trans) 
done

lemma bigo_lesseq3: "f =o O(h) ==> ALL x. 0 <= g x ==> ALL x. g x <= f x ==>
      g =o O(h)"
  apply (erule bigo_lesseq2)
  apply (rule allI)
  apply (subst abs_of_nonneg)
  apply (erule spec)+
done

lemma bigo_lesseq4: "f =o O(h) ==>
    ALL x. 0 <= g x ==> ALL x. g x <= abs (f x) ==>
      g =o O(h)"
  apply (erule bigo_lesseq1)
  apply (rule allI)
  apply (subst abs_of_nonneg)
  apply (erule spec)+
done

ML{*ResAtp.problem_name:="BigO__bigo_lesso1"*}
lemma bigo_lesso1: "ALL x. f x <= g x ==> f <o g =o O(h)"
  apply (unfold lesso_def)
  apply (subgoal_tac "(%x. max (f x - g x) 0) = 0")
(*
?? abstractions don't work: abstraction function gets the wrong type?
proof (neg_clausify)
assume 0: "llabs_subgoal_1 f g = 0"
assume 1: "llabs_subgoal_1 f g \<notin> O(h)"
show "False"
  by (metis 1 0 bigo_zero)
*)
  apply (erule ssubst)
  apply (rule bigo_zero)
  apply (unfold func_zero)
  apply (rule ext)
  apply (simp split: split_max)
done


ML{*ResAtp.problem_name := "BigO__bigo_lesso2"*}
lemma bigo_lesso2: "f =o g +o O(h) ==>
    ALL x. 0 <= k x ==> ALL x. k x <= f x ==>
      k <o g =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst func_diff)
apply (erule thin_rl)
(*sledgehammer*);  
  apply (case_tac "0 <= k x - g x")
  apply (simp del: compare_rls diff_minus);
  apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
ML{*ResAtp.problem_name := "BigO__bigo_lesso2_simpler"*}
(*sledgehammer*);  
  apply (simp add: compare_rls del: diff_minus)
  apply (subst diff_minus)+
  apply (rule add_right_mono)
  apply (erule spec)
  apply (rule order_trans) 
  prefer 2
  apply (rule abs_ge_zero)
(*
  apply (simp only: compare_rls min_max.below_sup.above_sup_conv 
             linorder_not_le order_less_imp_le)
*)
  apply (simp add: compare_rls del: diff_minus)
done



ML{*ResAtp.problem_name := "BigO__bigo_lesso3"*}
lemma bigo_lesso3: "f =o g +o O(h) ==>
    ALL x. 0 <= k x ==> ALL x. g x <= k x ==>
      f <o k =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst func_diff)
apply (erule thin_rl) 
(*sledgehammer*); 
  apply (case_tac "0 <= f x - k x")
  apply (simp del: compare_rls diff_minus);
  apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
ML{*ResAtp.problem_name := "BigO__bigo_lesso3_simpler"*}
(*sledgehammer*);  
  apply (simp del: diff_minus)
  apply (subst diff_minus)+
  apply (rule add_left_mono)
  apply (rule le_imp_neg_le)
  apply (erule spec)
  apply (rule order_trans) 
  prefer 2
  apply (rule abs_ge_zero)
  apply (simp del: diff_minus)
done

lemma bigo_lesso4: "f <o g =o O(k::'a=>'b::ordered_field) ==>
    g =o h +o O(k) ==> f <o h =o O(k)"
  apply (unfold lesso_def)
  apply (drule set_plus_imp_minus)
  apply (drule bigo_abs5) back
  apply (simp add: func_diff)
  apply (drule bigo_useful_add)
  apply assumption
  apply (erule bigo_lesseq2) back
  apply (rule allI)
  apply (auto simp add: func_plus func_diff compare_rls 
    split: split_max abs_split)
done

ML{*ResAtp.problem_name := "BigO__bigo_lesso5"*}
lemma bigo_lesso5: "f <o g =o O(h) ==>
    EX C. ALL x. f x <= g x + C * abs(h x)"
  apply (simp only: lesso_def bigo_alt_def)
  apply clarsimp
(*sledgehammer*);  
apply (auto simp add: compare_rls add_ac) 
done

end
