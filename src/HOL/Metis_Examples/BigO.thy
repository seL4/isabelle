(*  Title:      HOL/Metis_Examples/BigO.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Testing the metis method.
*)

header {* Big O notation *}

theory BigO
imports "~~/src/HOL/Decision_Procs/Dense_Linear_Order" Main SetsAndFunctions 
begin

subsection {* Definitions *}

definition bigo :: "('a => 'b::ordered_idom) => ('a => 'b) set"    ("(1O'(_'))") where
  "O(f::('a => 'b)) ==   {h. EX c. ALL x. abs (h x) <= c * abs (f x)}"

declare [[ atp_problem_prefix = "BigO__bigo_pos_const" ]]
lemma bigo_pos_const: "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
  apply (metis abs_ge_minus_self abs_ge_zero abs_minus_cancel abs_of_nonneg equation_minus_iff Orderings.xt1(6) abs_mult)
  done

(*** Now various verions with an increasing modulus ***)

declare [[sledgehammer_modulus = 1]]

lemma (*bigo_pos_const:*) "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
proof (neg_clausify)
fix c x
have 0: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom. \<bar>X1 * X2\<bar> = \<bar>X2 * X1\<bar>"
  by (metis abs_mult mult_commute)
have 1: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom.
   X1 \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or> \<bar>X2\<bar> * X1 = \<bar>X2 * X1\<bar>"
  by (metis abs_mult_pos linorder_linear)
have 2: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom.
   \<not> (0\<Colon>'a\<Colon>ordered_idom) < X1 * X2 \<or>
   \<not> (0\<Colon>'a\<Colon>ordered_idom) \<le> X2 \<or> \<not> X1 \<le> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis linorder_not_less mult_nonneg_nonpos2)
assume 3: "\<And>x\<Colon>'b\<Colon>type.
   \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>
   \<le> (c\<Colon>'a\<Colon>ordered_idom) * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
assume 4: "\<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>
  \<le> \<bar>c\<Colon>'a\<Colon>ordered_idom\<bar> * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
have 5: "\<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>
  \<le> \<bar>(c\<Colon>'a\<Colon>ordered_idom) * (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
  by (metis 4 abs_mult)
have 6: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom.
   \<not> X1 \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or> X1 \<le> \<bar>X2\<bar>"
  by (metis abs_ge_zero xt1(6))
have 7: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom.
   X1 \<le> \<bar>X2\<bar> \<or> (0\<Colon>'a\<Colon>ordered_idom) < X1"
  by (metis not_leE 6)
have 8: "(0\<Colon>'a\<Colon>ordered_idom) < \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>"
  by (metis 5 7)
have 9: "\<And>X1\<Colon>'a\<Colon>ordered_idom.
   \<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar> \<le> X1 \<or>
   (0\<Colon>'a\<Colon>ordered_idom) < X1"
  by (metis 8 order_less_le_trans)
have 10: "(0\<Colon>'a\<Colon>ordered_idom)
< (c\<Colon>'a\<Colon>ordered_idom) * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>"
  by (metis 3 9)
have 11: "\<not> (c\<Colon>'a\<Colon>ordered_idom) \<le> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_ge_zero 2 10)
have 12: "\<And>X1\<Colon>'a\<Colon>ordered_idom. (c\<Colon>'a\<Colon>ordered_idom) * \<bar>X1\<bar> = \<bar>X1 * c\<bar>"
  by (metis mult_commute 1 11)
have 13: "\<And>X1\<Colon>'b\<Colon>type.
   - (h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1
   \<le> (c\<Colon>'a\<Colon>ordered_idom) * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1\<bar>"
  by (metis 3 abs_le_D2)
have 14: "\<And>X1\<Colon>'b\<Colon>type.
   - (h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1
   \<le> \<bar>(c\<Colon>'a\<Colon>ordered_idom) * (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1\<bar>"
  by (metis 0 12 13)
have 15: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom. \<bar>X1 * \<bar>X2\<bar>\<bar> = \<bar>X1 * X2\<bar>"
  by (metis abs_mult abs_mult_pos abs_ge_zero)
have 16: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom. X1 \<le> \<bar>X2\<bar> \<or> \<not> X1 \<le> X2"
  by (metis xt1(6) abs_ge_self)
have 17: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom. \<not> \<bar>X1\<bar> \<le> X2 \<or> X1 \<le> \<bar>X2\<bar>"
  by (metis 16 abs_le_D1)
have 18: "\<And>X1\<Colon>'b\<Colon>type.
   (h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1
   \<le> \<bar>(c\<Colon>'a\<Colon>ordered_idom) * (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1\<bar>"
  by (metis 17 3 15)
show "False"
  by (metis abs_le_iff 5 18 14)
qed

declare [[sledgehammer_modulus = 2]]

lemma (*bigo_pos_const:*) "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto);
proof (neg_clausify)
fix c x
have 0: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom. \<bar>X1 * X2\<bar> = \<bar>X2 * X1\<bar>"
  by (metis abs_mult mult_commute)
assume 1: "\<And>x\<Colon>'b\<Colon>type.
   \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>
   \<le> (c\<Colon>'a\<Colon>ordered_idom) * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
assume 2: "\<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>
  \<le> \<bar>c\<Colon>'a\<Colon>ordered_idom\<bar> * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
have 3: "\<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>
  \<le> \<bar>(c\<Colon>'a\<Colon>ordered_idom) * (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
  by (metis 2 abs_mult)
have 4: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom.
   \<not> X1 \<le> (0\<Colon>'a\<Colon>ordered_idom) \<or> X1 \<le> \<bar>X2\<bar>"
  by (metis abs_ge_zero xt1(6))
have 5: "(0\<Colon>'a\<Colon>ordered_idom) < \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>"
  by (metis not_leE 4 3)
have 6: "(0\<Colon>'a\<Colon>ordered_idom)
< (c\<Colon>'a\<Colon>ordered_idom) * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>"
  by (metis 1 order_less_le_trans 5)
have 7: "\<And>X1\<Colon>'a\<Colon>ordered_idom. (c\<Colon>'a\<Colon>ordered_idom) * \<bar>X1\<bar> = \<bar>X1 * c\<bar>"
  by (metis abs_ge_zero linorder_not_less mult_nonneg_nonpos2 6 linorder_linear abs_mult_pos mult_commute)
have 8: "\<And>X1\<Colon>'b\<Colon>type.
   - (h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1
   \<le> \<bar>(c\<Colon>'a\<Colon>ordered_idom) * (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1\<bar>"
  by (metis 0 7 abs_le_D2 1)
have 9: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom. \<not> \<bar>X1\<bar> \<le> X2 \<or> X1 \<le> \<bar>X2\<bar>"
  by (metis abs_ge_self xt1(6) abs_le_D1)
show "False"
  by (metis 8 abs_ge_zero abs_mult_pos abs_mult 1 9 3 abs_le_iff)
qed

declare [[sledgehammer_modulus = 3]]

lemma (*bigo_pos_const:*) "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto);
proof (neg_clausify)
fix c x
assume 0: "\<And>x\<Colon>'b\<Colon>type.
   \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>
   \<le> (c\<Colon>'a\<Colon>ordered_idom) * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
assume 1: "\<not> \<bar>(h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) (x\<Colon>'b\<Colon>type)\<bar>
  \<le> \<bar>c\<Colon>'a\<Colon>ordered_idom\<bar> * \<bar>(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) x\<bar>"
have 2: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom.
   X1 \<le> \<bar>X2\<bar> \<or> (0\<Colon>'a\<Colon>ordered_idom) < X1"
  by (metis abs_ge_zero xt1(6) not_leE)
have 3: "\<not> (c\<Colon>'a\<Colon>ordered_idom) \<le> (0\<Colon>'a\<Colon>ordered_idom)"
  by (metis abs_ge_zero mult_nonneg_nonpos2 linorder_not_less order_less_le_trans 1 abs_mult 2 0)
have 4: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2\<Colon>'a\<Colon>ordered_idom. \<bar>X1 * \<bar>X2\<bar>\<bar> = \<bar>X1 * X2\<bar>"
  by (metis abs_ge_zero abs_mult_pos abs_mult)
have 5: "\<And>X1\<Colon>'b\<Colon>type.
   (h\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1
   \<le> \<bar>(c\<Colon>'a\<Colon>ordered_idom) * (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>ordered_idom) X1\<bar>"
  by (metis 4 0 xt1(6) abs_ge_self abs_le_D1)
show "False"
  by (metis abs_mult mult_commute 3 abs_mult_pos linorder_linear 0 abs_le_D2 5 1 abs_le_iff)
qed


declare [[sledgehammer_modulus = 1]]

lemma (*bigo_pos_const:*) "(EX (c::'a::ordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto);
proof (neg_clausify)
fix c x  (*sort/type constraint inserted by hand!*)
have 0: "\<And>(X1\<Colon>'a\<Colon>ordered_idom) X2. \<bar>X1 * \<bar>X2\<bar>\<bar> = \<bar>X1 * X2\<bar>"
  by (metis abs_ge_zero abs_mult_pos abs_mult)
assume 1: "\<And>A. \<bar>h A\<bar> \<le> c * \<bar>f A\<bar>"
have 2: "\<And>X1 X2. \<not> \<bar>X1\<bar> \<le> X2 \<or> (0\<Colon>'a) \<le> X2"
  by (metis abs_ge_zero order_trans)
have 3: "\<And>X1. (0\<Colon>'a) \<le> c * \<bar>f X1\<bar>"
  by (metis 1 2)
have 4: "\<And>X1. c * \<bar>f X1\<bar> = \<bar>c * f X1\<bar>"
  by (metis 0 abs_of_nonneg 3)
have 5: "\<And>X1. - h X1 \<le> c * \<bar>f X1\<bar>"
  by (metis 1 abs_le_D2)
have 6: "\<And>X1. - h X1 \<le> \<bar>c * f X1\<bar>"
  by (metis 4 5)
have 7: "\<And>X1. h X1 \<le> c * \<bar>f X1\<bar>"
  by (metis 1 abs_le_D1)
have 8: "\<And>X1. h X1 \<le> \<bar>c * f X1\<bar>"
  by (metis 4 7)
assume 9: "\<not> \<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>"
have 10: "\<not> \<bar>h x\<bar> \<le> \<bar>c * f x\<bar>"
  by (metis abs_mult 9)
show "False"
  by (metis 6 8 10 abs_leI)
qed


declare [[sledgehammer_sorts = true]]

lemma bigo_alt_def: "O(f) = 
    {h. EX c. (0 < c & (ALL x. abs (h x) <= c * abs (f x)))}"
by (auto simp add: bigo_def bigo_pos_const)

declare [[ atp_problem_prefix = "BigO__bigo_elt_subset" ]]
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


declare [[ atp_problem_prefix = "BigO__bigo_refl" ]]
lemma bigo_refl [intro]: "f : O(f)"
  apply(auto simp add: bigo_def)
proof (neg_clausify)
fix x
assume 0: "\<And>xa. \<not> \<bar>f (x xa)\<bar> \<le> xa * \<bar>f (x xa)\<bar>"
have 1: "\<And>X2. X2 \<le> (1\<Colon>'b) * X2 \<or> \<not> (1\<Colon>'b) \<le> (1\<Colon>'b)"
  by (metis mult_le_cancel_right1 order_eq_iff)
have 2: "\<And>X2. X2 \<le> (1\<Colon>'b) * X2"
  by (metis order_eq_iff 1)
show "False"
  by (metis 0 2)
qed

declare [[ atp_problem_prefix = "BigO__bigo_zero" ]]
lemma bigo_zero: "0 : O(g)"
  apply (auto simp add: bigo_def func_zero)
proof (neg_clausify)
fix x
assume 0: "\<And>xa. \<not> (0\<Colon>'b) \<le> xa * \<bar>g (x xa)\<bar>"
have 1: "\<not> (0\<Colon>'b) \<le> (0\<Colon>'b)"
  by (metis 0 mult_eq_0_iff)
show "False"
  by (metis 1 linorder_neq_iff linorder_antisym_conv1)
qed

lemma bigo_zero2: "O(%x.0) = {%x.0}"
  apply (auto simp add: bigo_def) 
  apply (rule ext)
  apply auto
done

lemma bigo_plus_self_subset [intro]: 
  "O(f) \<oplus> O(f) <= O(f)"
  apply (auto simp add: bigo_alt_def set_plus_def)
  apply (rule_tac x = "c + ca" in exI)
  apply auto
  apply (simp add: ring_distribs func_plus)
  apply (blast intro:order_trans abs_triangle_ineq add_mono elim:) 
done

lemma bigo_plus_idemp [simp]: "O(f) \<oplus> O(f) = O(f)"
  apply (rule equalityI)
  apply (rule bigo_plus_self_subset)
  apply (rule set_zero_plus2) 
  apply (rule bigo_zero)
done

lemma bigo_plus_subset [intro]: "O(f + g) <= O(f) \<oplus> O(g)"
  apply (rule subsetI)
  apply (auto simp add: bigo_def bigo_pos_const func_plus set_plus_def)
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
apply (metis abs_not_less_zero double_less_0_iff less_not_permute linorder_not_less mult_less_0_iff)
  apply (rule ext)
  apply (auto simp add: if_splits linorder_not_le)
done

lemma bigo_plus_subset2 [intro]: "A <= O(f) ==> B <= O(f) ==> A \<oplus> B <= O(f)"
  apply (subgoal_tac "A \<oplus> B <= O(f) \<oplus> O(f)")
  apply (erule order_trans)
  apply simp
  apply (auto del: subsetI simp del: bigo_plus_idemp)
done

declare [[ atp_problem_prefix = "BigO__bigo_plus_eq" ]]
lemma bigo_plus_eq: "ALL x. 0 <= f x ==> ALL x. 0 <= g x ==> 
  O(f + g) = O(f) \<oplus> O(g)"
  apply (rule equalityI)
  apply (rule bigo_plus_subset)
  apply (simp add: bigo_alt_def set_plus_def func_plus)
  apply clarify 
(*sledgehammer*); 
  apply (rule_tac x = "max c ca" in exI)
  apply (rule conjI)
   apply (metis Orderings.less_max_iff_disj)
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
  apply (metis add_nonneg_nonneg)
  apply (rule add_mono)
using [[ atp_problem_prefix = "BigO__bigo_plus_eq_simpler" ]] 
(*Found by SPASS; SLOW*)
apply (metis le_maxI2 linorder_linear linorder_not_le min_max.sup_absorb1 mult_le_cancel_right order_trans)
apply (metis le_maxI2 linorder_not_le mult_le_cancel_right order_trans)
done

declare [[ atp_problem_prefix = "BigO__bigo_bounded_alt" ]]
lemma bigo_bounded_alt: "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> 
    f : O(g)" 
  apply (auto simp add: bigo_def)
(*Version 1: one-shot proof*)
  apply (metis OrderedGroup.abs_le_D1 linorder_class.not_less  order_less_le  Orderings.xt1(12)  Ring_and_Field.abs_mult)
  done

lemma (*bigo_bounded_alt:*) "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> 
    f : O(g)" 
  apply (auto simp add: bigo_def)
(*Version 2: single-step proof*)
proof (neg_clausify)
fix x
assume 0: "\<And>x. f x \<le> c * g x"
assume 1: "\<And>xa. \<not> f (x xa) \<le> xa * \<bar>g (x xa)\<bar>"
have 2: "\<And>X3. c * g X3 = f X3 \<or> \<not> c * g X3 \<le> f X3"
  by (metis 0 order_antisym_conv)
have 3: "\<And>X3. \<not> f (x \<bar>X3\<bar>) \<le> \<bar>X3 * g (x \<bar>X3\<bar>)\<bar>"
  by (metis 1 abs_mult)
have 4: "\<And>X1 X3\<Colon>'b\<Colon>ordered_idom. X3 \<le> X1 \<or> X1 \<le> \<bar>X3\<bar>"
  by (metis linorder_linear abs_le_D1)
have 5: "\<And>X3::'b. \<bar>X3\<bar> * \<bar>X3\<bar> = X3 * X3"
  by (metis abs_mult_self)
have 6: "\<And>X3. \<not> X3 * X3 < (0\<Colon>'b\<Colon>ordered_idom)"
  by (metis not_square_less_zero)
have 7: "\<And>X1 X3::'b. \<bar>X1\<bar> * \<bar>X3\<bar> = \<bar>X3 * X1\<bar>"
  by (metis abs_mult mult_commute)
have 8: "\<And>X3::'b. X3 * X3 = \<bar>X3 * X3\<bar>"
  by (metis abs_mult 5)
have 9: "\<And>X3. X3 * g (x \<bar>X3\<bar>) \<le> f (x \<bar>X3\<bar>)"
  by (metis 3 4)
have 10: "c * g (x \<bar>c\<bar>) = f (x \<bar>c\<bar>)"
  by (metis 2 9)
have 11: "\<And>X3::'b. \<bar>X3\<bar> * \<bar>\<bar>X3\<bar>\<bar> = \<bar>X3\<bar> * \<bar>X3\<bar>"
  by (metis abs_idempotent abs_mult 8)
have 12: "\<And>X3::'b. \<bar>X3 * \<bar>X3\<bar>\<bar> = \<bar>X3\<bar> * \<bar>X3\<bar>"
  by (metis mult_commute 7 11)
have 13: "\<And>X3::'b. \<bar>X3 * \<bar>X3\<bar>\<bar> = X3 * X3"
  by (metis 8 7 12)
have 14: "\<And>X3. X3 \<le> \<bar>X3\<bar> \<or> X3 < (0\<Colon>'b)"
  by (metis abs_ge_self abs_le_D1 abs_if)
have 15: "\<And>X3. X3 \<le> \<bar>X3\<bar> \<or> \<bar>X3\<bar> < (0\<Colon>'b)"
  by (metis abs_ge_self abs_le_D1 abs_if)
have 16: "\<And>X3. X3 * X3 < (0\<Colon>'b) \<or> X3 * \<bar>X3\<bar> \<le> X3 * X3"
  by (metis 15 13)
have 17: "\<And>X3::'b. X3 * \<bar>X3\<bar> \<le> X3 * X3"
  by (metis 16 6)
have 18: "\<And>X3. X3 \<le> \<bar>X3\<bar> \<or> \<not> X3 < (0\<Colon>'b)"
  by (metis mult_le_cancel_left 17)
have 19: "\<And>X3::'b. X3 \<le> \<bar>X3\<bar>"
  by (metis 18 14)
have 20: "\<not> f (x \<bar>c\<bar>) \<le> \<bar>f (x \<bar>c\<bar>)\<bar>"
  by (metis 3 10)
show "False"
  by (metis 20 19)
qed


text{*So here is the easier (and more natural) problem using transitivity*}
declare [[ atp_problem_prefix = "BigO__bigo_bounded_alt_trans" ]]
lemma "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> f : O(g)" 
  apply (auto simp add: bigo_def)
  (*Version 1: one-shot proof*) 
  apply (metis Orderings.leD Orderings.leI abs_ge_self abs_le_D1 abs_mult abs_of_nonneg order_le_less)
  done

text{*So here is the easier (and more natural) problem using transitivity*}
declare [[ atp_problem_prefix = "BigO__bigo_bounded_alt_trans" ]]
lemma "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> f : O(g)" 
  apply (auto simp add: bigo_def)
(*Version 2: single-step proof*)
proof (neg_clausify)
fix x
assume 0: "\<And>A\<Colon>'a\<Colon>type.
   (f\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) A
   \<le> (c\<Colon>'b\<Colon>ordered_idom) * (g\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) A"
assume 1: "\<And>A\<Colon>'b\<Colon>ordered_idom.
   \<not> (f\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a\<Colon>type) A)
     \<le> A * \<bar>(g\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) (x A)\<bar>"
have 2: "\<And>X2\<Colon>'a\<Colon>type.
   \<not> (c\<Colon>'b\<Colon>ordered_idom) * (g\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) X2
     < (f\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) X2"
  by (metis 0 linorder_not_le)
have 3: "\<And>X2\<Colon>'b\<Colon>ordered_idom.
   \<not> (f\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a\<Colon>type) \<bar>X2\<bar>)
     \<le> \<bar>X2 * (g\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>X2\<bar>)\<bar>"
  by (metis abs_mult 1)
have 4: "\<And>X2\<Colon>'b\<Colon>ordered_idom.
   \<bar>X2 * (g\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a\<Colon>type) \<bar>X2\<bar>)\<bar>
   < (f\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>X2\<bar>)"
  by (metis 3 linorder_not_less)
have 5: "\<And>X2\<Colon>'b\<Colon>ordered_idom.
   X2 * (g\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a\<Colon>type) \<bar>X2\<bar>)
   < (f\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) (x \<bar>X2\<bar>)"
  by (metis abs_less_iff 4)
show "False"
  by (metis 2 5)
qed


lemma bigo_bounded: "ALL x. 0 <= f x ==> ALL x. f x <= g x ==> 
    f : O(g)" 
  apply (erule bigo_bounded_alt [of f 1 g])
  apply simp
done

declare [[ atp_problem_prefix = "BigO__bigo_bounded2" ]]
lemma bigo_bounded2: "ALL x. lb x <= f x ==> ALL x. f x <= lb x + g x ==>
    f : lb +o O(g)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_bounded)
  apply (auto simp add: diff_minus fun_Compl_def func_plus)
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
  by (metis 1 diff_minus)
have 4: "\<not> (0\<Colon>'b) + lb x \<le> f x"
  by (metis 3 le_diff_eq)
show "False"
  by (metis 4 2 0)
qed

declare [[ atp_problem_prefix = "BigO__bigo_abs" ]]
lemma bigo_abs: "(%x. abs(f x)) =o O(f)" 
  apply (unfold bigo_def)
  apply auto
proof (neg_clausify)
fix x
assume 0: "\<And>xa. \<not> \<bar>f (x xa)\<bar> \<le> xa * \<bar>f (x xa)\<bar>"
have 1: "\<And>X2. X2 \<le> (1\<Colon>'b) * X2 \<or> \<not> (1\<Colon>'b) \<le> (1\<Colon>'b)"
  by (metis mult_le_cancel_right1 order_eq_iff)
have 2: "\<And>X2. X2 \<le> (1\<Colon>'b) * X2"
  by (metis order_eq_iff 1)
show "False"
  by (metis 0 2)
qed

declare [[ atp_problem_prefix = "BigO__bigo_abs2" ]]
lemma bigo_abs2: "f =o O(%x. abs(f x))"
  apply (unfold bigo_def)
  apply auto
proof (neg_clausify)
fix x
assume 0: "\<And>xa. \<not> \<bar>f (x xa)\<bar> \<le> xa * \<bar>f (x xa)\<bar>"
have 1: "\<And>X2. X2 \<le> (1\<Colon>'b) * X2 \<or> \<not> (1\<Colon>'b) \<le> (1\<Colon>'b)"
  by (metis mult_le_cancel_right1 order_eq_iff)
have 2: "\<And>X2. X2 \<le> (1\<Colon>'b) * X2"
  by (metis order_eq_iff 1)
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
  apply (subst fun_diff_def)
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
    apply (subst fun_diff_def)
    apply (rule bigo_abs)
    done
  also have "... <= O(h)"
    using a by (rule bigo_elt_subset)
  finally show "(%x. abs (f x) - abs (g x)) : O(h)".
qed

lemma bigo_abs5: "f =o O(g) ==> (%x. abs(f x)) =o O(g)" 
by (unfold bigo_def, auto)

lemma bigo_elt_subset2 [intro]: "f : g +o O(h) ==> O(f) <= O(g) \<oplus> O(h)"
proof -
  assume "f : g +o O(h)"
  also have "... <= O(g) \<oplus> O(h)"
    by (auto del: subsetI)
  also have "... = O(%x. abs(g x)) \<oplus> O(%x. abs(h x))"
    apply (subst bigo_abs3 [symmetric])+
    apply (rule refl)
    done
  also have "... = O((%x. abs(g x)) + (%x. abs(h x)))"
    by (rule bigo_plus_eq [symmetric], auto)
  finally have "f : ...".
  then have "O(f) <= ..."
    by (elim bigo_elt_subset)
  also have "... = O(%x. abs(g x)) \<oplus> O(%x. abs(h x))"
    by (rule bigo_plus_eq, auto)
  finally show ?thesis
    by (simp add: bigo_abs3 [symmetric])
qed

declare [[ atp_problem_prefix = "BigO__bigo_mult" ]]
lemma bigo_mult [intro]: "O(f)\<otimes>O(g) <= O(f * g)"
  apply (rule subsetI)
  apply (subst bigo_def)
  apply (auto simp del: abs_mult mult_ac
              simp add: bigo_alt_def set_times_def func_times)
(*sledgehammer*); 
  apply (rule_tac x = "c * ca" in exI)
  apply(rule allI)
  apply(erule_tac x = x in allE)+
  apply(subgoal_tac "c * ca * abs(f x * g x) = 
      (c * abs(f x)) * (ca * abs(g x))")
using [[ atp_problem_prefix = "BigO__bigo_mult_simpler" ]]
prefer 2 
apply (metis mult_assoc mult_left_commute
  OrderedGroup.abs_of_pos OrderedGroup.mult_left_commute
  Ring_and_Field.abs_mult Ring_and_Field.mult_pos_pos)
  apply (erule ssubst) 
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
  by (metis Ring_and_Field.mult_cancel_right2 mult_commute)
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


declare [[ atp_problem_prefix = "BigO__bigo_mult2" ]]
lemma bigo_mult2 [intro]: "f *o O(g) <= O(f * g)"
  apply (auto simp add: bigo_def elt_set_times_def func_times abs_mult)
(*sledgehammer*); 
  apply (rule_tac x = c in exI)
  apply clarify
  apply (drule_tac x = x in spec)
using [[ atp_problem_prefix = "BigO__bigo_mult2_simpler" ]]
(*sledgehammer [no luck]*); 
  apply (subgoal_tac "abs(f x) * abs(b x) <= abs(f x) * (c * abs(g x))")
  apply (simp add: mult_ac)
  apply (rule mult_left_mono, assumption)
  apply (rule abs_ge_zero)
done

declare [[ atp_problem_prefix = "BigO__bigo_mult3" ]]
lemma bigo_mult3: "f : O(h) ==> g : O(j) ==> f * g : O(h * j)"
by (metis bigo_mult set_times_intro subset_iff)

declare [[ atp_problem_prefix = "BigO__bigo_mult4" ]]
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

declare [[ atp_problem_prefix = "BigO__bigo_mult6" ]]
lemma bigo_mult6: "ALL x. f x ~= 0 ==>
    O(f * g) = (f::'a => ('b::ordered_field)) *o O(g)"
by (metis bigo_mult2 bigo_mult5 order_antisym)

(*proof requires relaxing relevance: 2007-01-25*)
declare [[ atp_problem_prefix = "BigO__bigo_mult7" ]]
  declare bigo_mult6 [simp]
lemma bigo_mult7: "ALL x. f x ~= 0 ==>
    O(f * g) <= O(f::'a => ('b::ordered_field)) \<otimes> O(g)"
(*sledgehammer*)
  apply (subst bigo_mult6)
  apply assumption
  apply (rule set_times_mono3) 
  apply (rule bigo_refl)
done
  declare bigo_mult6 [simp del]

declare [[ atp_problem_prefix = "BigO__bigo_mult8" ]]
  declare bigo_mult7[intro!]
lemma bigo_mult8: "ALL x. f x ~= 0 ==>
    O(f * g) = O(f::'a => ('b::ordered_field)) \<otimes> O(g)"
by (metis bigo_mult bigo_mult7 order_antisym_conv)

lemma bigo_minus [intro]: "f : O(g) ==> - f : O(g)"
  by (auto simp add: bigo_def fun_Compl_def)

lemma bigo_minus2: "f : g +o O(h) ==> -f : -g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (drule set_plus_imp_minus)
  apply (drule bigo_minus)
  apply (simp add: diff_minus)
done

lemma bigo_minus3: "O(-f) = O(f)"
  by (auto simp add: bigo_def fun_Compl_def abs_minus_cancel)

lemma bigo_plus_absorb_lemma1: "f : O(g) ==> f +o O(g) <= O(g)"
proof -
  assume a: "f : O(g)"
  show "f +o O(g) <= O(g)"
  proof -
    have "f : O(f)" by auto
    then have "f +o O(g) <= O(f) \<oplus> O(g)"
      by (auto del: subsetI)
    also have "... <= O(g) \<oplus> O(g)"
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

declare [[ atp_problem_prefix = "BigO__bigo_plus_absorb" ]]
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

declare [[ atp_problem_prefix = "BigO__bigo_const2" ]]
lemma (*bigo_const2 [intro]:*) "O(%x. c) <= O(%x. 1)"
by (metis bigo_const1 bigo_elt_subset);

lemma bigo_const2 [intro]: "O(%x. c::'b::ordered_idom) <= O(%x. 1)";
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

declare [[ atp_problem_prefix = "BigO__bigo_const3" ]]
lemma bigo_const3: "(c::'a::ordered_field) ~= 0 ==> (%x. 1) : O(%x. c)"
apply (simp add: bigo_def)
proof (neg_clausify)
assume 0: "(c\<Colon>'a\<Colon>ordered_field) \<noteq> (0\<Colon>'a\<Colon>ordered_field)"
assume 1: "\<And>A\<Colon>'a\<Colon>ordered_field. \<not> (1\<Colon>'a\<Colon>ordered_field) \<le> A * \<bar>c\<Colon>'a\<Colon>ordered_field\<bar>"
have 2: "(0\<Colon>'a\<Colon>ordered_field) = \<bar>c\<Colon>'a\<Colon>ordered_field\<bar> \<or>
\<not> (1\<Colon>'a\<Colon>ordered_field) \<le> (1\<Colon>'a\<Colon>ordered_field)"
  by (metis 1 field_inverse)
have 3: "\<bar>c\<Colon>'a\<Colon>ordered_field\<bar> = (0\<Colon>'a\<Colon>ordered_field)"
  by (metis linorder_neq_iff linorder_antisym_conv1 2)
have 4: "(0\<Colon>'a\<Colon>ordered_field) = (c\<Colon>'a\<Colon>ordered_field)"
  by (metis 3 abs_eq_0)
show "False"
  by (metis 0 4)
qed

lemma bigo_const4: "(c::'a::ordered_field) ~= 0 ==> O(%x. 1) <= O(%x. c)"
by (rule bigo_elt_subset, rule bigo_const3, assumption)

lemma bigo_const [simp]: "(c::'a::ordered_field) ~= 0 ==> 
    O(%x. c) = O(%x. 1)"
by (rule equalityI, rule bigo_const2, rule bigo_const4, assumption)

declare [[ atp_problem_prefix = "BigO__bigo_const_mult1" ]]
lemma bigo_const_mult1: "(%x. c * f x) : O(f)"
  apply (simp add: bigo_def abs_mult)
proof (neg_clausify)
fix x
assume 0: "\<And>xa\<Colon>'b\<Colon>ordered_idom.
   \<not> \<bar>c\<Colon>'b\<Colon>ordered_idom\<bar> *
     \<bar>(f\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>ordered_idom) ((x\<Colon>'b\<Colon>ordered_idom \<Rightarrow> 'a\<Colon>type) xa)\<bar>
     \<le> xa * \<bar>f (x xa)\<bar>"
show "False"
  by (metis linorder_neq_iff linorder_antisym_conv1 0)
qed

lemma bigo_const_mult2: "O(%x. c * f x) <= O(f)"
by (rule bigo_elt_subset, rule bigo_const_mult1)

declare [[ atp_problem_prefix = "BigO__bigo_const_mult3" ]]
lemma bigo_const_mult3: "(c::'a::ordered_field) ~= 0 ==> f : O(%x. c * f x)"
  apply (simp add: bigo_def)
(*sledgehammer [no luck]*); 
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

declare [[ atp_problem_prefix = "BigO__bigo_const_mult5" ]]
lemma bigo_const_mult5 [simp]: "(c::'a::ordered_field) ~= 0 ==> 
    (%x. c) *o O(f) = O(f)"
  apply (auto del: subsetI)
  apply (rule order_trans)
  apply (rule bigo_mult2)
  apply (simp add: func_times)
  apply (auto intro!: subsetI simp add: bigo_def elt_set_times_def func_times)
  apply (rule_tac x = "%y. inverse c * x y" in exI)
  apply (rename_tac g d) 
  apply safe
  apply (rule_tac [2] ext) 
   prefer 2 
   apply simp
  apply (simp add: mult_assoc [symmetric] abs_mult)
  (*couldn't get this proof without the step above; SLOW*)
  apply (metis mult_assoc abs_ge_zero mult_left_mono)
done


declare [[ atp_problem_prefix = "BigO__bigo_const_mult6" ]]
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
  apply (simp only: set_minus_plus [symmetric] diff_minus fun_Compl_def
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

declare [[ atp_problem_prefix = "BigO__bigo_setsum1" ]]
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

declare [[ atp_problem_prefix = "BigO__bigo_setsum3" ]]
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
  apply (subst fun_diff_def)
  apply (subst setsum_subtractf [symmetric])
  apply (subst right_diff_distrib [symmetric])
  apply (rule bigo_setsum3)
  apply (subst fun_diff_def [symmetric])
  apply (erule set_plus_imp_minus)
done

declare [[ atp_problem_prefix = "BigO__bigo_setsum5" ]]
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
apply (metis abs_of_nonneg zero_le_mult_iff)
done

lemma bigo_setsum6: "f =o g +o O(h) ==> ALL x y. 0 <= l x y ==>
    ALL x. 0 <= h x ==>
      (%x. SUM y : A x. (l x y) * f(k x y)) =o
        (%x. SUM y : A x. (l x y) * g(k x y)) +o
          O(%x. SUM y : A x. (l x y) * h(k x y))" 
  apply (rule set_minus_imp_plus)
  apply (subst fun_diff_def)
  apply (subst setsum_subtractf [symmetric])
  apply (subst right_diff_distrib [symmetric])
  apply (rule bigo_setsum5)
  apply (subst fun_diff_def [symmetric])
  apply (drule set_plus_imp_minus)
  apply auto
done

subsection {* Misc useful stuff *}

lemma bigo_useful_intro: "A <= O(f) ==> B <= O(f) ==>
  A \<oplus> B <= O(f)"
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

declare [[ atp_problem_prefix = "BigO__bigo_fix" ]]
lemma bigo_fix: "(%x. f ((x::nat) + 1)) =o O(%x. h(x + 1)) ==> f 0 = 0 ==>
    f =o O(h)"
  apply (simp add: bigo_alt_def)
(*sledgehammer*); 
  apply clarify
  apply (rule_tac x = c in exI)
  apply safe
  apply (case_tac "x = 0")
apply (metis OrderedGroup.abs_ge_zero  OrderedGroup.abs_zero  order_less_le  Ring_and_Field.split_mult_pos_le) 
  apply (subgoal_tac "x = Suc (x - 1)")
  apply metis
  apply simp
  done


lemma bigo_fix2: 
    "(%x. f ((x::nat) + 1)) =o (%x. g(x + 1)) +o O(%x. h(x + 1)) ==> 
       f 0 = g 0 ==> f =o g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_fix)
  apply (subst fun_diff_def)
  apply (subst fun_diff_def [symmetric])
  apply (rule set_plus_imp_minus)
  apply simp
  apply (simp add: fun_diff_def)
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

declare [[ atp_problem_prefix = "BigO__bigo_lesso1" ]]
lemma bigo_lesso1: "ALL x. f x <= g x ==> f <o g =o O(h)"
  apply (unfold lesso_def)
  apply (subgoal_tac "(%x. max (f x - g x) 0) = 0")
(*??Translation of TSTP raised an exception: Type unification failed: Variable ?'X2.0::type not of sort ord*)
apply (metis bigo_zero)
  apply (unfold func_zero)
  apply (rule ext)
  apply (simp split: split_max)
done


declare [[ atp_problem_prefix = "BigO__bigo_lesso2" ]]
lemma bigo_lesso2: "f =o g +o O(h) ==>
    ALL x. 0 <= k x ==> ALL x. k x <= f x ==>
      k <o g =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst fun_diff_def)
apply (erule thin_rl)
(*sledgehammer*);  
  apply (case_tac "0 <= k x - g x")
  prefer 2 (*re-order subgoals because I don't know what to put after a structured proof*)
   apply (metis abs_ge_zero abs_minus_commute linorder_linear min_max.sup_absorb1 min_max.sup_commute)
proof (neg_clausify)
fix x
assume 0: "\<And>A. k A \<le> f A"
have 1: "\<And>(X1\<Colon>'b\<Colon>ordered_idom) X2. \<not> max X1 X2 < X1"
  by (metis linorder_not_less le_maxI1)  (*sort inserted by hand*)
assume 2: "(0\<Colon>'b) \<le> k x - g x"
have 3: "\<not> k x - g x < (0\<Colon>'b)"
  by (metis 2 linorder_not_less)
have 4: "\<And>X1 X2. min X1 (k X2) \<le> f X2"
  by (metis min_max.inf_le2 min_max.le_inf_iff min_max.le_iff_inf 0)
have 5: "\<bar>g x - f x\<bar> = f x - g x"
  by (metis abs_minus_commute combine_common_factor mult_zero_right minus_add_cancel minus_zero abs_if diff_less_eq min_max.inf_commute 4 linorder_not_le min_max.le_iff_inf 3 diff_less_0_iff_less linorder_not_less)
have 6: "max (0\<Colon>'b) (k x - g x) = k x - g x"
  by (metis min_max.le_iff_sup 2)
assume 7: "\<not> max (k x - g x) (0\<Colon>'b) \<le> \<bar>f x - g x\<bar>"
have 8: "\<not> k x - g x \<le> f x - g x"
  by (metis 5 abs_minus_commute 7 min_max.sup_commute 6)
show "False"
  by (metis min_max.sup_commute min_max.inf_commute min_max.sup_inf_absorb min_max.le_iff_inf 0 max_diff_distrib_left 1 linorder_not_le 8)
qed

declare [[ atp_problem_prefix = "BigO__bigo_lesso3" ]]
lemma bigo_lesso3: "f =o g +o O(h) ==>
    ALL x. 0 <= k x ==> ALL x. g x <= k x ==>
      f <o k =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst fun_diff_def)
apply (erule thin_rl) 
(*sledgehammer*); 
  apply (case_tac "0 <= f x - k x")
  apply (simp)
  apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
using [[ atp_problem_prefix = "BigO__bigo_lesso3_simpler" ]]
apply (metis diff_less_0_iff_less linorder_not_le not_leE uminus_add_conv_diff xt1(12) xt1(6))
apply (metis add_minus_cancel diff_le_eq le_diff_eq uminus_add_conv_diff)
apply (metis abs_ge_zero linorder_linear min_max.sup_absorb1 min_max.sup_commute)
done

lemma bigo_lesso4: "f <o g =o O(k::'a=>'b::ordered_field) ==>
    g =o h +o O(k) ==> f <o h =o O(k)"
  apply (unfold lesso_def)
  apply (drule set_plus_imp_minus)
  apply (drule bigo_abs5) back
  apply (simp add: fun_diff_def)
  apply (drule bigo_useful_add)
  apply assumption
  apply (erule bigo_lesseq2) back
  apply (rule allI)
  apply (auto simp add: func_plus fun_diff_def algebra_simps
    split: split_max abs_split)
done

declare [[ atp_problem_prefix = "BigO__bigo_lesso5" ]]
lemma bigo_lesso5: "f <o g =o O(h) ==>
    EX C. ALL x. f x <= g x + C * abs(h x)"
  apply (simp only: lesso_def bigo_alt_def)
  apply clarsimp
  apply (metis abs_if abs_mult add_commute diff_le_eq less_not_permute)  
done

end
