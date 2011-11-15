(*  Title:      HOL/Metis_Examples/Big_O.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring the Big O notation.
*)

header {* Metis Example Featuring the Big O Notation *}

theory Big_O
imports
  "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
  Main
  "~~/src/HOL/Library/Function_Algebras"
  "~~/src/HOL/Library/Set_Algebras"
begin

declare [[metis_new_skolemizer]]

subsection {* Definitions *}

definition bigo :: "('a => 'b::{linordered_idom,number_ring}) => ('a => 'b) set"    ("(1O'(_'))") where
  "O(f::('a => 'b)) ==   {h. EX c. ALL x. abs (h x) <= c * abs (f x)}"

declare [[ sledgehammer_problem_prefix = "BigO__bigo_pos_const" ]]
lemma bigo_pos_const: "(EX (c::'a::linordered_idom).
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
  apply (metis abs_ge_zero abs_of_nonneg Orderings.xt1(6) abs_mult)
  done

(*** Now various verions with an increasing shrink factor ***)

sledgehammer_params [isar_proof, isar_shrink_factor = 1]

lemma (*bigo_pos_const:*) "(EX (c::'a::linordered_idom).
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have F1: "\<forall>x\<^isub>1\<Colon>'a\<Colon>linordered_idom. 0 \<le> \<bar>x\<^isub>1\<bar>" by (metis abs_ge_zero)
  have F2: "\<forall>x\<^isub>1\<Colon>'a\<Colon>linordered_idom. 1 * x\<^isub>1 = x\<^isub>1" by (metis mult_1)
  have F3: "\<forall>x\<^isub>1 x\<^isub>3. x\<^isub>3 \<le> \<bar>h x\<^isub>1\<bar> \<longrightarrow> x\<^isub>3 \<le> c * \<bar>f x\<^isub>1\<bar>" by (metis A1 order_trans)
  have F4: "\<forall>x\<^isub>2 x\<^isub>3\<Colon>'a\<Colon>linordered_idom. \<bar>x\<^isub>3\<bar> * \<bar>x\<^isub>2\<bar> = \<bar>x\<^isub>3 * x\<^isub>2\<bar>"
    by (metis abs_mult)
  have F5: "\<forall>x\<^isub>3 x\<^isub>1\<Colon>'a\<Colon>linordered_idom. 0 \<le> x\<^isub>1 \<longrightarrow> \<bar>x\<^isub>3 * x\<^isub>1\<bar> = \<bar>x\<^isub>3\<bar> * x\<^isub>1"
    by (metis abs_mult_pos)
  hence "\<forall>x\<^isub>1\<ge>0. \<bar>x\<^isub>1\<Colon>'a\<Colon>linordered_idom\<bar> = \<bar>1\<bar> * x\<^isub>1" by (metis F2)
  hence "\<forall>x\<^isub>1\<ge>0. \<bar>x\<^isub>1\<Colon>'a\<Colon>linordered_idom\<bar> = x\<^isub>1" by (metis F2 abs_one)
  hence "\<forall>x\<^isub>3. 0 \<le> \<bar>h x\<^isub>3\<bar> \<longrightarrow> \<bar>c * \<bar>f x\<^isub>3\<bar>\<bar> = c * \<bar>f x\<^isub>3\<bar>" by (metis F3)
  hence "\<forall>x\<^isub>3. \<bar>c * \<bar>f x\<^isub>3\<bar>\<bar> = c * \<bar>f x\<^isub>3\<bar>" by (metis F1)
  hence "\<forall>x\<^isub>3. (0\<Colon>'a) \<le> \<bar>f x\<^isub>3\<bar> \<longrightarrow> c * \<bar>f x\<^isub>3\<bar> = \<bar>c\<bar> * \<bar>f x\<^isub>3\<bar>" by (metis F5)
  hence "\<forall>x\<^isub>3. (0\<Colon>'a) \<le> \<bar>f x\<^isub>3\<bar> \<longrightarrow> c * \<bar>f x\<^isub>3\<bar> = \<bar>c * f x\<^isub>3\<bar>" by (metis F4)
  hence "\<forall>x\<^isub>3. c * \<bar>f x\<^isub>3\<bar> = \<bar>c * f x\<^isub>3\<bar>" by (metis F1)
  hence "\<bar>h x\<bar> \<le> \<bar>c * f x\<bar>" by (metis A1)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis F4)
qed

sledgehammer_params [isar_proof, isar_shrink_factor = 2]

lemma (*bigo_pos_const:*) "(EX (c::'a::linordered_idom).
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have F1: "\<forall>x\<^isub>1\<Colon>'a\<Colon>linordered_idom. 1 * x\<^isub>1 = x\<^isub>1" by (metis mult_1)
  have F2: "\<forall>x\<^isub>2 x\<^isub>3\<Colon>'a\<Colon>linordered_idom. \<bar>x\<^isub>3\<bar> * \<bar>x\<^isub>2\<bar> = \<bar>x\<^isub>3 * x\<^isub>2\<bar>"
    by (metis abs_mult)
  have "\<forall>x\<^isub>1\<ge>0. \<bar>x\<^isub>1\<Colon>'a\<Colon>linordered_idom\<bar> = x\<^isub>1" by (metis F1 abs_mult_pos abs_one)
  hence "\<forall>x\<^isub>3. \<bar>c * \<bar>f x\<^isub>3\<bar>\<bar> = c * \<bar>f x\<^isub>3\<bar>" by (metis A1 abs_ge_zero order_trans)
  hence "\<forall>x\<^isub>3. 0 \<le> \<bar>f x\<^isub>3\<bar> \<longrightarrow> c * \<bar>f x\<^isub>3\<bar> = \<bar>c * f x\<^isub>3\<bar>" by (metis F2 abs_mult_pos)
  hence "\<bar>h x\<bar> \<le> \<bar>c * f x\<bar>" by (metis A1 abs_ge_zero)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis F2)
qed

sledgehammer_params [isar_proof, isar_shrink_factor = 3]

lemma (*bigo_pos_const:*) "(EX (c::'a::linordered_idom).
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have F1: "\<forall>x\<^isub>1\<Colon>'a\<Colon>linordered_idom. 1 * x\<^isub>1 = x\<^isub>1" by (metis mult_1)
  have F2: "\<forall>x\<^isub>3 x\<^isub>1\<Colon>'a\<Colon>linordered_idom. 0 \<le> x\<^isub>1 \<longrightarrow> \<bar>x\<^isub>3 * x\<^isub>1\<bar> = \<bar>x\<^isub>3\<bar> * x\<^isub>1" by (metis abs_mult_pos)
  hence "\<forall>x\<^isub>1\<ge>0. \<bar>x\<^isub>1\<Colon>'a\<Colon>linordered_idom\<bar> = x\<^isub>1" by (metis F1 abs_one)
  hence "\<forall>x\<^isub>3. 0 \<le> \<bar>f x\<^isub>3\<bar> \<longrightarrow> c * \<bar>f x\<^isub>3\<bar> = \<bar>c\<bar> * \<bar>f x\<^isub>3\<bar>" by (metis F2 A1 abs_ge_zero order_trans)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis A1 abs_mult abs_ge_zero)
qed

sledgehammer_params [isar_proof, isar_shrink_factor = 4]

lemma (*bigo_pos_const:*) "(EX (c::'a::linordered_idom).
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "abs c" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have "\<forall>x\<^isub>1\<Colon>'a\<Colon>linordered_idom. 1 * x\<^isub>1 = x\<^isub>1" by (metis mult_1)
  hence "\<forall>x\<^isub>3. \<bar>c * \<bar>f x\<^isub>3\<bar>\<bar> = c * \<bar>f x\<^isub>3\<bar>"
    by (metis A1 abs_ge_zero order_trans abs_mult_pos abs_one)
  hence "\<bar>h x\<bar> \<le> \<bar>c * f x\<bar>" by (metis A1 abs_ge_zero abs_mult_pos abs_mult)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis abs_mult)
qed

sledgehammer_params [isar_proof, isar_shrink_factor = 1]

lemma bigo_alt_def: "O(f) =
    {h. EX c. (0 < c & (ALL x. abs (h x) <= c * abs (f x)))}"
by (auto simp add: bigo_def bigo_pos_const)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_elt_subset" ]]
lemma bigo_elt_subset [intro]: "f : O(g) ==> O(f) <= O(g)"
  apply (auto simp add: bigo_alt_def)
  apply (rule_tac x = "ca * c" in exI)
  apply (rule conjI)
  apply (rule mult_pos_pos)
  apply (assumption)+
(*sledgehammer*)
  apply (rule allI)
  apply (drule_tac x = "xa" in spec)+
  apply (subgoal_tac "ca * abs(f xa) <= ca * (c * abs(g xa))")
  apply (erule order_trans)
  apply (simp add: mult_ac)
  apply (rule mult_left_mono, assumption)
  apply (rule order_less_imp_le, assumption)
done


declare [[ sledgehammer_problem_prefix = "BigO__bigo_refl" ]]
lemma bigo_refl [intro]: "f : O(f)"
apply (auto simp add: bigo_def)
by (metis mult_1 order_refl)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_zero" ]]
lemma bigo_zero: "0 : O(g)"
apply (auto simp add: bigo_def func_zero)
by (metis mult_zero_left order_refl)

lemma bigo_zero2: "O(%x.0) = {%x.0}"
  by (auto simp add: bigo_def)

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
  apply (simp add: abs_triangle_ineq)
  apply (simp add: order_less_le)
  apply (rule mult_nonneg_nonneg)
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
  apply (rule abs_triangle_ineq)
  apply (simp add: order_less_le)
apply (metis abs_not_less_zero double_less_0_iff less_not_permute linorder_not_less mult_less_0_iff)
done

lemma bigo_plus_subset2 [intro]: "A <= O(f) ==> B <= O(f) ==> A \<oplus> B <= O(f)"
  apply (subgoal_tac "A \<oplus> B <= O(f) \<oplus> O(f)")
  apply (erule order_trans)
  apply simp
  apply (auto del: subsetI simp del: bigo_plus_idemp)
done

declare [[ sledgehammer_problem_prefix = "BigO__bigo_plus_eq" ]]
lemma bigo_plus_eq: "ALL x. 0 <= f x ==> ALL x. 0 <= g x ==>
  O(f + g) = O(f) \<oplus> O(g)"
  apply (rule equalityI)
  apply (rule bigo_plus_subset)
  apply (simp add: bigo_alt_def set_plus_def func_plus)
  apply clarify
(*sledgehammer*)
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
using [[ sledgehammer_problem_prefix = "BigO__bigo_plus_eq_simpler" ]]
  apply (metis le_maxI2 linorder_linear min_max.sup_absorb1 mult_right_mono xt1(6))
  apply (metis le_maxI2 linorder_not_le mult_le_cancel_right order_trans)
done

declare [[ sledgehammer_problem_prefix = "BigO__bigo_bounded_alt" ]]
lemma bigo_bounded_alt: "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==>
    f : O(g)"
  apply (auto simp add: bigo_def)
(* Version 1: one-line proof *)
  apply (metis abs_le_D1 linorder_class.not_less  order_less_le  Orderings.xt1(12)  abs_mult)
  done

lemma (*bigo_bounded_alt:*) "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==>
    f : O(g)"
apply (auto simp add: bigo_def)
(* Version 2: structured proof *)
proof -
  assume "\<forall>x. f x \<le> c * g x"
  thus "\<exists>c. \<forall>x. f x \<le> c * \<bar>g x\<bar>" by (metis abs_mult abs_ge_self order_trans)
qed

text{*So here is the easier (and more natural) problem using transitivity*}
declare [[ sledgehammer_problem_prefix = "BigO__bigo_bounded_alt_trans" ]]
lemma "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> f : O(g)"
apply (auto simp add: bigo_def)
(* Version 1: one-line proof *)
by (metis abs_ge_self abs_mult order_trans)

text{*So here is the easier (and more natural) problem using transitivity*}
declare [[ sledgehammer_problem_prefix = "BigO__bigo_bounded_alt_trans" ]]
lemma "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> f : O(g)"
  apply (auto simp add: bigo_def)
(* Version 2: structured proof *)
proof -
  assume "\<forall>x. f x \<le> c * g x"
  thus "\<exists>c. \<forall>x. f x \<le> c * \<bar>g x\<bar>" by (metis abs_mult abs_ge_self order_trans)
qed

lemma bigo_bounded: "ALL x. 0 <= f x ==> ALL x. f x <= g x ==>
    f : O(g)"
  apply (erule bigo_bounded_alt [of f 1 g])
  apply simp
done

declare [[ sledgehammer_problem_prefix = "BigO__bigo_bounded2" ]]
lemma bigo_bounded2: "ALL x. lb x <= f x ==> ALL x. f x <= lb x + g x ==>
    f : lb +o O(g)"
apply (rule set_minus_imp_plus)
apply (rule bigo_bounded)
 apply (auto simp add: diff_minus fun_Compl_def func_plus)
 prefer 2
 apply (drule_tac x = x in spec)+
 apply (metis add_right_mono add_commute diff_add_cancel diff_minus_eq_add le_less order_trans)
proof -
  fix x :: 'a
  assume "\<forall>x. lb x \<le> f x"
  thus "(0\<Colon>'b) \<le> f x + - lb x" by (metis not_leE diff_minus less_iff_diff_less_0 less_le_not_le)
qed

declare [[ sledgehammer_problem_prefix = "BigO__bigo_abs" ]]
lemma bigo_abs: "(%x. abs(f x)) =o O(f)"
apply (unfold bigo_def)
apply auto
by (metis mult_1 order_refl)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_abs2" ]]
lemma bigo_abs2: "f =o O(%x. abs(f x))"
apply (unfold bigo_def)
apply auto
by (metis mult_1 order_refl)

lemma bigo_abs3: "O(f) = O(%x. abs(f x))"
proof -
  have F1: "\<forall>v u. u \<in> O(v) \<longrightarrow> O(u) \<subseteq> O(v)" by (metis bigo_elt_subset)
  have F2: "\<forall>u. (\<lambda>R. \<bar>u R\<bar>) \<in> O(u)" by (metis bigo_abs)
  have "\<forall>u. u \<in> O(\<lambda>R. \<bar>u R\<bar>)" by (metis bigo_abs2)
  thus "O(f) = O(\<lambda>x. \<bar>f x\<bar>)" using F1 F2 by auto
qed

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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_mult" ]]
lemma bigo_mult [intro]: "O(f)\<otimes>O(g) <= O(f * g)"
  apply (rule subsetI)
  apply (subst bigo_def)
  apply (auto simp del: abs_mult mult_ac
              simp add: bigo_alt_def set_times_def func_times)
(*sledgehammer*)
  apply (rule_tac x = "c * ca" in exI)
  apply(rule allI)
  apply(erule_tac x = x in allE)+
  apply(subgoal_tac "c * ca * abs(f x * g x) =
      (c * abs(f x)) * (ca * abs(g x))")
using [[ sledgehammer_problem_prefix = "BigO__bigo_mult_simpler" ]]
prefer 2
apply (metis mult_assoc mult_left_commute
  abs_of_pos mult_left_commute
  abs_mult mult_pos_pos)
  apply (erule ssubst)
  apply (subst abs_mult)
(* not quite as hard as BigO__bigo_mult_simpler_1 (a hard problem!) since
   abs_mult has just been done *)
by (metis abs_ge_zero mult_mono')

declare [[ sledgehammer_problem_prefix = "BigO__bigo_mult2" ]]
lemma bigo_mult2 [intro]: "f *o O(g) <= O(f * g)"
  apply (auto simp add: bigo_def elt_set_times_def func_times abs_mult)
(*sledgehammer*)
  apply (rule_tac x = c in exI)
  apply clarify
  apply (drule_tac x = x in spec)
using [[ sledgehammer_problem_prefix = "BigO__bigo_mult2_simpler" ]]
(*sledgehammer [no luck]*)
  apply (subgoal_tac "abs(f x) * abs(b x) <= abs(f x) * (c * abs(g x))")
  apply (simp add: mult_ac)
  apply (rule mult_left_mono, assumption)
  apply (rule abs_ge_zero)
done

declare [[ sledgehammer_problem_prefix = "BigO__bigo_mult3" ]]
lemma bigo_mult3: "f : O(h) ==> g : O(j) ==> f * g : O(h * j)"
by (metis bigo_mult set_rev_mp set_times_intro)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_mult4" ]]
lemma bigo_mult4 [intro]:"f : k +o O(h) ==> g * f : (g * k) +o O(g * h)"
by (metis bigo_mult2 set_plus_mono_b set_times_intro2 set_times_plus_distrib)


lemma bigo_mult5: "ALL x. f x ~= 0 ==>
    O(f * g) <= (f::'a => ('b::{linordered_field,number_ring})) *o O(g)"
proof -
  assume a: "ALL x. f x ~= 0"
  show "O(f * g) <= f *o O(g)"
  proof
    fix h
    assume h: "h : O(f * g)"
    then have "(%x. 1 / (f x)) * h : (%x. 1 / f x) *o O(f * g)"
      by auto
    also have "... <= O((%x. 1 / f x) * (f * g))"
      by (rule bigo_mult2)
    also have "(%x. 1 / f x) * (f * g) = g"
      apply (simp add: func_times)
      apply (rule ext)
      apply (simp add: a h nonzero_divide_eq_eq mult_ac)
      done
    finally have "(%x. (1::'b) / f x) * h : O(g)".
    then have "f * ((%x. (1::'b) / f x) * h) : f *o O(g)"
      by auto
    also have "f * ((%x. (1::'b) / f x) * h) = h"
      apply (simp add: func_times)
      apply (rule ext)
      apply (simp add: a h nonzero_divide_eq_eq mult_ac)
      done
    finally show "h : f *o O(g)".
  qed
qed

declare [[ sledgehammer_problem_prefix = "BigO__bigo_mult6" ]]
lemma bigo_mult6: "ALL x. f x ~= 0 ==>
    O(f * g) = (f::'a => ('b::{linordered_field,number_ring})) *o O(g)"
by (metis bigo_mult2 bigo_mult5 order_antisym)

(*proof requires relaxing relevance: 2007-01-25*)
declare [[ sledgehammer_problem_prefix = "BigO__bigo_mult7" ]]
  declare bigo_mult6 [simp]
lemma bigo_mult7: "ALL x. f x ~= 0 ==>
    O(f * g) <= O(f::'a => ('b::{linordered_field,number_ring})) \<otimes> O(g)"
(*sledgehammer*)
  apply (subst bigo_mult6)
  apply assumption
  apply (rule set_times_mono3)
  apply (rule bigo_refl)
done
  declare bigo_mult6 [simp del]

declare [[ sledgehammer_problem_prefix = "BigO__bigo_mult8" ]]
  declare bigo_mult7[intro!]
lemma bigo_mult8: "ALL x. f x ~= 0 ==>
    O(f * g) = O(f::'a => ('b::{linordered_field,number_ring})) \<otimes> O(g)"
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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_plus_absorb" ]]
lemma bigo_plus_absorb [simp]: "f : O(g) ==> f +o O(g) = O(g)"
by (metis bigo_plus_absorb_lemma1 bigo_plus_absorb_lemma2 order_eq_iff)

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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_const2" ]]
lemma (*bigo_const2 [intro]:*) "O(%x. c) <= O(%x. 1)"
by (metis bigo_const1 bigo_elt_subset)

lemma bigo_const2 [intro]: "O(%x. c::'b::{linordered_idom,number_ring}) <= O(%x. 1)"
(* "thus" had to be replaced by "show" with an explicit reference to "F1" *)
proof -
  have F1: "\<forall>u. (\<lambda>Q. u) \<in> O(\<lambda>Q. 1)" by (metis bigo_const1)
  show "O(\<lambda>x. c) \<subseteq> O(\<lambda>x. 1)" by (metis F1 bigo_elt_subset)
qed

declare [[ sledgehammer_problem_prefix = "BigO__bigo_const3" ]]
lemma bigo_const3: "(c::'a::{linordered_field,number_ring}) ~= 0 ==> (%x. 1) : O(%x. c)"
apply (simp add: bigo_def)
by (metis abs_eq_0 left_inverse order_refl)

lemma bigo_const4: "(c::'a::{linordered_field,number_ring}) ~= 0 ==> O(%x. 1) <= O(%x. c)"
by (rule bigo_elt_subset, rule bigo_const3, assumption)

lemma bigo_const [simp]: "(c::'a::{linordered_field,number_ring}) ~= 0 ==>
    O(%x. c) = O(%x. 1)"
by (rule equalityI, rule bigo_const2, rule bigo_const4, assumption)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_const_mult1" ]]
lemma bigo_const_mult1: "(%x. c * f x) : O(f)"
  apply (simp add: bigo_def abs_mult)
by (metis le_less)

lemma bigo_const_mult2: "O(%x. c * f x) <= O(f)"
by (rule bigo_elt_subset, rule bigo_const_mult1)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_const_mult3" ]]
lemma bigo_const_mult3: "(c::'a::{linordered_field,number_ring}) ~= 0 ==> f : O(%x. c * f x)"
  apply (simp add: bigo_def)
(*sledgehammer [no luck]*)
  apply (rule_tac x = "abs(inverse c)" in exI)
  apply (simp only: abs_mult [symmetric] mult_assoc [symmetric])
apply (subst left_inverse)
apply (auto )
done

lemma bigo_const_mult4: "(c::'a::{linordered_field,number_ring}) ~= 0 ==>
    O(f) <= O(%x. c * f x)"
by (rule bigo_elt_subset, rule bigo_const_mult3, assumption)

lemma bigo_const_mult [simp]: "(c::'a::{linordered_field,number_ring}) ~= 0 ==>
    O(%x. c * f x) = O(f)"
by (rule equalityI, rule bigo_const_mult2, erule bigo_const_mult4)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_const_mult5" ]]
lemma bigo_const_mult5 [simp]: "(c::'a::{linordered_field,number_ring}) ~= 0 ==>
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
  (* couldn't get this proof without the step above *)
proof -
  fix g :: "'b \<Rightarrow> 'a" and d :: 'a
  assume A1: "c \<noteq> (0\<Colon>'a)"
  assume A2: "\<forall>x\<Colon>'b. \<bar>g x\<bar> \<le> d * \<bar>f x\<bar>"
  have F1: "inverse \<bar>c\<bar> = \<bar>inverse c\<bar>" using A1 by (metis nonzero_abs_inverse)
  have F2: "(0\<Colon>'a) < \<bar>c\<bar>" using A1 by (metis zero_less_abs_iff)
  have "(0\<Colon>'a) < \<bar>c\<bar> \<longrightarrow> (0\<Colon>'a) < \<bar>inverse c\<bar>" using F1 by (metis positive_imp_inverse_positive)
  hence "(0\<Colon>'a) < \<bar>inverse c\<bar>" using F2 by metis
  hence F3: "(0\<Colon>'a) \<le> \<bar>inverse c\<bar>" by (metis order_le_less)
  have "\<exists>(u\<Colon>'a) SKF\<^isub>7\<Colon>'a \<Rightarrow> 'b. \<bar>g (SKF\<^isub>7 (\<bar>inverse c\<bar> * u))\<bar> \<le> u * \<bar>f (SKF\<^isub>7 (\<bar>inverse c\<bar> * u))\<bar>"
    using A2 by metis
  hence F4: "\<exists>(u\<Colon>'a) SKF\<^isub>7\<Colon>'a \<Rightarrow> 'b. \<bar>g (SKF\<^isub>7 (\<bar>inverse c\<bar> * u))\<bar> \<le> u * \<bar>f (SKF\<^isub>7 (\<bar>inverse c\<bar> * u))\<bar> \<and> (0\<Colon>'a) \<le> \<bar>inverse c\<bar>"
    using F3 by metis
  hence "\<exists>(v\<Colon>'a) (u\<Colon>'a) SKF\<^isub>7\<Colon>'a \<Rightarrow> 'b. \<bar>inverse c\<bar> * \<bar>g (SKF\<^isub>7 (u * v))\<bar> \<le> u * (v * \<bar>f (SKF\<^isub>7 (u * v))\<bar>)"
    by (metis comm_mult_left_mono)
  thus "\<exists>ca\<Colon>'a. \<forall>x\<Colon>'b. \<bar>inverse c\<bar> * \<bar>g x\<bar> \<le> ca * \<bar>f x\<bar>"
    using A2 F4 by (metis ab_semigroup_mult_class.mult_ac(1) comm_mult_left_mono)
qed


declare [[ sledgehammer_problem_prefix = "BigO__bigo_const_mult6" ]]
lemma bigo_const_mult6 [intro]: "(%x. c) *o O(f) <= O(f)"
  apply (auto intro!: subsetI
    simp add: bigo_def elt_set_times_def func_times
    simp del: abs_mult mult_ac)
(*sledgehammer*)
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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_setsum1" ]]
lemma bigo_setsum1: "ALL x y. 0 <= h x y ==>
    EX c. ALL x y. abs(f x y) <= c * (h x y) ==>
      (%x. SUM y : A x. f x y) =o O(%x. SUM y : A x. h x y)"
  apply (rule bigo_setsum_main)
(*sledgehammer*)
  apply force
  apply clarsimp
  apply (rule_tac x = c in exI)
  apply force
done

lemma bigo_setsum2: "ALL y. 0 <= h y ==>
    EX c. ALL y. abs(f y) <= c * (h y) ==>
      (%x. SUM y : A x. f y) =o O(%x. SUM y : A x. h y)"
by (rule bigo_setsum1, auto)

declare [[ sledgehammer_problem_prefix = "BigO__bigo_setsum3" ]]
lemma bigo_setsum3: "f =o O(h) ==>
    (%x. SUM y : A x. (l x y) * f(k x y)) =o
      O(%x. SUM y : A x. abs(l x y * h(k x y)))"
  apply (rule bigo_setsum1)
  apply (rule allI)+
  apply (rule abs_ge_zero)
  apply (unfold bigo_def)
  apply (auto simp add: abs_mult)
(*sledgehammer*)
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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_setsum5" ]]
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

lemma bigo_useful_const_mult: "(c::'a::{linordered_field,number_ring}) ~= 0 ==>
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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_fix" ]]
lemma bigo_fix: "(%x. f ((x::nat) + 1)) =o O(%x. h(x + 1)) ==> f 0 = 0 ==>
    f =o O(h)"
  apply (simp add: bigo_alt_def)
(*sledgehammer*)
  apply clarify
  apply (rule_tac x = c in exI)
  apply safe
  apply (case_tac "x = 0")
apply (metis abs_ge_zero  abs_zero  order_less_le  split_mult_pos_le)
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

definition lesso :: "('a => 'b::linordered_idom) => ('a => 'b) => ('a => 'b)" (infixl "<o" 70) where
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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_lesso1" ]]
lemma bigo_lesso1: "ALL x. f x <= g x ==> f <o g =o O(h)"
apply (unfold lesso_def)
apply (subgoal_tac "(%x. max (f x - g x) 0) = 0")
proof -
  assume "(\<lambda>x. max (f x - g x) 0) = 0"
  thus "(\<lambda>x. max (f x - g x) 0) \<in> O(h)" by (metis bigo_zero)
next
  show "\<forall>x\<Colon>'a. f x \<le> g x \<Longrightarrow> (\<lambda>x\<Colon>'a. max (f x - g x) (0\<Colon>'b)) = (0\<Colon>'a \<Rightarrow> 'b)"
  apply (unfold func_zero)
  apply (rule ext)
  by (simp split: split_max)
qed

declare [[ sledgehammer_problem_prefix = "BigO__bigo_lesso2" ]]
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
(*sledgehammer*)
  apply (case_tac "0 <= k x - g x")
(* apply (metis abs_le_iff add_le_imp_le_right diff_minus le_less
                le_max_iff_disj min_max.le_supE min_max.sup_absorb2
                min_max.sup_commute) *)
proof -
  fix x :: 'a
  assume "\<forall>x\<Colon>'a. k x \<le> f x"
  hence F1: "\<forall>x\<^isub>1\<Colon>'a. max (k x\<^isub>1) (f x\<^isub>1) = f x\<^isub>1" by (metis min_max.sup_absorb2)
  assume "(0\<Colon>'b) \<le> k x - g x"
  hence F2: "max (0\<Colon>'b) (k x - g x) = k x - g x" by (metis min_max.sup_absorb2)
  have F3: "\<forall>x\<^isub>1\<Colon>'b. x\<^isub>1 \<le> \<bar>x\<^isub>1\<bar>" by (metis abs_le_iff le_less)
  have "\<forall>(x\<^isub>2\<Colon>'b) x\<^isub>1\<Colon>'b. max x\<^isub>1 x\<^isub>2 \<le> x\<^isub>2 \<or> max x\<^isub>1 x\<^isub>2 \<le> x\<^isub>1" by (metis le_less le_max_iff_disj)
  hence "\<forall>(x\<^isub>3\<Colon>'b) (x\<^isub>2\<Colon>'b) x\<^isub>1\<Colon>'b. x\<^isub>1 - x\<^isub>2 \<le> x\<^isub>3 - x\<^isub>2 \<or> x\<^isub>3 \<le> x\<^isub>1" by (metis add_le_imp_le_right diff_minus min_max.le_supE)
  hence "k x - g x \<le> f x - g x" by (metis F1 le_less min_max.sup_absorb2 min_max.sup_commute)
  hence "k x - g x \<le> \<bar>f x - g x\<bar>" by (metis F3 le_max_iff_disj min_max.sup_absorb2)
  thus "max (k x - g x) (0\<Colon>'b) \<le> \<bar>f x - g x\<bar>" by (metis F2 min_max.sup_commute)
next
  show "\<And>x\<Colon>'a.
       \<lbrakk>\<forall>x\<Colon>'a. (0\<Colon>'b) \<le> k x; \<forall>x\<Colon>'a. k x \<le> f x; \<not> (0\<Colon>'b) \<le> k x - g x\<rbrakk>
       \<Longrightarrow> max (k x - g x) (0\<Colon>'b) \<le> \<bar>f x - g x\<bar>"
    by (metis abs_ge_zero le_cases min_max.sup_absorb2)
qed

declare [[ sledgehammer_problem_prefix = "BigO__bigo_lesso3" ]]
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
(*sledgehammer*)
  apply (case_tac "0 <= f x - k x")
  apply (simp)
  apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
using [[ sledgehammer_problem_prefix = "BigO__bigo_lesso3_simpler" ]]
apply (metis diff_less_0_iff_less linorder_not_le not_leE uminus_add_conv_diff xt1(12) xt1(6))
apply (metis add_minus_cancel diff_le_eq le_diff_eq uminus_add_conv_diff)
apply (metis abs_ge_zero linorder_linear min_max.sup_absorb1 min_max.sup_commute)
done

lemma bigo_lesso4: "f <o g =o O(k::'a=>'b::{linordered_field,number_ring}) ==>
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

declare [[ sledgehammer_problem_prefix = "BigO__bigo_lesso5" ]]
lemma bigo_lesso5: "f <o g =o O(h) ==>
    EX C. ALL x. f x <= g x + C * abs(h x)"
  apply (simp only: lesso_def bigo_alt_def)
  apply clarsimp
  apply (metis abs_if abs_mult add_commute diff_le_eq less_not_permute)
done

end
