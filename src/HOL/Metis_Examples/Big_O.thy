(*  Title:      HOL/Metis_Examples/Big_O.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring the Big O notation.
*)

header {* Metis Example Featuring the Big O Notation *}

theory Big_O
imports
  "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
  "~~/src/HOL/Library/Function_Algebras"
  "~~/src/HOL/Library/Set_Algebras"
begin

subsection {* Definitions *}

definition bigo :: "('a => 'b\<Colon>{linordered_idom,number_ring}) => ('a => 'b) set" ("(1O'(_'))") where
  "O(f\<Colon>('a => 'b)) == {h. \<exists>c. \<forall>x. abs (h x) <= c * abs (f x)}"

lemma bigo_pos_const:
  "(\<exists>c\<Colon>'a\<Colon>linordered_idom.
    \<forall>x. abs (h x) \<le> c * abs (f x))
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. abs(h x) \<le> c * abs (f x)))"
by (metis (no_types) abs_ge_zero
      comm_semiring_1_class.normalizing_semiring_rules(7) mult.comm_neutral
      mult_nonpos_nonneg not_leE order_trans zero_less_one)

(*** Now various verions with an increasing shrink factor ***)

sledgehammer_params [isar_proof, isar_shrink_factor = 1]

lemma
  "(\<exists>c\<Colon>'a\<Colon>linordered_idom.
    \<forall>x. abs (h x) \<le> c * abs (f x))
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. abs(h x) \<le> c * abs (f x)))"
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

lemma
  "(\<exists>c\<Colon>'a\<Colon>linordered_idom.
    \<forall>x. abs (h x) \<le> c * abs (f x))
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. abs(h x) \<le> c * abs (f x)))"
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

lemma
  "(\<exists>c\<Colon>'a\<Colon>linordered_idom.
    \<forall>x. abs (h x) \<le> c * abs (f x))
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. abs(h x) \<le> c * abs (f x)))"
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

lemma
  "(\<exists>c\<Colon>'a\<Colon>linordered_idom.
    \<forall>x. abs (h x) \<le> c * abs (f x))
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. abs(h x) \<le> c * abs (f x)))"
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

lemma bigo_alt_def: "O(f) = {h. \<exists>c. (0 < c \<and> (\<forall>x. abs (h x) <= c * abs (f x)))}"
by (auto simp add: bigo_def bigo_pos_const)

lemma bigo_elt_subset [intro]: "f : O(g) \<Longrightarrow> O(f) \<le> O(g)"
apply (auto simp add: bigo_alt_def)
apply (rule_tac x = "ca * c" in exI)
by (metis comm_semiring_1_class.normalizing_semiring_rules(7,19)
          mult_le_cancel_left_pos order_trans mult_pos_pos)

lemma bigo_refl [intro]: "f : O(f)"
unfolding bigo_def mem_Collect_eq
by (metis mult_1 order_refl)

lemma bigo_zero: "0 : O(g)"
apply (auto simp add: bigo_def func_zero)
by (metis mult_zero_left order_refl)

lemma bigo_zero2: "O(\<lambda>x. 0) = {\<lambda>x. 0}"
by (auto simp add: bigo_def)

lemma bigo_plus_self_subset [intro]:
  "O(f) \<oplus> O(f) <= O(f)"
apply (auto simp add: bigo_alt_def set_plus_def)
apply (rule_tac x = "c + ca" in exI)
apply auto
apply (simp add: ring_distribs func_plus)
by (metis order_trans abs_triangle_ineq add_mono)

lemma bigo_plus_idemp [simp]: "O(f) \<oplus> O(f) = O(f)"
by (metis bigo_plus_self_subset bigo_zero set_eq_subset set_zero_plus2)

lemma bigo_plus_subset [intro]: "O(f + g) <= O(f) \<oplus> O(g)"
apply (rule subsetI)
apply (auto simp add: bigo_def bigo_pos_const func_plus set_plus_def)
apply (subst bigo_pos_const [symmetric])+
apply (rule_tac x = "\<lambda>n. if abs (g n) <= (abs (f n)) then x n else 0" in exI)
apply (rule conjI)
 apply (rule_tac x = "c + c" in exI)
 apply clarsimp
 apply auto
  apply (subgoal_tac "c * abs (f xa + g xa) <= (c + c) * abs (f xa)")
   apply (metis mult_2 order_trans)
  apply (subgoal_tac "c * abs (f xa + g xa) <= c * (abs (f xa) + abs (g xa))")
   apply (erule order_trans)
   apply (simp add: ring_distribs)
  apply (rule mult_left_mono)
   apply (simp add: abs_triangle_ineq)
  apply (simp add: order_less_le)
 apply (rule mult_nonneg_nonneg)
  apply auto
apply (rule_tac x = "\<lambda>n. if (abs (f n)) < abs (g n) then x n else 0" in exI)
apply (rule conjI)
 apply (rule_tac x = "c + c" in exI)
 apply auto
 apply (subgoal_tac "c * abs (f xa + g xa) <= (c + c) * abs (g xa)")
  apply (metis order_trans semiring_mult_2)
 apply (subgoal_tac "c * abs (f xa + g xa) <= c * (abs (f xa) + abs (g xa))")
  apply (erule order_trans)
  apply (simp add: ring_distribs)
 apply (metis abs_triangle_ineq mult_le_cancel_left_pos)
by (metis abs_ge_zero abs_of_pos zero_le_mult_iff)

lemma bigo_plus_subset2 [intro]: "A <= O(f) \<Longrightarrow> B <= O(f) \<Longrightarrow> A \<oplus> B <= O(f)"
by (metis bigo_plus_idemp set_plus_mono2)

lemma bigo_plus_eq: "\<forall>x. 0 <= f x \<Longrightarrow> \<forall>x. 0 <= g x \<Longrightarrow> O(f + g) = O(f) \<oplus> O(g)"
apply (rule equalityI)
apply (rule bigo_plus_subset)
apply (simp add: bigo_alt_def set_plus_def func_plus)
apply clarify
(* sledgehammer *)
apply (rule_tac x = "max c ca" in exI)

apply (rule conjI)
 apply (metis less_max_iff_disj)
apply clarify
apply (drule_tac x = "xa" in spec)+
apply (subgoal_tac "0 <= f xa + g xa")
 apply (simp add: ring_distribs)
 apply (subgoal_tac "abs (a xa + b xa) <= abs (a xa) + abs (b xa)")
  apply (subgoal_tac "abs (a xa) + abs (b xa) <=
           max c ca * f xa + max c ca * g xa")
   apply (metis order_trans)
  defer 1
  apply (metis abs_triangle_ineq)
 apply (metis add_nonneg_nonneg)
by (metis (no_types) add_mono le_maxI2 linorder_linear min_max.sup_absorb1
          mult_right_mono xt1(6))

lemma bigo_bounded_alt: "\<forall>x. 0 <= f x \<Longrightarrow> \<forall>x. f x <= c * g x \<Longrightarrow> f : O(g)"
apply (auto simp add: bigo_def)
(* Version 1: one-line proof *)
by (metis abs_le_D1 linorder_class.not_less order_less_le Orderings.xt1(12) abs_mult)

lemma "\<forall>x. 0 <= f x \<Longrightarrow> \<forall>x. f x <= c * g x \<Longrightarrow> f : O(g)"
apply (auto simp add: bigo_def)
(* Version 2: structured proof *)
proof -
  assume "\<forall>x. f x \<le> c * g x"
  thus "\<exists>c. \<forall>x. f x \<le> c * \<bar>g x\<bar>" by (metis abs_mult abs_ge_self order_trans)
qed

lemma bigo_bounded: "\<forall>x. 0 <= f x \<Longrightarrow> \<forall>x. f x <= g x \<Longrightarrow> f : O(g)"
apply (erule bigo_bounded_alt [of f 1 g])
by (metis mult_1)

lemma bigo_bounded2: "\<forall>x. lb x <= f x \<Longrightarrow> \<forall>x. f x <= lb x + g x \<Longrightarrow> f : lb +o O(g)"
apply (rule set_minus_imp_plus)
apply (rule bigo_bounded)
 apply (metis add_le_cancel_left diff_add_cancel diff_self minus_apply
              comm_semiring_1_class.normalizing_semiring_rules(24))
by (metis add_le_cancel_left diff_add_cancel func_plus le_fun_def
          comm_semiring_1_class.normalizing_semiring_rules(24))

lemma bigo_abs: "(\<lambda>x. abs(f x)) =o O(f)"
apply (unfold bigo_def)
apply auto
by (metis mult_1 order_refl)

lemma bigo_abs2: "f =o O(\<lambda>x. abs(f x))"
apply (unfold bigo_def)
apply auto
by (metis mult_1 order_refl)

lemma bigo_abs3: "O(f) = O(\<lambda>x. abs(f x))"
proof -
  have F1: "\<forall>v u. u \<in> O(v) \<longrightarrow> O(u) \<subseteq> O(v)" by (metis bigo_elt_subset)
  have F2: "\<forall>u. (\<lambda>R. \<bar>u R\<bar>) \<in> O(u)" by (metis bigo_abs)
  have "\<forall>u. u \<in> O(\<lambda>R. \<bar>u R\<bar>)" by (metis bigo_abs2)
  thus "O(f) = O(\<lambda>x. \<bar>f x\<bar>)" using F1 F2 by auto
qed

lemma bigo_abs4: "f =o g +o O(h) \<Longrightarrow> (\<lambda>x. abs (f x)) =o (\<lambda>x. abs (g x)) +o O(h)"
  apply (drule set_plus_imp_minus)
  apply (rule set_minus_imp_plus)
  apply (subst fun_diff_def)
proof -
  assume a: "f - g : O(h)"
  have "(\<lambda>x. abs (f x) - abs (g x)) =o O(\<lambda>x. abs(abs (f x) - abs (g x)))"
    by (rule bigo_abs2)
  also have "... <= O(\<lambda>x. abs (f x - g x))"
    apply (rule bigo_elt_subset)
    apply (rule bigo_bounded)
     apply (metis abs_ge_zero)
    by (metis abs_triangle_ineq3)
  also have "... <= O(f - g)"
    apply (rule bigo_elt_subset)
    apply (subst fun_diff_def)
    apply (rule bigo_abs)
    done
  also have "... <= O(h)"
    using a by (rule bigo_elt_subset)
  finally show "(\<lambda>x. abs (f x) - abs (g x)) : O(h)".
qed

lemma bigo_abs5: "f =o O(g) \<Longrightarrow> (\<lambda>x. abs(f x)) =o O(g)"
by (unfold bigo_def, auto)

lemma bigo_elt_subset2 [intro]: "f : g +o O(h) \<Longrightarrow> O(f) <= O(g) \<oplus> O(h)"
proof -
  assume "f : g +o O(h)"
  also have "... <= O(g) \<oplus> O(h)"
    by (auto del: subsetI)
  also have "... = O(\<lambda>x. abs(g x)) \<oplus> O(\<lambda>x. abs(h x))"
    by (metis bigo_abs3)
  also have "... = O((\<lambda>x. abs(g x)) + (\<lambda>x. abs(h x)))"
    by (rule bigo_plus_eq [symmetric], auto)
  finally have "f : ...".
  then have "O(f) <= ..."
    by (elim bigo_elt_subset)
  also have "... = O(\<lambda>x. abs(g x)) \<oplus> O(\<lambda>x. abs(h x))"
    by (rule bigo_plus_eq, auto)
  finally show ?thesis
    by (simp add: bigo_abs3 [symmetric])
qed

lemma bigo_mult [intro]: "O(f) \<otimes> O(g) <= O(f * g)"
apply (rule subsetI)
apply (subst bigo_def)
apply (auto simp del: abs_mult mult_ac
            simp add: bigo_alt_def set_times_def func_times)
(* sledgehammer *)
apply (rule_tac x = "c * ca" in exI)
apply (rule allI)
apply (erule_tac x = x in allE)+
apply (subgoal_tac "c * ca * abs (f x * g x) = (c * abs(f x)) * (ca * abs (g x))")
 apply (metis (no_types) abs_ge_zero abs_mult mult_mono')
by (metis mult_assoc mult_left_commute abs_of_pos mult_left_commute abs_mult)

lemma bigo_mult2 [intro]: "f *o O(g) <= O(f * g)"
by (metis bigo_mult bigo_refl set_times_mono3 subset_trans)

lemma bigo_mult3: "f : O(h) \<Longrightarrow> g : O(j) \<Longrightarrow> f * g : O(h * j)"
by (metis bigo_mult set_rev_mp set_times_intro)

lemma bigo_mult4 [intro]:"f : k +o O(h) \<Longrightarrow> g * f : (g * k) +o O(g * h)"
by (metis bigo_mult2 set_plus_mono_b set_times_intro2 set_times_plus_distrib)

lemma bigo_mult5: "\<forall>x. f x ~= 0 \<Longrightarrow>
    O(f * g) <= (f\<Colon>'a => ('b\<Colon>{linordered_field,number_ring})) *o O(g)"
proof -
  assume a: "\<forall>x. f x ~= 0"
  show "O(f * g) <= f *o O(g)"
  proof
    fix h
    assume h: "h : O(f * g)"
    then have "(\<lambda>x. 1 / (f x)) * h : (\<lambda>x. 1 / f x) *o O(f * g)"
      by auto
    also have "... <= O((\<lambda>x. 1 / f x) * (f * g))"
      by (rule bigo_mult2)
    also have "(\<lambda>x. 1 / f x) * (f * g) = g"
      apply (simp add: func_times)
      by (metis (lifting, no_types) a ext mult_ac(2) nonzero_divide_eq_eq)
    finally have "(\<lambda>x. (1\<Colon>'b) / f x) * h : O(g)".
    then have "f * ((\<lambda>x. (1\<Colon>'b) / f x) * h) : f *o O(g)"
      by auto
    also have "f * ((\<lambda>x. (1\<Colon>'b) / f x) * h) = h"
      apply (simp add: func_times)
      by (metis (lifting, no_types) a eq_divide_imp ext
                comm_semiring_1_class.normalizing_semiring_rules(7))
    finally show "h : f *o O(g)".
  qed
qed

lemma bigo_mult6:
"\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) = (f\<Colon>'a \<Rightarrow> ('b\<Colon>{linordered_field,number_ring})) *o O(g)"
by (metis bigo_mult2 bigo_mult5 order_antisym)

(*proof requires relaxing relevance: 2007-01-25*)
declare bigo_mult6 [simp]

lemma bigo_mult7:
"\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) \<le> O(f\<Colon>'a \<Rightarrow> ('b\<Colon>{linordered_field,number_ring})) \<otimes> O(g)"
by (metis bigo_refl bigo_mult6 set_times_mono3)

declare bigo_mult6 [simp del]
declare bigo_mult7 [intro!]

lemma bigo_mult8:
"\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) = O(f\<Colon>'a \<Rightarrow> ('b\<Colon>{linordered_field,number_ring})) \<otimes> O(g)"
by (metis bigo_mult bigo_mult7 order_antisym_conv)

lemma bigo_minus [intro]: "f : O(g) \<Longrightarrow> - f : O(g)"
by (auto simp add: bigo_def fun_Compl_def)

lemma bigo_minus2: "f : g +o O(h) \<Longrightarrow> -f : -g +o O(h)"
by (metis (no_types) bigo_elt_subset bigo_minus bigo_mult4 bigo_refl
          comm_semiring_1_class.normalizing_semiring_rules(11) minus_mult_left
          set_plus_mono_b)

lemma bigo_minus3: "O(-f) = O(f)"
by (metis bigo_elt_subset bigo_minus bigo_refl equalityI minus_minus)

lemma bigo_plus_absorb_lemma1: "f : O(g) \<Longrightarrow> f +o O(g) \<le> O(g)"
by (metis bigo_plus_idemp set_plus_mono3)

lemma bigo_plus_absorb_lemma2: "f : O(g) \<Longrightarrow> O(g) \<le> f +o O(g)"
by (metis (no_types) bigo_minus bigo_plus_absorb_lemma1 right_minus
          set_plus_mono_b set_plus_rearrange2 set_zero_plus subsetI)

lemma bigo_plus_absorb [simp]: "f : O(g) \<Longrightarrow> f +o O(g) = O(g)"
by (metis bigo_plus_absorb_lemma1 bigo_plus_absorb_lemma2 order_eq_iff)

lemma bigo_plus_absorb2 [intro]: "f : O(g) \<Longrightarrow> A <= O(g) \<Longrightarrow> f +o A \<le> O(g)"
by (metis bigo_plus_absorb set_plus_mono)

lemma bigo_add_commute_imp: "f : g +o O(h) \<Longrightarrow> g : f +o O(h)"
by (metis bigo_minus minus_diff_eq set_plus_imp_minus set_minus_plus)

lemma bigo_add_commute: "(f : g +o O(h)) = (g : f +o O(h))"
by (metis bigo_add_commute_imp)

lemma bigo_const1: "(\<lambda>x. c) : O(\<lambda>x. 1)"
by (auto simp add: bigo_def mult_ac)

lemma bigo_const2 [intro]: "O(\<lambda>x. c) \<le> O(\<lambda>x. 1)"
by (metis bigo_const1 bigo_elt_subset)

lemma bigo_const3: "(c\<Colon>'a\<Colon>{linordered_field,number_ring}) ~= 0 \<Longrightarrow> (\<lambda>x. 1) : O(\<lambda>x. c)"
apply (simp add: bigo_def)
by (metis abs_eq_0 left_inverse order_refl)

lemma bigo_const4: "(c\<Colon>'a\<Colon>{linordered_field,number_ring}) ~= 0 \<Longrightarrow> O(\<lambda>x. 1) <= O(\<lambda>x. c)"
by (metis bigo_elt_subset bigo_const3)

lemma bigo_const [simp]: "(c\<Colon>'a\<Colon>{linordered_field,number_ring}) ~= 0 \<Longrightarrow>
    O(\<lambda>x. c) = O(\<lambda>x. 1)"
by (metis bigo_const2 bigo_const4 equalityI)

lemma bigo_const_mult1: "(\<lambda>x. c * f x) : O(f)"
apply (simp add: bigo_def abs_mult)
by (metis le_less)

lemma bigo_const_mult2: "O(\<lambda>x. c * f x) \<le> O(f)"
by (rule bigo_elt_subset, rule bigo_const_mult1)

lemma bigo_const_mult3: "(c\<Colon>'a\<Colon>{linordered_field,number_ring}) ~= 0 \<Longrightarrow> f : O(\<lambda>x. c * f x)"
apply (simp add: bigo_def)
by (metis (no_types) abs_mult mult_assoc mult_1 order_refl left_inverse)

lemma bigo_const_mult4:
"(c\<Colon>'a\<Colon>{linordered_field,number_ring}) \<noteq> 0 \<Longrightarrow> O(f) \<le> O(\<lambda>x. c * f x)"
by (metis bigo_elt_subset bigo_const_mult3)

lemma bigo_const_mult [simp]: "(c\<Colon>'a\<Colon>{linordered_field,number_ring}) ~= 0 \<Longrightarrow>
    O(\<lambda>x. c * f x) = O(f)"
by (metis equalityI bigo_const_mult2 bigo_const_mult4)

lemma bigo_const_mult5 [simp]: "(c\<Colon>'a\<Colon>{linordered_field,number_ring}) ~= 0 \<Longrightarrow>
    (\<lambda>x. c) *o O(f) = O(f)"
  apply (auto del: subsetI)
  apply (rule order_trans)
  apply (rule bigo_mult2)
  apply (simp add: func_times)
  apply (auto intro!: subsetI simp add: bigo_def elt_set_times_def func_times)
  apply (rule_tac x = "\<lambda>y. inverse c * x y" in exI)
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

lemma bigo_const_mult6 [intro]: "(\<lambda>x. c) *o O(f) <= O(f)"
  apply (auto intro!: subsetI
    simp add: bigo_def elt_set_times_def func_times
    simp del: abs_mult mult_ac)
(* sledgehammer *)
  apply (rule_tac x = "ca * (abs c)" in exI)
  apply (rule allI)
  apply (subgoal_tac "ca * abs(c) * abs(f x) = abs(c) * (ca * abs(f x))")
  apply (erule ssubst)
  apply (subst abs_mult)
  apply (rule mult_left_mono)
  apply (erule spec)
  apply simp
  apply (simp add: mult_ac)
done

lemma bigo_const_mult7 [intro]: "f =o O(g) \<Longrightarrow> (\<lambda>x. c * f x) =o O(g)"
by (metis bigo_const_mult1 bigo_elt_subset order_less_le psubsetD)

lemma bigo_compose1: "f =o O(g) \<Longrightarrow> (\<lambda>x. f(k x)) =o O(\<lambda>x. g(k x))"
by (unfold bigo_def, auto)

lemma bigo_compose2:
"f =o g +o O(h) \<Longrightarrow> (\<lambda>x. f(k x)) =o (\<lambda>x. g(k x)) +o O(\<lambda>x. h(k x))"
apply (simp only: set_minus_plus [symmetric] diff_minus fun_Compl_def func_plus)
by (erule bigo_compose1)

subsection {* Setsum *}

lemma bigo_setsum_main: "\<forall>x. \<forall>y \<in> A x. 0 <= h x y \<Longrightarrow>
    \<exists>c. \<forall>x. \<forall>y \<in> A x. abs (f x y) <= c * (h x y) \<Longrightarrow>
      (\<lambda>x. SUM y : A x. f x y) =o O(\<lambda>x. SUM y : A x. h x y)"
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
by (metis abs_ge_self abs_mult_pos order_trans)

lemma bigo_setsum1: "\<forall>x y. 0 <= h x y \<Longrightarrow>
    \<exists>c. \<forall>x y. abs (f x y) <= c * (h x y) \<Longrightarrow>
      (\<lambda>x. SUM y : A x. f x y) =o O(\<lambda>x. SUM y : A x. h x y)"
by (metis (no_types) bigo_setsum_main)

lemma bigo_setsum2: "\<forall>y. 0 <= h y \<Longrightarrow>
    \<exists>c. \<forall>y. abs (f y) <= c * (h y) \<Longrightarrow>
      (\<lambda>x. SUM y : A x. f y) =o O(\<lambda>x. SUM y : A x. h y)"
apply (rule bigo_setsum1)
by metis+

lemma bigo_setsum3: "f =o O(h) \<Longrightarrow>
    (\<lambda>x. SUM y : A x. (l x y) * f(k x y)) =o
      O(\<lambda>x. SUM y : A x. abs(l x y * h(k x y)))"
apply (rule bigo_setsum1)
 apply (rule allI)+
 apply (rule abs_ge_zero)
apply (unfold bigo_def)
apply (auto simp add: abs_mult)
by (metis abs_ge_zero mult_left_commute mult_left_mono)

lemma bigo_setsum4: "f =o g +o O(h) \<Longrightarrow>
    (\<lambda>x. SUM y : A x. l x y * f(k x y)) =o
      (\<lambda>x. SUM y : A x. l x y * g(k x y)) +o
        O(\<lambda>x. SUM y : A x. abs(l x y * h(k x y)))"
apply (rule set_minus_imp_plus)
apply (subst fun_diff_def)
apply (subst setsum_subtractf [symmetric])
apply (subst right_diff_distrib [symmetric])
apply (rule bigo_setsum3)
by (metis (lifting, no_types) fun_diff_def set_plus_imp_minus ext)

lemma bigo_setsum5: "f =o O(h) \<Longrightarrow> \<forall>x y. 0 <= l x y \<Longrightarrow>
    \<forall>x. 0 <= h x \<Longrightarrow>
      (\<lambda>x. SUM y : A x. (l x y) * f(k x y)) =o
        O(\<lambda>x. SUM y : A x. (l x y) * h(k x y))"
apply (subgoal_tac "(\<lambda>x. SUM y : A x. (l x y) * h(k x y)) =
      (\<lambda>x. SUM y : A x. abs((l x y) * h(k x y)))")
 apply (erule ssubst)
 apply (erule bigo_setsum3)
apply (rule ext)
apply (rule setsum_cong2)
by (metis abs_of_nonneg zero_le_mult_iff)

lemma bigo_setsum6: "f =o g +o O(h) \<Longrightarrow> \<forall>x y. 0 <= l x y \<Longrightarrow>
    \<forall>x. 0 <= h x \<Longrightarrow>
      (\<lambda>x. SUM y : A x. (l x y) * f(k x y)) =o
        (\<lambda>x. SUM y : A x. (l x y) * g(k x y)) +o
          O(\<lambda>x. SUM y : A x. (l x y) * h(k x y))"
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

lemma bigo_useful_intro: "A <= O(f) \<Longrightarrow> B <= O(f) \<Longrightarrow>
  A \<oplus> B <= O(f)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_mono2)
  apply assumption+
done

lemma bigo_useful_add: "f =o O(h) \<Longrightarrow> g =o O(h) \<Longrightarrow> f + g =o O(h)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_intro)
  apply assumption+
done

lemma bigo_useful_const_mult: "(c\<Colon>'a\<Colon>{linordered_field,number_ring}) ~= 0 \<Longrightarrow>
    (\<lambda>x. c) * f =o O(h) \<Longrightarrow> f =o O(h)"
  apply (rule subsetD)
  apply (subgoal_tac "(\<lambda>x. 1 / c) *o O(h) <= O(h)")
  apply assumption
  apply (rule bigo_const_mult6)
  apply (subgoal_tac "f = (\<lambda>x. 1 / c) * ((\<lambda>x. c) * f)")
  apply (erule ssubst)
  apply (erule set_times_intro2)
  apply (simp add: func_times)
done

lemma bigo_fix: "(\<lambda>x. f ((x\<Colon>nat) + 1)) =o O(\<lambda>x. h(x + 1)) \<Longrightarrow> f 0 = 0 \<Longrightarrow>
    f =o O(h)"
apply (simp add: bigo_alt_def)
by (metis abs_ge_zero abs_mult abs_of_pos abs_zero not0_implies_Suc)

lemma bigo_fix2:
    "(\<lambda>x. f ((x\<Colon>nat) + 1)) =o (\<lambda>x. g(x + 1)) +o O(\<lambda>x. h(x + 1)) \<Longrightarrow>
       f 0 = g 0 \<Longrightarrow> f =o g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_fix)
  apply (subst fun_diff_def)
  apply (subst fun_diff_def [symmetric])
  apply (rule set_plus_imp_minus)
  apply simp
  apply (simp add: fun_diff_def)
done

subsection {* Less than or equal to *}

definition lesso :: "('a => 'b\<Colon>linordered_idom) => ('a => 'b) => ('a => 'b)" (infixl "<o" 70) where
  "f <o g == (\<lambda>x. max (f x - g x) 0)"

lemma bigo_lesseq1: "f =o O(h) \<Longrightarrow> \<forall>x. abs (g x) <= abs (f x) \<Longrightarrow>
    g =o O(h)"
  apply (unfold bigo_def)
  apply clarsimp
apply (blast intro: order_trans)
done

lemma bigo_lesseq2: "f =o O(h) \<Longrightarrow> \<forall>x. abs (g x) <= f x \<Longrightarrow>
      g =o O(h)"
  apply (erule bigo_lesseq1)
apply (blast intro: abs_ge_self order_trans)
done

lemma bigo_lesseq3: "f =o O(h) \<Longrightarrow> \<forall>x. 0 <= g x \<Longrightarrow> \<forall>x. g x <= f x \<Longrightarrow>
      g =o O(h)"
  apply (erule bigo_lesseq2)
  apply (rule allI)
  apply (subst abs_of_nonneg)
  apply (erule spec)+
done

lemma bigo_lesseq4: "f =o O(h) \<Longrightarrow>
    \<forall>x. 0 <= g x \<Longrightarrow> \<forall>x. g x <= abs (f x) \<Longrightarrow>
      g =o O(h)"
  apply (erule bigo_lesseq1)
  apply (rule allI)
  apply (subst abs_of_nonneg)
  apply (erule spec)+
done

lemma bigo_lesso1: "\<forall>x. f x <= g x \<Longrightarrow> f <o g =o O(h)"
apply (unfold lesso_def)
apply (subgoal_tac "(\<lambda>x. max (f x - g x) 0) = 0")
 apply (metis bigo_zero)
by (metis (lifting, no_types) func_zero le_fun_def le_iff_diff_le_0
      min_max.sup_absorb2 order_eq_iff)

lemma bigo_lesso2: "f =o g +o O(h) \<Longrightarrow>
    \<forall>x. 0 <= k x \<Longrightarrow> \<forall>x. k x <= f x \<Longrightarrow>
      k <o g =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst fun_diff_def)
apply (erule thin_rl)
(* sledgehammer *)
apply (case_tac "0 <= k x - g x")
 apply (metis (hide_lams, no_types) abs_le_iff add_le_imp_le_right diff_minus le_less
          le_max_iff_disj min_max.le_supE min_max.sup_absorb2
          min_max.sup_commute)
by (metis abs_ge_zero le_cases min_max.sup_absorb2)

lemma bigo_lesso3: "f =o g +o O(h) \<Longrightarrow>
    \<forall>x. 0 <= k x \<Longrightarrow> \<forall>x. g x <= k x \<Longrightarrow>
      f <o k =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst fun_diff_def)
  apply (erule thin_rl)
  (* sledgehammer *)
  apply (case_tac "0 <= f x - k x")
  apply simp
  apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
  apply (metis diff_less_0_iff_less linorder_not_le not_leE xt1(12) xt1(6))
 apply (metis add_minus_cancel diff_le_eq le_diff_eq uminus_add_conv_diff)
apply (metis abs_ge_zero linorder_linear min_max.sup_absorb1 min_max.sup_commute)
done

lemma bigo_lesso4:
  "f <o g =o O(k\<Colon>'a=>'b\<Colon>{linordered_field,number_ring}) \<Longrightarrow>
   g =o h +o O(k) \<Longrightarrow> f <o h =o O(k)"
apply (unfold lesso_def)
apply (drule set_plus_imp_minus)
apply (drule bigo_abs5) back
apply (simp add: fun_diff_def)
apply (drule bigo_useful_add, assumption)
apply (erule bigo_lesseq2) back
apply (rule allI)
by (auto simp add: func_plus fun_diff_def algebra_simps
    split: split_max abs_split)

lemma bigo_lesso5: "f <o g =o O(h) \<Longrightarrow> \<exists>C. \<forall>x. f x <= g x + C * abs (h x)"
apply (simp only: lesso_def bigo_alt_def)
apply clarsimp
by (metis abs_if abs_mult add_commute diff_le_eq less_not_permute)

end
