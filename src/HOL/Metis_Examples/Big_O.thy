(*  Title:      HOL/Metis_Examples/Big_O.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring the Big O notation.
*)

section \<open>Metis Example Featuring the Big O Notation\<close>

theory Big_O
imports
  "HOL-Decision_Procs.Dense_Linear_Order"
  "HOL-Library.Function_Algebras"
  "HOL-Library.Set_Algebras"
begin

subsection \<open>Definitions\<close>

definition bigo :: "('a => 'b::linordered_idom) => ('a => 'b) set" (\<open>(1O'(_'))\<close>) where
  "O(f::('a => 'b)) == {h. \<exists>c. \<forall>x. \<bar>h x\<bar> <= c * \<bar>f x\<bar>}"

lemma bigo_pos_const:
  "(\<exists>c::'a::linordered_idom.
    \<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>)
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>))"
  by (metis (no_types) abs_ge_zero
      algebra_simps mult.comm_neutral
      mult_nonpos_nonneg not_le_imp_less order_trans zero_less_one)

(*** Now various verions with an increasing shrink factor ***)

sledgehammer_params [isar_proofs, compress = 1]

lemma
  "(\<exists>c::'a::linordered_idom.
    \<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>)
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "\<bar>c\<bar>" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have F1: "\<forall>x\<^sub>1::'a::linordered_idom. 0 \<le> \<bar>x\<^sub>1\<bar>" by (metis abs_ge_zero)
  have F2: "\<forall>x\<^sub>1::'a::linordered_idom. 1 * x\<^sub>1 = x\<^sub>1" by (metis mult_1)
  have F3: "\<forall>x\<^sub>1 x\<^sub>3. x\<^sub>3 \<le> \<bar>h x\<^sub>1\<bar> \<longrightarrow> x\<^sub>3 \<le> c * \<bar>f x\<^sub>1\<bar>" by (metis A1 order_trans)
  have F4: "\<forall>x\<^sub>2 x\<^sub>3::'a::linordered_idom. \<bar>x\<^sub>3\<bar> * \<bar>x\<^sub>2\<bar> = \<bar>x\<^sub>3 * x\<^sub>2\<bar>" by (metis abs_mult)
  have F5: "\<forall>x\<^sub>3 x\<^sub>1::'a::linordered_idom. 0 \<le> x\<^sub>1 \<longrightarrow> \<bar>x\<^sub>3 * x\<^sub>1\<bar> = \<bar>x\<^sub>3\<bar> * x\<^sub>1" by (metis abs_mult_pos)
  hence "\<forall>x\<^sub>1\<ge>0. \<bar>x\<^sub>1::'a::linordered_idom\<bar> = \<bar>1\<bar> * x\<^sub>1" by (metis F2)
  hence "\<forall>x\<^sub>1\<ge>0. \<bar>x\<^sub>1::'a::linordered_idom\<bar> = x\<^sub>1" by (metis F2 abs_one)
  hence "\<forall>x\<^sub>3. 0 \<le> \<bar>h x\<^sub>3\<bar> \<longrightarrow> \<bar>c * \<bar>f x\<^sub>3\<bar>\<bar> = c * \<bar>f x\<^sub>3\<bar>" by (metis F3)
  hence "\<forall>x\<^sub>3. \<bar>c * \<bar>f x\<^sub>3\<bar>\<bar> = c * \<bar>f x\<^sub>3\<bar>" by (metis F1)
  hence "\<forall>x\<^sub>3. (0::'a) \<le> \<bar>f x\<^sub>3\<bar> \<longrightarrow> c * \<bar>f x\<^sub>3\<bar> = \<bar>c\<bar> * \<bar>f x\<^sub>3\<bar>" by (metis F5)
  hence "\<forall>x\<^sub>3. (0::'a) \<le> \<bar>f x\<^sub>3\<bar> \<longrightarrow> c * \<bar>f x\<^sub>3\<bar> = \<bar>c * f x\<^sub>3\<bar>" by (metis F4)
  hence "\<forall>x\<^sub>3. c * \<bar>f x\<^sub>3\<bar> = \<bar>c * f x\<^sub>3\<bar>" by (metis F1)
  hence "\<bar>h x\<bar> \<le> \<bar>c * f x\<bar>" by (metis A1)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis F4)
qed

sledgehammer_params [isar_proofs, compress = 2]

lemma
  "(\<exists>c::'a::linordered_idom.
    \<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>)
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "\<bar>c\<bar>" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have F1: "\<forall>x\<^sub>1::'a::linordered_idom. 1 * x\<^sub>1 = x\<^sub>1" by (metis mult_1)
  have F2: "\<forall>x\<^sub>2 x\<^sub>3::'a::linordered_idom. \<bar>x\<^sub>3\<bar> * \<bar>x\<^sub>2\<bar> = \<bar>x\<^sub>3 * x\<^sub>2\<bar>"
    by (metis abs_mult)
  have "\<forall>x\<^sub>1\<ge>0. \<bar>x\<^sub>1::'a::linordered_idom\<bar> = x\<^sub>1" by (metis F1 abs_mult_pos abs_one)
  hence "\<forall>x\<^sub>3. \<bar>c * \<bar>f x\<^sub>3\<bar>\<bar> = c * \<bar>f x\<^sub>3\<bar>" by (metis A1 abs_ge_zero order_trans)
  hence "\<forall>x\<^sub>3. 0 \<le> \<bar>f x\<^sub>3\<bar> \<longrightarrow> c * \<bar>f x\<^sub>3\<bar> = \<bar>c * f x\<^sub>3\<bar>" by (metis F2 abs_mult_pos)
  hence "\<bar>h x\<bar> \<le> \<bar>c * f x\<bar>" by (metis A1 abs_ge_zero)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis F2)
qed

sledgehammer_params [isar_proofs, compress = 3]

lemma
  "(\<exists>c::'a::linordered_idom.
    \<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>)
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "\<bar>c\<bar>" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have F1: "\<forall>x\<^sub>1::'a::linordered_idom. 1 * x\<^sub>1 = x\<^sub>1" by (metis mult_1)
  have F2: "\<forall>x\<^sub>3 x\<^sub>1::'a::linordered_idom. 0 \<le> x\<^sub>1 \<longrightarrow> \<bar>x\<^sub>3 * x\<^sub>1\<bar> = \<bar>x\<^sub>3\<bar> * x\<^sub>1" by (metis abs_mult_pos)
  hence "\<forall>x\<^sub>1\<ge>0. \<bar>x\<^sub>1::'a::linordered_idom\<bar> = x\<^sub>1" by (metis F1 abs_one)
  hence "\<forall>x\<^sub>3. 0 \<le> \<bar>f x\<^sub>3\<bar> \<longrightarrow> c * \<bar>f x\<^sub>3\<bar> = \<bar>c\<bar> * \<bar>f x\<^sub>3\<bar>" by (metis F2 A1 abs_ge_zero order_trans)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis A1 abs_ge_zero)
qed

sledgehammer_params [isar_proofs, compress = 4]

lemma
  "(\<exists>c::'a::linordered_idom.
    \<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>)
    \<longleftrightarrow> (\<exists>c. 0 < c \<and> (\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>))"
  apply auto
  apply (case_tac "c = 0", simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (rule_tac x = "\<bar>c\<bar>" in exI, auto)
proof -
  fix c :: 'a and x :: 'b
  assume A1: "\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>"
  have "\<forall>x\<^sub>1::'a::linordered_idom. 1 * x\<^sub>1 = x\<^sub>1" by (metis mult_1)
  hence "\<forall>x\<^sub>3. \<bar>c * \<bar>f x\<^sub>3\<bar>\<bar> = c * \<bar>f x\<^sub>3\<bar>"
    by (metis A1 abs_ge_zero order_trans abs_mult_pos abs_one)
  hence "\<bar>h x\<bar> \<le> \<bar>c * f x\<bar>" by (metis A1 abs_ge_zero abs_mult_pos abs_mult)
  thus "\<bar>h x\<bar> \<le> \<bar>c\<bar> * \<bar>f x\<bar>" by (metis abs_mult)
qed

sledgehammer_params [isar_proofs, compress = 1]

lemma bigo_alt_def: "O(f) = {h. \<exists>c. (0 < c \<and> (\<forall>x. \<bar>h x\<bar> <= c * \<bar>f x\<bar>))}"
by (auto simp add: bigo_def bigo_pos_const)

lemma bigo_elt_subset [intro]: "f \<in> O(g) \<Longrightarrow> O(f) \<le> O(g)"
apply (auto simp add: bigo_alt_def)
apply (rule_tac x = "ca * c" in exI)
apply (metis algebra_simps mult_le_cancel_left_pos order_trans mult_pos_pos)
done

lemma bigo_refl [intro]: "f \<in> O(f)"
unfolding bigo_def mem_Collect_eq
by (metis mult_1 order_refl)

lemma bigo_zero: "0 \<in> O(g)"
apply (auto simp add: bigo_def func_zero)
by (metis mult_zero_left order_refl)

lemma bigo_zero2: "O(\<lambda>x. 0) = {\<lambda>x. 0}"
by (auto simp add: bigo_def)

lemma bigo_plus_self_subset [intro]:
  "O(f) + O(f) <= O(f)"
apply (auto simp add: bigo_alt_def set_plus_def)
apply (rule_tac x = "c + ca" in exI)
apply auto
apply (simp add: ring_distribs func_plus)
by (metis order_trans abs_triangle_ineq add_mono)

lemma bigo_plus_idemp [simp]: "O(f) + O(f) = O(f)"
by (metis bigo_plus_self_subset bigo_zero set_eq_subset set_zero_plus2)

lemma bigo_plus_subset [intro]: "O(f + g) <= O(f) + O(g)"
apply (rule subsetI)
apply (auto simp add: bigo_def bigo_pos_const func_plus set_plus_def)
apply (subst bigo_pos_const [symmetric])+
apply (rule_tac x = "\<lambda>n. if \<bar>g n\<bar> <= \<bar>f n\<bar> then x n else 0" in exI)
apply (rule conjI)
 apply (rule_tac x = "c + c" in exI)
 apply clarsimp
 apply (subgoal_tac "c * \<bar>f xa + g xa\<bar> <= (c + c) * \<bar>f xa\<bar>")
  apply (metis mult_2 order_trans)
 apply (subgoal_tac "c * \<bar>f xa + g xa\<bar> <= c * (\<bar>f xa\<bar> + \<bar>g xa\<bar>)")
  apply (erule order_trans)
  apply (simp add: ring_distribs)
 apply (rule mult_left_mono)
  apply (simp add: abs_triangle_ineq)
 apply (simp add: order_less_le)
apply (rule_tac x = "\<lambda>n. if \<bar>f n\<bar> < \<bar>g n\<bar> then x n else 0" in exI)
apply (rule conjI)
 apply (rule_tac x = "c + c" in exI)
 apply auto
apply (subgoal_tac "c * \<bar>f xa + g xa\<bar> <= (c + c) * \<bar>g xa\<bar>")
 apply (metis order_trans mult_2)
apply (subgoal_tac "c * \<bar>f xa + g xa\<bar> <= c * (\<bar>f xa\<bar> + \<bar>g xa\<bar>)")
 apply (erule order_trans)
 apply (simp add: ring_distribs)
by (metis abs_triangle_ineq mult_le_cancel_left_pos)

lemma bigo_plus_subset2 [intro]: "A <= O(f) \<Longrightarrow> B <= O(f) \<Longrightarrow> A + B <= O(f)"
by (metis bigo_plus_idemp set_plus_mono2)

lemma bigo_plus_eq: "\<forall>x. 0 <= f x \<Longrightarrow> \<forall>x. 0 <= g x \<Longrightarrow> O(f + g) = O(f) + O(g)"
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
 apply (subgoal_tac "\<bar>a xa + b xa\<bar> <= \<bar>a xa\<bar> + \<bar>b xa\<bar>")
  apply (subgoal_tac "\<bar>a xa\<bar> + \<bar>b xa\<bar> <= max c ca * f xa + max c ca * g xa")
   apply (metis order_trans)
  defer 1
  apply (metis abs_triangle_ineq)
 apply (metis add_nonneg_nonneg)
apply (rule add_mono)
 apply (metis max.cobounded2 linorder_linear max.absorb1 mult_right_mono xt1(6))
by (metis max.cobounded2 linorder_not_le mult_le_cancel_right order_trans)

lemma bigo_bounded_alt: "\<forall>x. 0 \<le> f x \<Longrightarrow> \<forall>x. f x \<le> c * g x \<Longrightarrow> f \<in> O(g)"
apply (auto simp add: bigo_def)
(* Version 1: one-line proof *)
by (metis abs_le_D1 linorder_class.not_less order_less_le Orderings.xt1(12) abs_mult)

lemma "\<forall>x. 0 \<le> f x \<Longrightarrow> \<forall>x. f x \<le> c * g x \<Longrightarrow> f \<in> O(g)"
apply (auto simp add: bigo_def)
(* Version 2: structured proof *)
proof -
  assume "\<forall>x. f x \<le> c * g x"
  thus "\<exists>c. \<forall>x. f x \<le> c * \<bar>g x\<bar>" by (metis abs_mult abs_ge_self order_trans)
qed

lemma bigo_bounded: "\<forall>x. 0 \<le> f x \<Longrightarrow> \<forall>x. f x \<le> g x \<Longrightarrow> f \<in> O(g)"
apply (erule bigo_bounded_alt [of f 1 g])
by (metis mult_1)

lemma bigo_bounded2: "\<forall>x. lb x \<le> f x \<Longrightarrow> \<forall>x. f x \<le> lb x + g x \<Longrightarrow> f \<in> lb +o O(g)"
apply (rule set_minus_imp_plus)
apply (rule bigo_bounded)
 apply (metis add_le_cancel_left diff_add_cancel diff_self minus_apply
              algebra_simps)
by (metis add_le_cancel_left diff_add_cancel func_plus le_fun_def
          algebra_simps)

lemma bigo_abs: "(\<lambda>x. \<bar>f x\<bar>) =o O(f)"
apply (unfold bigo_def)
apply auto
by (metis mult_1 order_refl)

lemma bigo_abs2: "f =o O(\<lambda>x. \<bar>f x\<bar>)"
apply (unfold bigo_def)
apply auto
by (metis mult_1 order_refl)

lemma bigo_abs3: "O(f) = O(\<lambda>x. \<bar>f x\<bar>)"
proof -
  have F1: "\<forall>v u. u \<in> O(v) \<longrightarrow> O(u) \<subseteq> O(v)" by (metis bigo_elt_subset)
  have F2: "\<forall>u. (\<lambda>R. \<bar>u R\<bar>) \<in> O(u)" by (metis bigo_abs)
  have "\<forall>u. u \<in> O(\<lambda>R. \<bar>u R\<bar>)" by (metis bigo_abs2)
  thus "O(f) = O(\<lambda>x. \<bar>f x\<bar>)" using F1 F2 by auto
qed

lemma bigo_abs4: "f =o g +o O(h) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) =o (\<lambda>x. \<bar>g x\<bar>) +o O(h)"
  apply (drule set_plus_imp_minus)
  apply (rule set_minus_imp_plus)
  apply (subst fun_diff_def)
proof -
  assume a: "f - g \<in> O(h)"
  have "(\<lambda>x. \<bar>f x\<bar> - \<bar>g x\<bar>) =o O(\<lambda>x. \<bar>\<bar>f x\<bar> - \<bar>g x\<bar>\<bar>)"
    by (rule bigo_abs2)
  also have "\<dots> <= O(\<lambda>x. \<bar>f x - g x\<bar>)"
    apply (rule bigo_elt_subset)
    apply (rule bigo_bounded)
     apply (metis abs_ge_zero)
    by (metis abs_triangle_ineq3)
  also have "\<dots> <= O(f - g)"
    apply (rule bigo_elt_subset)
    apply (subst fun_diff_def)
    apply (rule bigo_abs)
    done
  also have "\<dots> <= O(h)"
    using a by (rule bigo_elt_subset)
  finally show "(\<lambda>x. \<bar>f x\<bar> - \<bar>g x\<bar>) \<in> O(h)" .
qed

lemma bigo_abs5: "f =o O(g) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) =o O(g)"
by (unfold bigo_def, auto)

lemma bigo_elt_subset2 [intro]: "f \<in> g +o O(h) \<Longrightarrow> O(f) \<le> O(g) + O(h)"
proof -
  assume "f \<in> g +o O(h)"
  also have "\<dots> \<le> O(g) + O(h)"
    by (auto del: subsetI)
  also have "\<dots> = O(\<lambda>x. \<bar>g x\<bar>) + O(\<lambda>x. \<bar>h x\<bar>)"
    by (metis bigo_abs3)
  also have "... = O((\<lambda>x. \<bar>g x\<bar>) + (\<lambda>x. \<bar>h x\<bar>))"
    by (rule bigo_plus_eq [symmetric], auto)
  finally have "f \<in> \<dots>".
  then have "O(f) \<le> \<dots>"
    by (elim bigo_elt_subset)
  also have "\<dots> = O(\<lambda>x. \<bar>g x\<bar>) + O(\<lambda>x. \<bar>h x\<bar>)"
    by (rule bigo_plus_eq, auto)
  finally show ?thesis
    by (simp add: bigo_abs3 [symmetric])
qed

lemma bigo_mult [intro]: "O(f) * O(g) <= O(f * g)"
apply (rule subsetI)
apply (subst bigo_def)
apply (auto simp del: abs_mult ac_simps
            simp add: bigo_alt_def set_times_def func_times)
(* sledgehammer *)
apply (rule_tac x = "c * ca" in exI)
apply (rule allI)
apply (erule_tac x = x in allE)+
apply (subgoal_tac "c * ca * \<bar>f x * g x\<bar> = (c * \<bar>f x\<bar>) * (ca * \<bar>g x\<bar>)")
 apply (metis (no_types) abs_ge_zero abs_mult mult_mono')
by (metis mult.assoc mult.left_commute abs_of_pos mult.left_commute abs_mult)

lemma bigo_mult2 [intro]: "f *o O(g) <= O(f * g)"
by (metis bigo_mult bigo_refl set_times_mono3 subset_trans)

lemma bigo_mult3: "f \<in> O(h) \<Longrightarrow> g \<in> O(j) \<Longrightarrow> f * g \<in> O(h * j)"
by (metis bigo_mult rev_subsetD set_times_intro)

lemma bigo_mult4 [intro]:"f \<in> k +o O(h) \<Longrightarrow> g * f \<in> (g * k) +o O(g * h)"
by (metis bigo_mult2 set_plus_mono_b set_times_intro2 set_times_plus_distrib)

lemma bigo_mult5: "\<forall>x. f x ~= 0 \<Longrightarrow>
    O(f * g) <= (f::'a => ('b::linordered_field)) *o O(g)"
proof -
  assume a: "\<forall>x. f x \<noteq> 0"
  show "O(f * g) <= f *o O(g)"
  proof
    fix h
    assume h: "h \<in> O(f * g)"
    then have "(\<lambda>x. 1 / (f x)) * h \<in> (\<lambda>x. 1 / f x) *o O(f * g)"
      by auto
    also have "... <= O((\<lambda>x. 1 / f x) * (f * g))"
      by (rule bigo_mult2)
    also have "(\<lambda>x. 1 / f x) * (f * g) = g"
      by (simp add: fun_eq_iff a)
    finally have "(\<lambda>x. (1::'b) / f x) * h \<in> O(g)".
    then have "f * ((\<lambda>x. (1::'b) / f x) * h) \<in> f *o O(g)"
      by auto
    also have "f * ((\<lambda>x. (1::'b) / f x) * h) = h"
      by (simp add: func_times fun_eq_iff a)
    finally show "h \<in> f *o O(g)".
  qed
qed

lemma bigo_mult6:
"\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) = (f::'a \<Rightarrow> ('b::linordered_field)) *o O(g)"
by (metis bigo_mult2 bigo_mult5 order_antisym)

(*proof requires relaxing relevance: 2007-01-25*)
declare bigo_mult6 [simp]

lemma bigo_mult7:
"\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) \<le> O(f::'a \<Rightarrow> ('b::linordered_field)) * O(g)"
by (metis bigo_refl bigo_mult6 set_times_mono3)

declare bigo_mult6 [simp del]
declare bigo_mult7 [intro!]

lemma bigo_mult8:
"\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) = O(f::'a \<Rightarrow> ('b::linordered_field)) * O(g)"
by (metis bigo_mult bigo_mult7 order_antisym_conv)

lemma bigo_minus [intro]: "f \<in> O(g) \<Longrightarrow> - f \<in> O(g)"
by (auto simp add: bigo_def fun_Compl_def)

lemma bigo_minus2: "f \<in> g +o O(h) \<Longrightarrow> -f \<in> -g +o O(h)"
by (metis (no_types, lifting) bigo_minus diff_minus_eq_add minus_add_distrib
    minus_minus set_minus_imp_plus set_plus_imp_minus)

lemma bigo_minus3: "O(-f) = O(f)"
by (metis bigo_elt_subset bigo_minus bigo_refl equalityI minus_minus)

lemma bigo_plus_absorb_lemma1: "f \<in> O(g) \<Longrightarrow> f +o O(g) \<le> O(g)"
by (metis bigo_plus_idemp set_plus_mono3)

lemma bigo_plus_absorb_lemma2: "f \<in> O(g) \<Longrightarrow> O(g) \<le> f +o O(g)"
by (metis (no_types) bigo_minus bigo_plus_absorb_lemma1 right_minus
          set_plus_mono set_plus_rearrange2 set_zero_plus subsetD subset_refl
          subset_trans)

lemma bigo_plus_absorb [simp]: "f \<in> O(g) \<Longrightarrow> f +o O(g) = O(g)"
by (metis bigo_plus_absorb_lemma1 bigo_plus_absorb_lemma2 order_eq_iff)

lemma bigo_plus_absorb2 [intro]: "f \<in> O(g) \<Longrightarrow> A \<subseteq> O(g) \<Longrightarrow> f +o A \<subseteq> O(g)"
by (metis bigo_plus_absorb set_plus_mono)

lemma bigo_add_commute_imp: "f \<in> g +o O(h) \<Longrightarrow> g \<in> f +o O(h)"
by (metis bigo_minus minus_diff_eq set_plus_imp_minus set_minus_plus)

lemma bigo_add_commute: "(f \<in> g +o O(h)) = (g \<in> f +o O(h))"
by (metis bigo_add_commute_imp)

lemma bigo_const1: "(\<lambda>x. c) \<in> O(\<lambda>x. 1)"
by (auto simp add: bigo_def ac_simps)

lemma bigo_const2 [intro]: "O(\<lambda>x. c) \<le> O(\<lambda>x. 1)"
by (metis bigo_const1 bigo_elt_subset)

lemma bigo_const3: "(c::'a::linordered_field) \<noteq> 0 \<Longrightarrow> (\<lambda>x. 1) \<in> O(\<lambda>x. c)"
apply (simp add: bigo_def)
by (metis abs_eq_0 left_inverse order_refl)

lemma bigo_const4: "(c::'a::linordered_field) \<noteq> 0 \<Longrightarrow> O(\<lambda>x. 1) \<subseteq> O(\<lambda>x. c)"
by (metis bigo_elt_subset bigo_const3)

lemma bigo_const [simp]: "(c::'a::linordered_field) ~= 0 \<Longrightarrow>
    O(\<lambda>x. c) = O(\<lambda>x. 1)"
by (metis bigo_const2 bigo_const4 equalityI)

lemma bigo_const_mult1: "(\<lambda>x. c * f x) \<in> O(f)"
apply (simp add: bigo_def abs_mult)
by (metis le_less)

lemma bigo_const_mult2: "O(\<lambda>x. c * f x) \<le> O(f)"
by (rule bigo_elt_subset, rule bigo_const_mult1)

lemma bigo_const_mult3: "(c::'a::linordered_field) \<noteq> 0 \<Longrightarrow> f \<in> O(\<lambda>x. c * f x)"
apply (simp add: bigo_def)
by (metis (no_types) abs_mult mult.assoc mult_1 order_refl left_inverse)

lemma bigo_const_mult4:
"(c::'a::linordered_field) \<noteq> 0 \<Longrightarrow> O(f) \<le> O(\<lambda>x. c * f x)"
by (metis bigo_elt_subset bigo_const_mult3)

lemma bigo_const_mult [simp]: "(c::'a::linordered_field) \<noteq> 0 \<Longrightarrow>
    O(\<lambda>x. c * f x) = O(f)"
by (metis equalityI bigo_const_mult2 bigo_const_mult4)

lemma bigo_const_mult5 [simp]: "(c::'a::linordered_field) \<noteq> 0 \<Longrightarrow>
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
  apply (simp add: mult.assoc [symmetric] abs_mult)
  (* couldn't get this proof without the step above *)
proof -
  fix g :: "'b \<Rightarrow> 'a" and d :: 'a
  assume A1: "c \<noteq> (0::'a)"
  assume A2: "\<forall>x::'b. \<bar>g x\<bar> \<le> d * \<bar>f x\<bar>"
  have F1: "inverse \<bar>c\<bar> = \<bar>inverse c\<bar>" using A1 by (metis nonzero_abs_inverse)
  have F2: "(0::'a) < \<bar>c\<bar>" using A1 by (metis zero_less_abs_iff)
  have "(0::'a) < \<bar>c\<bar> \<longrightarrow> (0::'a) < \<bar>inverse c\<bar>" using F1 by (metis positive_imp_inverse_positive)
  hence "(0::'a) < \<bar>inverse c\<bar>" using F2 by metis
  hence F3: "(0::'a) \<le> \<bar>inverse c\<bar>" by (metis order_le_less)
  have "\<exists>(u::'a) SKF\<^sub>7::'a \<Rightarrow> 'b. \<bar>g (SKF\<^sub>7 (\<bar>inverse c\<bar> * u))\<bar> \<le> u * \<bar>f (SKF\<^sub>7 (\<bar>inverse c\<bar> * u))\<bar>"
    using A2 by metis
  hence F4: "\<exists>(u::'a) SKF\<^sub>7::'a \<Rightarrow> 'b. \<bar>g (SKF\<^sub>7 (\<bar>inverse c\<bar> * u))\<bar> \<le> u * \<bar>f (SKF\<^sub>7 (\<bar>inverse c\<bar> * u))\<bar> \<and> (0::'a) \<le> \<bar>inverse c\<bar>"
    using F3 by metis
  hence "\<exists>(v::'a) (u::'a) SKF\<^sub>7::'a \<Rightarrow> 'b. \<bar>inverse c\<bar> * \<bar>g (SKF\<^sub>7 (u * v))\<bar> \<le> u * (v * \<bar>f (SKF\<^sub>7 (u * v))\<bar>)"
    by (metis mult_left_mono)
  then show "\<exists>ca::'a. \<forall>x::'b. inverse \<bar>c\<bar> * \<bar>g x\<bar> \<le> ca * \<bar>f x\<bar>"
    using A2 F4 by (metis F1 \<open>0 < \<bar>inverse c\<bar>\<close> mult.assoc mult_le_cancel_left_pos)
qed

lemma bigo_const_mult6 [intro]: "(\<lambda>x. c) *o O(f) <= O(f)"
  apply (auto intro!: subsetI
    simp add: bigo_def elt_set_times_def func_times
    simp del: abs_mult ac_simps)
(* sledgehammer *)
  apply (rule_tac x = "ca * \<bar>c\<bar>" in exI)
  apply (rule allI)
  apply (subgoal_tac "ca * \<bar>c\<bar> * \<bar>f x\<bar> = \<bar>c\<bar> * (ca * \<bar>f x\<bar>)")
  apply (erule ssubst)
  apply (subst abs_mult)
  apply (rule mult_left_mono)
  apply (erule spec)
  apply simp
  apply (simp add: ac_simps)
done

lemma bigo_const_mult7 [intro]: "f =o O(g) \<Longrightarrow> (\<lambda>x. c * f x) =o O(g)"
by (metis bigo_const_mult1 bigo_elt_subset order_less_le psubsetD)

lemma bigo_compose1: "f =o O(g) \<Longrightarrow> (\<lambda>x. f(k x)) =o O(\<lambda>x. g(k x))"
by (unfold bigo_def, auto)

lemma bigo_compose2:
"f =o g +o O(h) \<Longrightarrow> (\<lambda>x. f(k x)) =o (\<lambda>x. g(k x)) +o O(\<lambda>x. h(k x))"
apply (simp only: set_minus_plus [symmetric] fun_Compl_def func_plus)
apply (drule bigo_compose1 [of "f - g" h k])
apply (simp add: fun_diff_def)
done

subsection \<open>Sum\<close>

lemma bigo_sum_main: "\<forall>x. \<forall>y \<in> A x. 0 \<le> h x y \<Longrightarrow>
    \<exists>c. \<forall>x. \<forall>y \<in> A x. \<bar>f x y\<bar> <= c * (h x y) \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. f x y) =o O(\<lambda>x. \<Sum>y \<in> A x. h x y)"
apply (auto simp add: bigo_def)
apply (rule_tac x = "\<bar>c\<bar>" in exI)
apply (subst abs_of_nonneg) back back
 apply (rule sum_nonneg)
 apply force
apply (subst sum_distrib_left)
apply (rule allI)
apply (rule order_trans)
 apply (rule sum_abs)
apply (rule sum_mono)
by (metis abs_ge_self abs_mult_pos order_trans)

lemma bigo_sum1: "\<forall>x y. 0 <= h x y \<Longrightarrow>
    \<exists>c. \<forall>x y. \<bar>f x y\<bar> <= c * (h x y) \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. f x y) =o O(\<lambda>x. \<Sum>y \<in> A x. h x y)"
by (metis (no_types) bigo_sum_main)

lemma bigo_sum2: "\<forall>y. 0 <= h y \<Longrightarrow>
    \<exists>c. \<forall>y. \<bar>f y\<bar> <= c * (h y) \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. f y) =o O(\<lambda>x. \<Sum>y \<in> A x. h y)"
apply (rule bigo_sum1)
by metis+

lemma bigo_sum3: "f =o O(h) \<Longrightarrow>
    (\<lambda>x. \<Sum>y \<in> A x. (l x y) * f(k x y)) =o
      O(\<lambda>x. \<Sum>y \<in> A x. \<bar>l x y * h(k x y)\<bar>)"
apply (rule bigo_sum1)
 apply (rule allI)+
 apply (rule abs_ge_zero)
apply (unfold bigo_def)
apply (auto simp add: abs_mult)
by (metis abs_ge_zero mult.left_commute mult_left_mono)

lemma bigo_sum4: "f =o g +o O(h) \<Longrightarrow>
    (\<lambda>x. \<Sum>y \<in> A x. l x y * f(k x y)) =o
      (\<lambda>x. \<Sum>y \<in> A x. l x y * g(k x y)) +o
        O(\<lambda>x. \<Sum>y \<in> A x. \<bar>l x y * h(k x y)\<bar>)"
apply (rule set_minus_imp_plus)
apply (subst fun_diff_def)
apply (subst sum_subtractf [symmetric])
apply (subst right_diff_distrib [symmetric])
apply (rule bigo_sum3)
by (metis (lifting, no_types) fun_diff_def set_plus_imp_minus ext)

lemma bigo_sum5: "f =o O(h) \<Longrightarrow> \<forall>x y. 0 <= l x y \<Longrightarrow>
    \<forall>x. 0 <= h x \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. (l x y) * f(k x y)) =o
        O(\<lambda>x. \<Sum>y \<in> A x. (l x y) * h(k x y))"
apply (subgoal_tac "(\<lambda>x. \<Sum>y \<in> A x. (l x y) * h(k x y)) =
      (\<lambda>x. \<Sum>y \<in> A x. \<bar>(l x y) * h(k x y)\<bar>)")
 apply (erule ssubst)
 apply (erule bigo_sum3)
apply (rule ext)
apply (rule sum.cong)
apply (rule refl)
by (metis abs_of_nonneg zero_le_mult_iff)

lemma bigo_sum6: "f =o g +o O(h) \<Longrightarrow> \<forall>x y. 0 <= l x y \<Longrightarrow>
    \<forall>x. 0 <= h x \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. (l x y) * f(k x y)) =o
        (\<lambda>x. \<Sum>y \<in> A x. (l x y) * g(k x y)) +o
          O(\<lambda>x. \<Sum>y \<in> A x. (l x y) * h(k x y))"
  apply (rule set_minus_imp_plus)
  apply (subst fun_diff_def)
  apply (subst sum_subtractf [symmetric])
  apply (subst right_diff_distrib [symmetric])
  apply (rule bigo_sum5)
  apply (subst fun_diff_def [symmetric])
  apply (drule set_plus_imp_minus)
  apply auto
done

subsection \<open>Misc useful stuff\<close>

lemma bigo_useful_intro: "A <= O(f) \<Longrightarrow> B <= O(f) \<Longrightarrow>
  A + B <= O(f)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_mono2)
  apply assumption+
done

lemma bigo_useful_add: "f =o O(h) \<Longrightarrow> g =o O(h) \<Longrightarrow> f + g =o O(h)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_intro)
  apply assumption+
done

lemma bigo_useful_const_mult: "(c::'a::linordered_field) ~= 0 \<Longrightarrow>
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

lemma bigo_fix: "(\<lambda>x. f ((x::nat) + 1)) =o O(\<lambda>x. h(x + 1)) \<Longrightarrow> f 0 = 0 \<Longrightarrow>
    f =o O(h)"
apply (simp add: bigo_alt_def)
by (metis abs_ge_zero abs_mult abs_of_pos abs_zero not0_implies_Suc)

lemma bigo_fix2:
    "(\<lambda>x. f ((x::nat) + 1)) =o (\<lambda>x. g(x + 1)) +o O(\<lambda>x. h(x + 1)) \<Longrightarrow>
       f 0 = g 0 \<Longrightarrow> f =o g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_fix)
  apply (subst fun_diff_def)
  apply (subst fun_diff_def [symmetric])
  apply (rule set_plus_imp_minus)
  apply simp
  apply (simp add: fun_diff_def)
done

subsection \<open>Less than or equal to\<close>

definition lesso :: "('a => 'b::linordered_idom) => ('a => 'b) => ('a => 'b)" (infixl \<open><o\<close> 70) where
  "f <o g == (\<lambda>x. max (f x - g x) 0)"

lemma bigo_lesseq1: "f =o O(h) \<Longrightarrow> \<forall>x. \<bar>g x\<bar> <= \<bar>f x\<bar> \<Longrightarrow>
    g =o O(h)"
  apply (unfold bigo_def)
  apply clarsimp
apply (blast intro: order_trans)
done

lemma bigo_lesseq2: "f =o O(h) \<Longrightarrow> \<forall>x. \<bar>g x\<bar> <= f x \<Longrightarrow>
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
    \<forall>x. 0 <= g x \<Longrightarrow> \<forall>x. g x <= \<bar>f x\<bar> \<Longrightarrow>
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
      max.absorb2 order_eq_iff)

lemma bigo_lesso2: "f =o g +o O(h) \<Longrightarrow>
    \<forall>x. 0 <= k x \<Longrightarrow> \<forall>x. k x <= f x \<Longrightarrow>
      k <o g =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule max.cobounded2)
  apply (rule allI)
  apply (subst fun_diff_def)
apply (erule thin_rl)
(* sledgehammer *)
apply (case_tac "0 <= k x - g x")
 apply (metis (lifting) abs_le_D1 linorder_linear min_diff_distrib_left
          min.absorb1 min.absorb2 max.absorb1)
by (metis abs_ge_zero le_cases max.absorb2)

lemma bigo_lesso3: "f =o g +o O(h) \<Longrightarrow>
    \<forall>x. 0 <= k x \<Longrightarrow> \<forall>x. g x <= k x \<Longrightarrow>
      f <o k =o O(h)"
apply (unfold lesso_def)
apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
 apply (rule allI)
 apply (rule max.cobounded2)
apply (rule allI)
apply (subst fun_diff_def)
apply (erule thin_rl)
(* sledgehammer *)
apply (case_tac "0 <= f x - k x")
 apply simp
 apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
  apply (metis diff_less_0_iff_less linorder_not_le not_le_imp_less xt1(12) xt1(6))
 apply (metis add_minus_cancel diff_le_eq le_diff_eq uminus_add_conv_diff)
by (metis abs_ge_zero linorder_linear max.absorb1 max.commute)

lemma bigo_lesso4:
  "f <o g =o O(k::'a=>'b::{linordered_field}) \<Longrightarrow>
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

lemma bigo_lesso5: "f <o g =o O(h) \<Longrightarrow> \<exists>C. \<forall>x. f x <= g x + C * \<bar>h x\<bar>"
apply (simp only: lesso_def bigo_alt_def)
apply clarsimp
by (metis add.commute diff_le_eq)

end
