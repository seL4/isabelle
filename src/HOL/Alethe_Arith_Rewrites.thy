(*  Title:      HOL/Alethe_Arith_Rewrites.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_Arith_Rewrites
  imports "Alethe_Arith_Rewrites_Lemmas"
begin

(*
Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in
Alethe_Rare_Interface.thy and register the rules using the cvc5_rare command.
*)

named_theorems rewrite_arith_elim_gt \<open>automatically_generated\<close>

(*(define-rule arith-elim-gt ((t ?) (s ?)) (> t s) (not (>= s t)))*)
lemma [rewrite_arith_elim_gt]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (s < t) = (\<not> t \<le> s)"
  by auto

named_theorems rewrite_arith_elim_lt \<open>automatically_generated\<close>

(*(define-rule arith-elim-lt ((t ?) (s ?)) (< t s) (not (>= t s)))*)
lemma [rewrite_arith_elim_lt]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t < s) = (\<not> s \<le> t)"
  by auto

named_theorems rewrite_arith_elim_int_gt \<open>automatically_generated\<close>

(*(define-rule arith-elim-int-gt ((t Int) (s Int)) (> t s) (>= t (+ s 1)))*)
lemma [rewrite_arith_elim_int_gt]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t > s) = (t \<ge> (s + 1))"
  by auto

named_theorems rewrite_arith_elim_int_lt \<open>automatically_generated\<close>

(*(define-rule arith-elim-int-lt ((t Int) (s Int)) (< t s) (>= s (+ t 1)))*)
lemma [rewrite_arith_elim_int_lt]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t < s) = (s \<ge> (t + 1))"
  by auto

named_theorems rewrite_arith_elim_leq \<open>automatically_generated\<close>

(*(define-rule arith-elim-leq ((t ?) (s ?)) (<= t s) (>= s t))*)
lemma [rewrite_arith_elim_leq]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<le> s) = (t \<le> s)"
  by auto

named_theorems rewrite_arith_leq_norm \<open>automatically_generated\<close>

(*(define-rule arith-leq-norm ((t Int) (s Int)) (<= t s) (not (>= t (+ s 1))))*)
lemma [rewrite_arith_leq_norm]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<le> s) = (\<not> s + (1::int) \<le> t)"
  by auto

named_theorems rewrite_arith_geq_tighten \<open>automatically_generated\<close>

(*(define-rule arith-geq-tighten ((t Int) (s Int)) (not (>= t s)) (>= s (+ t 1)))*)
lemma [rewrite_arith_geq_tighten]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (\<not> s \<le> t) = (t + (1::int) \<le> s)"
  by auto

named_theorems rewrite_arith_geq_norm1_int \<open>automatically_generated\<close>

(*(define-rule arith-geq-norm1-int ((t Int) (s Int)) (>= t s) (>= (- t s) 0))*)
lemma [rewrite_arith_geq_norm1_int]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (s \<le> t) = ((0::int) \<le> t - s)"
  by auto

named_theorems rewrite_arith_eq_elim_int \<open>automatically_generated\<close>

(*(define-rule arith-eq-elim-int ((t Int) (s Int)) (= t s) (and (>= t s) (<= t s)))*)
lemma [rewrite_arith_eq_elim_int]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t = s) = (t \<ge> s \<and> t \<le> s))"
  by auto

named_theorems rewrite_arith_mod_over_mod \<open>automatically_generated\<close>

(*
(define-cond-rule arith-mod-over-mod ((c Int) (ts Int :list) (r Int) (ss Int :list))
  (not (= c 0))
  (mod_total (+ ts (mod_total r c) ss) c)
  (mod_total (+ ts r ss) c))
*)
lemma [rewrite_arith_mod_over_mod]:
  fixes c::int and ts::"int cvc_ListVar" and r::int and ss::"int cvc_ListVar" 
  shows "NO_MATCH cvc_a (undefined c ts r ss)
 \<Longrightarrow> \<not>(c=0) 
 \<Longrightarrow> SMT.z3mod (cvc_list_left (+) ts (cvc_list_right (+) (SMT.z3mod r c) ss)) c
= SMT.z3mod (cvc_list_left (+) ts (cvc_list_right (+) r ss)) c"
  apply (cases ts)
  apply (cases ss)
  subgoal for ts' ss'
    unfolding SMT.z3mod_def
     apply simp_all
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op(3))
     apply (induction ts' arbitrary: ts)
     apply simp_all
     apply (induction ss' arbitrary: ss)
     apply simp_all
     apply (meson mod_add_left_eq)
    by (metis (no_types, lifting) mod_add_right_eq)
  done

named_theorems rewrite_arith_divisible_elim \<open>automatically_generated\<close>

(*
(define-cond-rule arith-divisible-elim ((n Int) (t Int))
  (not (= n 0))
  (divisible n t)
  (= (mod_total t n) 0))
*)
lemma [rewrite_arith_divisible_elim]:
  fixes n::"int" and t::"int"
  shows "NO_MATCH cvc_a (undefined n t)
 \<Longrightarrow> \<not>(n = 0) \<Longrightarrow> ((n dvd t) = (SMT.z3mod t n = 0))"
  apply (simp add: SMT.z3mod_def)
  by auto

named_theorems rewrite_arith_geq_ite_lift \<open>\<close>

(*
(define-rule arith-geq-ite-lift ((C Bool) (t ?) (s ?) (r ?))
  (>= (ite C t s) r)
  (ite C (>= t r) (>= s r)))
*)
lemma [rewrite_arith_geq_ite_lift]:
  fixes C::bool and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) \<ge> r) = (if C then (t \<ge> r) else (s \<ge> r)))"
  by auto

named_theorems rewrite_arith_leq_ite_lift \<open>\<close>

(*
(define-rule arith-leq-ite-lift ((C Bool) (t ?) (s ?) (r ?))
  (<= (ite C t s) r)
  (ite C (<= t r) (<= s r)))
*)
lemma [rewrite_arith_leq_ite_lift]:
  fixes C::bool and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) \<le> r) = (if C then (t \<le> r) else (s \<le> r)))"
  by auto

named_theorems rewrite_arith_min_lt1 \<open>\<close>

(*
(define-rule arith-min-lt1 ((t ?) (s ?))
  (<= (ite (< t s) t s) t)
  true)
*)
lemma [rewrite_arith_min_lt1]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((if (t < s) then t else s) \<le> t) = True"
  by auto

named_theorems rewrite_arith_min_lt2 \<open>\<close>

(*
(define-rule arith-min-lt2 ((t ?) (s ?))
  (<= (ite (< t s) t s) s)
  true)
*)
lemma [rewrite_arith_min_lt2]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((if (t < s) then t else s) \<le> s) = True"
  by auto

named_theorems rewrite_arith_max_geq1 \<open>\<close>

(*
(define-rule arith-max-geq1 ((t ?) (s ?))
  (>= (ite (>= t s) t s) t)
  true)
*)
lemma [rewrite_arith_max_geq1]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((if (t \<ge> s) then t else s) \<ge> t) = True"
  by auto

named_theorems rewrite_arith_max_geq2 \<open>\<close>

(*
(define-rule arith-max-geq2 ((t ?) (s ?))
  (>= (ite (>= t s) t s) s)
  true)
*)
lemma [rewrite_arith_max_geq2]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((if (t \<ge> s) then t else s) \<ge> s) = True"
  by auto


end
