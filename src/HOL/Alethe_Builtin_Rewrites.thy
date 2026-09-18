(*  Title:      HOL/Alethe_Builtin_Rewrites.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_Builtin_Rewrites
  imports "Alethe_Rare_Nary_Ops"
begin

(*
Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in
Alethe_Rare_Interface.thy and register the rules using the cvc5_rare command.
*)

named_theorems rewrite_ite_true_cond \<open>automatically_generated\<close>

(* (define-rule ite-true-cond ((x ?) (y ?)) (ite true x y) x) *)
lemma [rewrite_ite_true_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (if True then x else y) = x"
  by auto

named_theorems rewrite_ite_false_cond \<open>automatically_generated\<close>

(* (define-rule ite-false-cond ((x ?) (y ?)) (ite false x y) y) *)
lemma [rewrite_ite_false_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (if False then x else y) = y"
  by auto

named_theorems rewrite_ite_not_cond \<open>automatically_generated\<close>

(* (define-rule ite-not-cond ((c Bool) (x ?) (y ?)) (ite (not c) x y) (ite c y x)) *)
lemma [rewrite_ite_not_cond]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y) \<Longrightarrow> (if \<not> c then x else y) = (if c then y else x)"
  by auto

named_theorems rewrite_ite_eq_branch \<open>automatically_generated\<close>

(* (define-rule ite-eq-branch ((c Bool) (x ?)) (ite c x x) x) *)
lemma [rewrite_ite_eq_branch]:
  fixes c::"bool" and x::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else x) = x"
  by auto

named_theorems rewrite_ite_then_lookahead \<open>automatically_generated\<close>

(* (define-rule ite-then-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c (ite c x y) z) (ite c x z)) *)
lemma [rewrite_ite_then_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then if c then x else y else z) = (if c then x else z)"
  by auto

named_theorems rewrite_ite_else_lookahead \<open>automatically_generated\<close>

(* (define-rule ite-else-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c x (ite c y z)) (ite c x z)) *)
lemma [rewrite_ite_else_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then x else if c then y else z) = (if c then x else z)"
  by auto

named_theorems rewrite_ite_then_neg_lookahead \<open>automatically_generated\<close>

(* (define-rule ite-then-neg-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c (ite (not c) x y) z) (ite c y z)) *)
lemma [rewrite_ite_then_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then if \<not> c then x else y else z) = (if c then y else z)"
  by auto

named_theorems rewrite_ite_else_neg_lookahead \<open>automatically_generated\<close>

(* (define-rule ite-else-neg-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c x (ite (not c) y z)) (ite c x y)) *)
lemma [rewrite_ite_else_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then x else if \<not> c then y else z) = (if c then x else y)"
  by auto

end
