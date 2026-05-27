theory Alethe_Arith_Real_Rewrites
  imports "HOL.Real"
begin (*Since this theory requires real operators it is not included in RARE_interface*)

named_theorems rewrite_arith_geq_norm1_real \<open>\<close>

(*(define-rule arith-geq-norm1-real ((t Real) (s Real)) (>= t s) (>= (- t s) 0/1))*)
lemma [rewrite_arith_geq_norm1_real]:
  fixes t::"real" and s::"real" 
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t \<ge> s) = ((t - s) \<ge> 0/1))"
  by simp

named_theorems rewrite_arith_eq_elim_real \<open>\<close>

(*(define-rule arith-eq-elim-real ((t Real) (s Real)) (= t s) (and (>= t s) (<= t s)))*)
lemma [rewrite_arith_eq_elim_real]:
  fixes t::"'a::linordered_idom"  and  s::"'a::linordered_idom" 
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t = s) = (t \<ge> s \<and> t \<le> s))"
  by auto

named_theorems rewrite_arith_to_int_to_real \<open>\<close>

(*(define-rule arith-to-int-elim-to-real ((x Int)) (to_int (to_real x)) x)*)
lemma [rewrite_arith_to_int_to_real]:
  fixes x::"int"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> floor (of_int x ::real) = x"
  by simp

named_theorems rewrite_arith_int_eq_conflict \<open>\<close>

(*
(define-cond-rule arith-int-eq-conflict ((t Int) (c Real))
  (not (= (to_real (to_int c)) c))
  (= (to_real t) c)
  false)
*)
lemma [rewrite_arith_int_eq_conflict]:
  fixes t::int and c::real
  shows "NO_MATCH cvc_a (undefined t c)
 \<Longrightarrow> \<not>((of_int (floor c)::real) = c) \<Longrightarrow> (((of_int t ::real) = c) = False)"
  by auto

named_theorems rewrite_arith_int_geq_tighten \<open>\<close>

(*
(define-cond-rule arith-int-geq-tighten ((t Int) (c Real) (cc Int))
  (and (not (= (to_real (to_int c)) c)) (= cc (+ (to_int c) 1)))
  (>= (to_real t) c)
  (>= t cc))
*)
lemma [rewrite_arith_int_geq_tighten]:
  fixes t::int and c::real and cc::int
  shows "NO_MATCH cvc_a (undefined t c cc)
 \<Longrightarrow> (\<not>((of_int (floor c)) = c) \<and> (cc = (floor c) + 1)) \<Longrightarrow> (((of_int t ::real) \<ge> c) = (t \<ge> cc))"
  by linarith

end
