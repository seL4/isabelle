signature EXPANSION_INTERFACE =
sig
type T

val expand_term : 
  Lazy_Eval.eval_ctxt -> term -> Asymptotic_Basis.basis -> T * Asymptotic_Basis.basis
val expand_terms : 
  Lazy_Eval.eval_ctxt -> term list -> Asymptotic_Basis.basis -> T list * Asymptotic_Basis.basis

val prove_nhds : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm
val prove_at_infinity : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm
val prove_at_top : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm
val prove_at_bot : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm
val prove_at_0 : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm
val prove_at_right_0 : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm
val prove_at_left_0 : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm
val prove_eventually_nonzero : Lazy_Eval.eval_ctxt -> T * Asymptotic_Basis.basis -> thm

val prove_eventually_less : Lazy_Eval.eval_ctxt -> T * T * Asymptotic_Basis.basis -> thm
val prove_eventually_greater : Lazy_Eval.eval_ctxt -> T * T * Asymptotic_Basis.basis -> thm

val prove_smallo : Lazy_Eval.eval_ctxt -> T * T * Asymptotic_Basis.basis -> thm
val prove_bigo : Lazy_Eval.eval_ctxt -> T * T * Asymptotic_Basis.basis -> thm
val prove_bigtheta : Lazy_Eval.eval_ctxt -> T * T * Asymptotic_Basis.basis -> thm
val prove_asymp_equiv : Lazy_Eval.eval_ctxt -> T * T * Asymptotic_Basis.basis -> thm

end