(*  Title:      CTT/rew.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Simplifier for CTT, using Typedsimp.
*)

(*Make list of ProdE RS ProdE ... RS ProdE RS EqE
  for using assumptions as rewrite rules*)
fun peEs 0 = []
  | peEs n = @{thm EqE} :: map (curry (op RS) @{thm ProdE}) (peEs (n-1));

(*Tactic used for proving conditions for the cond_rls*)
fun prove_cond_tac ctxt = eresolve_tac ctxt (peEs 5);


structure TSimp_data: TSIMP_DATA =
  struct
  val refl              = @{thm refl_elem}
  val sym               = @{thm sym_elem}
  val trans             = @{thm trans_elem}
  val refl_red          = @{thm refl_red}
  val trans_red         = @{thm trans_red}
  val red_if_equal      = @{thm red_if_equal}
  val default_rls       = @{thms comp_rls}
  val routine_tac       = routine_tac @{thms routine_rls}
  end;

structure TSimp = TSimpFun (TSimp_data);

val standard_congr_rls = @{thms intrL2_rls} @ @{thms elimL_rls};

(*Make a rewriting tactic from a normalization tactic*)
fun make_rew_tac ctxt ntac =
    TRY (eqintr_tac ctxt)  THEN  TRYALL (resolve_tac ctxt [TSimp.split_eqn])  THEN  
    ntac;

fun rew_tac ctxt thms = make_rew_tac ctxt
    (TSimp.norm_tac ctxt (standard_congr_rls, thms));

fun hyp_rew_tac ctxt thms = make_rew_tac ctxt
    (TSimp.cond_norm_tac ctxt (prove_cond_tac ctxt, standard_congr_rls, thms));
