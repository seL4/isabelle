(*  Title:      CTT/rew
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Simplifier for CTT, using Typedsimp
*)

(*Make list of ProdE RS ProdE ... RS ProdE RS EqE
  for using assumptions as rewrite rules*)
fun peEs 0 = []
  | peEs n = EqE :: map (apl(ProdE, op RS)) (peEs (n-1));

(*Tactic used for proving conditions for the cond_rls*)
val prove_cond_tac = eresolve_tac (peEs 5);


structure TSimp_data: TSIMP_DATA =
  struct
  val refl              = refl_elem
  val sym               = sym_elem
  val trans             = trans_elem
  val refl_red          = refl_red
  val trans_red         = trans_red
  val red_if_equal      = red_if_equal
  val default_rls       = comp_rls
  val routine_tac       = routine_tac routine_rls
  end;

structure TSimp = TSimpFun (TSimp_data);

val standard_congr_rls = intrL2_rls @ elimL_rls;

(*Make a rewriting tactic from a normalization tactic*)
fun make_rew_tac ntac =
    TRY eqintr_tac  THEN  TRYALL (resolve_tac [TSimp.split_eqn])  THEN  
    ntac;

fun rew_tac thms = make_rew_tac
    (TSimp.norm_tac(standard_congr_rls, thms));

fun hyp_rew_tac thms = make_rew_tac
    (TSimp.cond_norm_tac(prove_cond_tac, standard_congr_rls, thms));
