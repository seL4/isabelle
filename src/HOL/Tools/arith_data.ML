(*  Title:      HOL/arith_data.ML
    Author:     Markus Wenzel, Stefan Berghofer, and Tobias Nipkow

Common arithmetic proof auxiliary.
*)

signature ARITH_DATA =
sig
  val prove_conv_nohyps: tactic list -> Proof.context -> term * term -> thm option
  val prove_conv: tactic list -> Proof.context -> thm list -> term * term -> thm option
  val prove_conv2: tactic -> (simpset -> tactic) -> simpset -> term * term -> thm
  val simp_all_tac: thm list -> simpset -> tactic
  val simplify_meta_eq: thm list -> simpset -> thm -> thm
  val trans_tac: thm option -> tactic
  val prep_simproc: string * string list * (theory -> simpset -> term -> thm option)
    -> simproc
end;

structure Arith_Data: ARITH_DATA =
struct

fun prove_conv_nohyps tacs ctxt (t, u) =
  if t aconv u then NONE
  else let val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))
  in SOME (Goal.prove ctxt [] [] eq (K (EVERY tacs))) end;

fun prove_conv tacs ctxt (_: thm list) = prove_conv_nohyps tacs ctxt;

fun prove_conv2 expand_tac norm_tac ss tu = (*FIXME avoid standard*)
  mk_meta_eq (standard (Goal.prove (Simplifier.the_context ss) [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq tu))
    (K (EVERY [expand_tac, norm_tac ss]))));

fun simp_all_tac rules =
  let val ss0 = HOL_ss addsimps rules
  in fn ss => ALLGOALS (simp_tac (Simplifier.inherit_context ss ss0)) end;

fun simplify_meta_eq rules =
  let val ss0 = HOL_basic_ss addeqcongs [eq_cong2] addsimps rules
  in fn ss => simplify (Simplifier.inherit_context ss ss0) o mk_meta_eq end

fun trans_tac NONE  = all_tac
  | trans_tac (SOME th) = ALLGOALS (rtac (th RS trans));

fun prep_simproc (name, pats, proc) = (*FIXME avoid the_context*)
  Simplifier.simproc (the_context ()) name pats proc;

end;
