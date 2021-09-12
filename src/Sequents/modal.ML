(*  Title:      Sequents/modal.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Simple modal reasoner.
*)

signature MODAL_PROVER_RULE =
sig
  val rewrite_rls      : thm list
  val safe_rls         : thm list
  val unsafe_rls       : thm list
  val bound_rls        : thm list
  val aside_rls        : thm list
end;

signature MODAL_PROVER =
sig
  val rule_tac   : Proof.context -> thm list -> int ->tactic
  val step_tac   : Proof.context -> int -> tactic
  val solven_tac : Proof.context -> int -> int -> tactic
  val solve_tac  : Proof.context -> int -> tactic
end;

functor Modal_ProverFun (Modal_Rule: MODAL_PROVER_RULE) : MODAL_PROVER =
struct

(*Returns the list of all formulas in the sequent*)
fun forms_of_seq \<^Const_>\<open>SeqO' for P u\<close> = P :: forms_of_seq u
  | forms_of_seq (H $ u) = forms_of_seq u
  | forms_of_seq _ = [];

(*Tests whether two sequences (left or right sides) could be resolved.
  seqp is a premise (subgoal), seqc is a conclusion of an object-rule.
  Assumes each formula in seqc is surrounded by sequence variables
  -- checks that each concl formula looks like some subgoal formula.*)
fun could_res (seqp,seqc) =
      forall (fn Qc => exists (fn Qp => Term.could_unify (Qp,Qc))
                              (forms_of_seq seqp))
             (forms_of_seq seqc);

(*Tests whether two sequents G|-H could be resolved, comparing each side.*)
fun could_resolve_seq (prem,conc) =
  case (prem,conc) of
      (_ $ Abs(_,_,leftp) $ Abs(_,_,rightp),
       _ $ Abs(_,_,leftc) $ Abs(_,_,rightc)) =>
          could_res (leftp,leftc)  andalso  could_res (rightp,rightc)
    | _ => false;

(*Like filt_resolve_tac, using could_resolve_seq
  Much faster than resolve_tac when there are many rules.
  Resolve subgoal i using the rules, unless more than maxr are compatible. *)
fun filseq_resolve_tac ctxt rules maxr = SUBGOAL(fn (prem,i) =>
  let val rls = filter_thms could_resolve_seq (maxr+1, prem, rules)
  in  if length rls > maxr  then  no_tac  else resolve_tac ctxt rls i
  end);

fun fresolve_tac ctxt rls n = filseq_resolve_tac ctxt rls 999 n;

(* NB No back tracking possible with aside rules *)

val aside_net = Tactic.build_net Modal_Rule.aside_rls;
fun aside_tac ctxt n = DETERM (REPEAT (filt_resolve_from_net_tac ctxt 999 aside_net n));
fun rule_tac ctxt rls n = fresolve_tac ctxt rls n THEN aside_tac ctxt n;

fun fres_safe_tac ctxt = fresolve_tac ctxt Modal_Rule.safe_rls;
fun fres_unsafe_tac ctxt = fresolve_tac ctxt Modal_Rule.unsafe_rls THEN' aside_tac ctxt;
fun fres_bound_tac ctxt = fresolve_tac ctxt Modal_Rule.bound_rls;

fun UPTOGOAL n tf = let fun tac i = if i<n then all_tac
                                    else tf(i) THEN tac(i-1)
                    in fn st => tac (Thm.nprems_of st) st end;

(* Depth first search bounded by d *)
fun solven_tac ctxt d n st = st |>
 (if d < 0 then no_tac
  else if Thm.nprems_of st = 0 then all_tac
  else (DETERM(fres_safe_tac ctxt n) THEN UPTOGOAL n (solven_tac ctxt d)) ORELSE
           ((fres_unsafe_tac ctxt n  THEN UPTOGOAL n (solven_tac ctxt d)) APPEND
             (fres_bound_tac ctxt n  THEN UPTOGOAL n (solven_tac ctxt (d - 1)))));

fun solve_tac ctxt d =
  rewrite_goals_tac ctxt Modal_Rule.rewrite_rls THEN solven_tac ctxt d 1;

fun step_tac ctxt n =
  COND (has_fewer_prems 1) all_tac
       (DETERM(fres_safe_tac ctxt n) ORELSE
        (fres_unsafe_tac ctxt n APPEND fres_bound_tac ctxt n));

end;
