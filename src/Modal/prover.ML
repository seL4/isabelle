(*  Title:      91/Modal/prover
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
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
    val rule_tac   : thm list -> int ->tactic
    val step_tac   : int -> tactic
    val solven_tac : int -> int -> tactic
    val solve_tac  : int -> tactic
end;

functor Modal_ProverFun (Modal_Rule: MODAL_PROVER_RULE) : MODAL_PROVER = 
struct
local open Modal_Rule
in 

(*Returns the list of all formulas in the sequent*)
fun forms_of_seq (Const("Seqof",_) $ P $ u) = P :: forms_of_seq u
  | forms_of_seq (H $ u) = forms_of_seq u
  | forms_of_seq _ = [];

(*Tests whether two sequences (left or right sides) could be resolved.
  seqp is a premise (subgoal), seqc is a conclusion of an object-rule.
  Assumes each formula in seqc is surrounded by sequence variables
  -- checks that each concl formula looks like some subgoal formula.*)
fun could_res (seqp,seqc) =
      forall (fn Qc => exists (fn Qp => could_unify (Qp,Qc)) 
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
fun filseq_resolve_tac rules maxr = SUBGOAL(fn (prem,i) =>
  let val rls = filter_thms could_resolve_seq (maxr+1, prem, rules)
  in  if length rls > maxr  then  no_tac  else resolve_tac rls i
  end);

fun fresolve_tac rls n = filseq_resolve_tac rls 999 n;

(* NB No back tracking possible with aside rules *)

fun aside_tac n = DETERM(REPEAT (filt_resolve_tac aside_rls 999 n));
fun rule_tac rls n = fresolve_tac rls n THEN aside_tac n;

val fres_safe_tac = fresolve_tac safe_rls;
val fres_unsafe_tac = fresolve_tac unsafe_rls THEN' aside_tac;
val fres_bound_tac = fresolve_tac bound_rls;

fun UPTOGOAL n tf = let fun tac i = if i<n then all_tac
                                    else tf(i) THEN tac(i-1)
                    in STATE(fn state=> tac(nprems_of state)) end;

(* Depth first search bounded by d *)
fun solven_tac d n = STATE (fn state =>
        if d<0 then no_tac
        else if (nprems_of state = 0) then all_tac 
        else (DETERM(fres_safe_tac n) THEN UPTOGOAL n (solven_tac d)) ORELSE
                 ((fres_unsafe_tac n  THEN UPTOGOAL n (solven_tac d)) APPEND
                   (fres_bound_tac n  THEN UPTOGOAL n (solven_tac (d-1)))));

fun solve_tac d = rewrite_goals_tac rewrite_rls THEN solven_tac d 1;

fun step_tac n = STATE (fn state =>  
      if (nprems_of state = 0) then all_tac 
      else (DETERM(fres_safe_tac n)) ORELSE 
           (fres_unsafe_tac n APPEND fres_bound_tac n));

end;
end;
