(*  Title:      HOL/Tools/Function/relation.ML
    Author:     Alexander Krauss, TU Muenchen

Tactics to start a termination proof using a user-specified relation.
*)

signature FUNCTION_RELATION =
sig
  val relation_tac: Proof.context -> (typ -> term) -> int -> tactic
  val relation_infer_tac: Proof.context -> term -> int -> tactic
end

structure Function_Relation: FUNCTION_RELATION =
struct

(* tactic version *)

fun inst_state_tac ctxt inst =
  SUBGOAL (fn (goal, _) =>
    (case Term.add_vars goal [] of
      [v as (_, T)] =>
        PRIMITIVE (Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt (inst T))]))
    | _ => no_tac));

fun relation_tac ctxt rel i =
  TRY (Function_Common.termination_rule_tac ctxt i)
  THEN inst_state_tac ctxt rel i;


(* version with type inference *)

fun inst_state_infer_tac ctxt rel =
  SUBGOAL (fn (goal, _) =>
    (case Term.add_vars goal [] of
      [v as (_, T)] =>
        let
          val rel' =
            singleton (Variable.polymorphic ctxt) rel
            |> map_types Type_Infer.paramify_vars
            |> Type.constraint T
            |> Syntax.check_term ctxt;
        in PRIMITIVE (Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt rel')])) end
    | _ => no_tac));

fun relation_infer_tac ctxt rel i =
  TRY (Function_Common.termination_rule_tac ctxt i)
  THEN inst_state_infer_tac ctxt rel i;

end
