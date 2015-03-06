(*  Title:      HOL/Tools/Function/relation.ML
    Author:     Alexander Krauss, TU Muenchen

Tactics to start a termination proof using a user-specified relation.
*)

signature FUNCTION_RELATION =
sig
  val relation_tac: Proof.context -> (typ -> term) -> int -> tactic
  val relation_infer_tac: Proof.context -> term -> int -> tactic
end

structure Function_Relation : FUNCTION_RELATION =
struct

(* tactic version *)

fun inst_state_tac inst st =
  (case Term.add_vars (Thm.prop_of st) [] of  (* FIXME tactic should not inspect main conclusion *)
    [v as (_, T)] =>
      let val thy = Thm.theory_of_thm st in
        PRIMITIVE (Thm.instantiate ([], [(Thm.cterm_of thy (Var v), Thm.cterm_of thy (inst T))])) st
      end
  | _ => Seq.empty);

fun relation_tac ctxt rel i =
  TRY (Function_Common.termination_rule_tac ctxt i)
  THEN inst_state_tac rel;


(* version with type inference *)

fun inst_state_infer_tac ctxt rel st =
  (case Term.add_vars (Thm.prop_of st) [] of  (* FIXME tactic should not inspect main conclusion *)
    [v as (_, T)] =>
      let
        val rel' = singleton (Variable.polymorphic ctxt) rel
          |> map_types Type_Infer.paramify_vars
          |> Type.constraint T
          |> Syntax.check_term ctxt
          |> Proof_Context.cterm_of ctxt;
      in
        PRIMITIVE (Thm.instantiate ([], [(Proof_Context.cterm_of ctxt (Var v), rel')])) st
      end
  | _ => Seq.empty);

fun relation_infer_tac ctxt rel i =
  TRY (Function_Common.termination_rule_tac ctxt i)
  THEN inst_state_infer_tac ctxt rel;

end
