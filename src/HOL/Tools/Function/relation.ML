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
  case Term.add_vars (prop_of st) [] of
    [v as (_, T)] =>
      let val cert = Thm.cterm_of (Thm.theory_of_thm st);
      in PRIMITIVE (Thm.instantiate ([], [(cert (Var v), cert (inst T))])) st end
  | _ => Seq.empty;

fun relation_tac ctxt rel i =
  TRY (Function_Common.apply_termination_rule ctxt i)
  THEN inst_state_tac rel;


(* version with type inference *)

fun inst_state_infer_tac ctxt rel st =
  case Term.add_vars (prop_of st) [] of
    [v as (_, T)] =>
      let
        val cert = Thm.cterm_of (Proof_Context.theory_of ctxt);
        val rel' = singleton (Variable.polymorphic ctxt) rel
          |> map_types Type_Infer.paramify_vars
          |> Type.constraint T
          |> Syntax.check_term ctxt
          |> cert;
      in
        PRIMITIVE (Thm.instantiate ([], [(cert (Var v), rel')])) st
      end
  | _ => Seq.empty;

fun relation_infer_tac ctxt rel i =
  TRY (Function_Common.apply_termination_rule ctxt i)
  THEN inst_state_infer_tac ctxt rel;

end
