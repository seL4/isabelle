(*  Title:      HOL/Tools/Function/relation.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Method "relation" to commence a termination proof using a user-specified relation.
*)

signature FUNCTION_RELATION =
sig
  val relation_tac: Proof.context -> (typ -> term) -> int -> tactic
  val setup: theory -> theory
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


(* method version (with type inference) *)

fun inst_state_infer_tac ctxt rel st =
  case Term.add_vars (prop_of st) [] of
    [v as (_, T)] =>
      let
        val cert = Thm.cterm_of (ProofContext.theory_of ctxt);
        val rel' = singleton (Variable.polymorphic ctxt) rel
          |> map_types Type_Infer.paramify_vars
          |> Type.constraint T
          |> Syntax.check_term ctxt
          |> cert;
      in
        PRIMITIVE (Thm.instantiate ([], [(cert (Var v), rel')])) st
      end
  | _ => Seq.empty;

fun relation_meth rel ctxt = SIMPLE_METHOD' (fn i =>
  TRY (Function_Common.apply_termination_rule ctxt i)
  THEN inst_state_infer_tac ctxt rel);

val setup =
  Method.setup @{binding relation} (Args.term >> relation_meth)
    "proves termination using a user-specified wellfounded relation";

end
