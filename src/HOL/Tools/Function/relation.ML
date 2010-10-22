(*  Title:      HOL/Tools/Function/relation.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Method "relation" to commence a termination proof using a user-specified relation.
*)

signature FUNCTION_RELATION =
sig
  val relation_tac: Proof.context -> term -> int -> tactic
  val setup: theory -> theory
end

structure Function_Relation : FUNCTION_RELATION =
struct

fun gen_inst_state_tac prep ctxt rel st =
  case Term.add_vars (prop_of st) [] of
    [v as (_, T)] =>
      let
        val cert = Thm.cterm_of (ProofContext.theory_of ctxt)
        val rel' = prep T (singleton (Variable.polymorphic ctxt) rel) 
          |> cert
        val st' = Thm.incr_indexes (#maxidx (Thm.rep_cterm rel') + 1) st (*FIXME??*)
      in        
        PRIMITIVE (Drule.cterm_instantiate [(cert (Var v), rel')]) st'
      end
  | _ => Seq.empty;

fun gen_relation_tac prep ctxt rel i =
  TRY (Function_Common.apply_termination_rule ctxt i)
  THEN gen_inst_state_tac prep ctxt rel

val relation_tac = gen_relation_tac (K I)

fun relation_meth rel ctxt = SIMPLE_METHOD' 
  (gen_relation_tac (fn T => map_types Type_Infer.paramify_vars
      #> Type.constraint T #> Syntax.check_term ctxt)
    ctxt rel)

val setup =
  Method.setup @{binding relation} (Args.term >> relation_meth)
    "proves termination using a user-specified wellfounded relation"

end
