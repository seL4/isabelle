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

fun inst_state_tac ctxt rel st =
  let
    val cert = Thm.cterm_of (ProofContext.theory_of ctxt)
    val rel' = cert (singleton (Variable.polymorphic ctxt) rel)
    val st' = Thm.incr_indexes (#maxidx (Thm.rep_cterm rel') + 1) st
  in case Term.add_vars (prop_of st') [] of
       [v] => 
         PRIMITIVE (Drule.cterm_instantiate [(cert (Var v), rel')]) st'
     | _ => Seq.empty
  end

fun relation_tac ctxt rel i =
  TRY (Function_Common.apply_termination_rule ctxt i)
  THEN inst_state_tac ctxt rel

val setup =
  Method.setup @{binding relation}
    (Args.term >> (fn rel => fn ctxt => SIMPLE_METHOD' (relation_tac ctxt rel)))
    "proves termination using a user-specified wellfounded relation"

end
