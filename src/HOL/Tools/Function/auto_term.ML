(*  Title:      HOL/Tools/Function/auto_term.ML
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

fun inst_thm ctxt rel st =
    let
      val cert = Thm.cterm_of (ProofContext.theory_of ctxt)
      val rel' = cert (singleton (Variable.polymorphic ctxt) rel)
      val st' = Thm.incr_indexes (#maxidx (Thm.rep_cterm rel') + 1) st
      val Rvar = cert (Var (the_single (Term.add_vars (prop_of st') [])))
    in 
      Drule.cterm_instantiate [(Rvar, rel')] st' 
    end

fun relation_tac ctxt rel i = 
    TRY (Function_Common.apply_termination_rule ctxt i)
    THEN PRIMITIVE (inst_thm ctxt rel)

val setup =
  Method.setup @{binding relation}
    (Args.term >> (fn rel => fn ctxt => SIMPLE_METHOD' (relation_tac ctxt rel)))
    "proves termination using a user-specified wellfounded relation"

end
