(*  Title:      HOL/Tools/function_package/auto_term.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Method "relation" to commence a termination proof using a user-specified relation.
*)

signature FUNDEF_RELATION =
sig
  val relation_tac: Proof.context -> term -> int -> tactic
  val setup: theory -> theory
end

structure FundefRelation : FUNDEF_RELATION =
struct

fun relation_tac ctxt rel =
    let
      val cert = Thm.cterm_of (ProofContext.theory_of ctxt)

      val rel' = cert (singleton (Variable.polymorphic ctxt) rel)
      val rule = FundefCommon.get_termination_rule ctxt |> the
                  |> Thm.incr_indexes (#maxidx (Thm.rep_cterm rel') + 1)

      val prem = #1 (Logic.dest_implies (Thm.prop_of rule))
      val Rvar = cert (Var (the_single (Term.add_vars prem [])))
    in rtac (Drule.cterm_instantiate [(Rvar, rel')] rule) end


val setup = Method.add_methods
  [("relation", (Method.SIMPLE_METHOD' o uncurry relation_tac) oo (Method.syntax Args.term),
    "proves termination using a user-specified wellfounded relation")]

end
