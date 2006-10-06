(*  Title:      HOL/Tools/function_package/auto_term.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
The auto_term method.
*)


signature FUNDEF_AUTO_TERM =
sig
  val setup: theory -> theory
end

structure FundefAutoTerm : FUNDEF_AUTO_TERM =
struct

open FundefCommon
open FundefAbbrev


fun auto_term_tac ctxt rule rel wf_rules ss =
  let
    val cert = Thm.cterm_of (ProofContext.theory_of ctxt)

    val rel' = cert (singleton (Variable.polymorphic ctxt) rel)
    val rule' = rule |> Thm.incr_indexes (#maxidx (Thm.rep_cterm rel') + 1)
    val prem = #1 (Logic.dest_implies (Thm.prop_of rule'))
    val R' = cert (Var (the_single (Term.add_vars prem [])))
  in
    resolve_tac [Drule.cterm_instantiate [(R', rel')] rule'] 1  (* produce the usual goals *)
    THEN (ALLGOALS
      (fn 1 => REPEAT (ares_tac wf_rules 1)    (* Solve wellfoundedness *)
        | i => asm_simp_tac ss i))             (* Simplify termination conditions *)
  end


fun termination_meth src = Method.syntax Args.term src #> (fn (ctxt, rel) =>
  let
    val {simps, congs, wfs} = RecdefPackage.get_hints (Context.Proof ctxt)
    val ss = local_simpset_of ctxt addsimps simps

    val intro_rule = ProofContext.get_thm ctxt (Name "termination")
    (* FIXME avoid internal name lookup -- dynamic scoping! *)
  in Method.RAW_METHOD (K (auto_term_tac ctxt intro_rule rel wfs ss)) end)

val setup = Method.add_methods
  [("auto_term", termination_meth, "termination prover for recdef compatibility")]

end
