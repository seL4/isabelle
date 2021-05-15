(*  Title:      HOL/TPTP/TPTP_Parser_Example.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Example of importing a TPTP problem and trying to prove it in Isabelle/HOL.
*)

theory TPTP_Parser_Example
imports TPTP_Parser TPTP_Interpret
begin

import_tptp "$TPTP/Problems/LCL/LCL414+1.p"

ML \<open>
val an_fmlas =
  TPTP_Interpret.get_manifests @{theory}
  |> hd (*FIXME use named lookup*)
  |> #2 (*get problem contents*)
  |> #3 (*get formulas*)
\<close>

(*Display nicely.*)
ML \<open>
List.app (fn (n, role, fmla, _) =>
  Pretty.writeln
    (Pretty.block [Pretty.str ("\"" ^ n ^ "\"" ^ "(" ^
      TPTP_Syntax.role_to_string role  ^ "): "), Syntax.pretty_term @{context} fmla])
  ) (rev an_fmlas)
\<close>

ML \<open>
(*Extract the (name, term) pairs of formulas having roles belonging to a
 user-supplied set*)
fun extract_terms roles : TPTP_Interpret.tptp_formula_meaning list ->
 (string * term) list =
   let
     fun role_predicate (_, role, _, _) =
       fold (fn r1 => fn b => role = r1 orelse b) roles false
   in filter role_predicate #> map (fn (n, _, t, _) => (n, t)) end
\<close>

ML \<open>
(*Use a given tactic on a goal*)
fun prove_conjectures tactic ctxt an_fmlas =
  let
    val assumptions =
      extract_terms
       [TPTP_Syntax.Role_Definition, TPTP_Syntax.Role_Axiom]
       an_fmlas
      |> map snd
    val goals = extract_terms [TPTP_Syntax.Role_Conjecture] an_fmlas
    fun driver (n, goal) =
      (n, Goal.prove ctxt [] assumptions goal (fn _ => tactic ctxt))
  in map driver goals end

val auto_prove = prove_conjectures auto_tac
val sh_prove = prove_conjectures (fn ctxt =>
  Sledgehammer_Tactics.sledgehammer_with_metis_tac ctxt []
  (*FIXME use relevance_override*)
  {add = [], del = [], only = false} 1)
\<close>

ML \<open>
@{assert} (is_some (try (auto_prove @{context}) an_fmlas) = false)
\<close>

sledgehammer_params [provers = z3, debug]
ML \<open>
@{assert} (is_some (try (sh_prove @{context}) an_fmlas) = true)
\<close>

end
