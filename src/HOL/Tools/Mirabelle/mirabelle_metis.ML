(*  Title:      HOL/Mirabelle/Tools/mirabelle_metis.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Sascha Boehme, TU Munich
    Author:     Martin Desharnais, UniBw Munich

Mirabelle action: "metis".
*)

structure Mirabelle_Metis: MIRABELLE_ACTION =
struct

fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    fun run_action ({pre, post, ...} : Mirabelle.command) =
      let
        val thms = Mirabelle.theorems_of_sucessful_proof post;
        val names = map Thm.get_name_hint thms;
        val facts = map #1 (Facts.props (Proof_Context.facts_of (Proof.context_of pre)));
        fun metis ctxt = Metis_Tactic.metis_tac [] ATP_Problem_Generate.liftingN ctxt (thms @ facts);
      in
        (if Mirabelle.can_apply timeout metis pre then "succeeded" else "failed")
        |> not (null names) ? suffix (":\n" ^ commas names)
      end
  in {run_action = run_action, finalize = K ""} end

val () = Mirabelle.register_action "metis" make_action

end
