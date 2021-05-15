(*  Title:      HOL/Mirabelle/Tools/mirabelle_metis.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich

Mirabelle action: "metis".
*)

structure Mirabelle_Metis: sig end =
struct

val _ =
  Theory.setup (Mirabelle.command_action \<^binding>\<open>metis\<close>
    (fn {timeout, ...} => fn {pre, post, ...} =>
      let
        val thms = Mirabelle.theorems_of_sucessful_proof post;
        val names = map Thm.get_name_hint thms;
        val facts = map #1 (Facts.props (Proof_Context.facts_of (Proof.context_of pre)));
        fun metis ctxt = Metis_Tactic.metis_tac [] ATP_Problem_Generate.liftingN ctxt (thms @ facts);
      in
        (if Mirabelle.can_apply timeout metis pre then "succeeded" else "failed")
        |> not (null names) ? suffix (":\n" ^ commas names)
      end));

end
