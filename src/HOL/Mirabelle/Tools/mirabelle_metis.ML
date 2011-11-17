(*  Title:      HOL/Mirabelle/Tools/mirabelle_metis.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

structure Mirabelle_Metis : MIRABELLE_ACTION =
struct

fun metis_tag id = "#" ^ string_of_int id ^ " metis: "

fun init _ = I
fun done _ _ = ()

fun run id ({pre, post, timeout, log, ...}: Mirabelle.run_args) =
  let
    val thms = Mirabelle.theorems_of_sucessful_proof post
    val names = map Thm.get_name_hint thms
    val add_info = if null names then I else suffix (":\n" ^ commas names)

    val facts = Facts.props (Proof_Context.facts_of (Proof.context_of pre))

    fun metis ctxt =
      Metis_Tactic.metis_tac [] ATP_Translate.lam_liftingN ctxt (thms @ facts)
  in
    (if Mirabelle.can_apply timeout metis pre then "succeeded" else "failed")
    |> prefix (metis_tag id)
    |> add_info
    |> log
  end
  handle TimeLimit.TimeOut => log (metis_tag id ^ "timeout")
       | ERROR msg => log (metis_tag id ^ "error: " ^ msg)

fun invoke _ = Mirabelle.register (init, Mirabelle.catch metis_tag run, done)

end
