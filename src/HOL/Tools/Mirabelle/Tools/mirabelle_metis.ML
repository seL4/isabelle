(* Title:  mirabelle_metis.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Metis : MIRABELLE_ACTION =
struct

fun metis_action timeout {pre, post} =
  let
    val thms = Mirabelle.theorems_of_sucessful_proof post
    val names = map Thm.get_name thms

    val facts = Facts.props (ProofContext.facts_of (Proof.context_of pre))

    fun metis ctxt = MetisTools.metis_tac ctxt (thms @ facts)
  in
    (if Mirabelle.can_apply timeout metis pre then "succeeded" else "failed")
    |> suffix (" (" ^ commas names ^ ")")
    |> SOME
  end

fun invoke _ = Mirabelle.register ("metis", metis_action)

end
