(* Title:  mirabelle_sledgehammer.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

fun sledgehammer_action {pre=st, ...} =
  let
    val prover_name = hd (space_explode " " (AtpManager.get_atps ()))
    val thy = Proof.theory_of st
 
    val prover = the (AtpManager.get_prover prover_name thy)
    val timeout = AtpManager.get_timeout () 

    val (success, message) =
      let
        val (success, message, _, _, _) =
          prover timeout NONE NONE prover_name 1 (Proof.get_goal st)
      in (success, message) end
      handle ResHolClause.TOO_TRIVIAL => (true, "trivial")
           | ERROR msg => (false, "error: " ^ msg)
  in
    if success
    then SOME ("success (" ^ prover_name ^ ": " ^ message ^ ")")
    else NONE
  end

fun invoke _ = Mirabelle.register ("sledgehammer", sledgehammer_action)

end
