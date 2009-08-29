(* Title:  mirabelle_sledgehammer.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

local
val valid = Symbol.is_ascii_letter orf Symbol.is_ascii_digit orf
  member (op =) (explode "_.")
val name = Scan.many1 valid >> (rpair Position.none o implode)

val digit = (fn
  "0" => SOME 0 | "1" => SOME 1 | "2" => SOME 2 | "3" => SOME 3 |
  "4" => SOME 4 | "5" => SOME 5 | "6" => SOME 6 | "7" => SOME 7 |
  "8" => SOME 8 | "9" => SOME 9 | _ => NONE)
fun join d n = 10 * n + d
val number = Scan.repeat1 (Scan.some digit) >> (fn ds => fold join ds 0)
val interval = Scan.option (Scan.$$ "(" |-- number --| Scan.$$ ")" >>
  (single o Facts.Single))

val fact_ref = name -- interval >> Facts.Named

in

fun thm_of_name ctxt s =
  (case try (Scan.read Symbol.stopper fact_ref) (explode s) of
    SOME (SOME r) => ProofContext.get_fact ctxt r
  | _ => [])

end


fun sledgehammer_action args {pre=st, ...} =
  let
    val prover_name =
      AList.lookup (op =) args "prover"
      |> the_default (hd (space_explode " " (AtpManager.get_atps ())))

    val thy = Proof.theory_of st
 
    val prover = the (AtpManager.get_prover prover_name thy)
    val timeout = AtpManager.get_timeout () 

    (* run sledgehammer *)
    val (success, message, thm_names) =
      let
        val (success, (message, thm_names), _, _, _) =
          prover timeout NONE NONE prover_name 1 (Proof.get_goal st)
      in (success, message, SOME thm_names) end
      handle ResHolClause.TOO_TRIVIAL => (true, "trivial", SOME [])
           | ERROR msg => (false, "error: " ^ msg, NONE)

    (* try metis *)
    val thms = maps (thm_of_name (Proof.context_of st)) (these thm_names)
    fun metis ctxt = MetisTools.metis_tac ctxt thms
    val msg = if not (AList.defined (op =) args "metis") then "" else
      if try (Mirabelle.can_apply metis) st = SOME true
        then "\nMETIS: success"
        else "\nMETIS: failure"
  in
    if success
    then SOME ("success (" ^ prover_name ^ ": " ^ message ^ ")" ^ msg)
    else NONE
  end

fun invoke args = Mirabelle.register ("sledgehammer", sledgehammer_action args)

end
