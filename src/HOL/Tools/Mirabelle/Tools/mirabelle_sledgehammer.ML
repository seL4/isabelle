(* Title:  mirabelle_sledgehammer.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

fun thms_of_name ctxt name =
  let
    val lex = OuterKeyword.get_lexicons
    val get = maps (ProofContext.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source {do_recover=false}
    |> OuterLex.source {do_recover=SOME false} lex Position.start
    |> OuterLex.source_proper
    |> Source.source OuterLex.stopper (SpecParse.xthms1 >> get) NONE
    |> Source.exhaust
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
    fun get_thms ctxt = maps (thms_of_name ctxt)
    fun metis thms ctxt = MetisTools.metis_tac ctxt thms
    fun apply_metis thms = "\nApplying metis with these theorems: " ^
     (if try (Mirabelle.can_apply (metis thms)) st = SOME true
      then "success"
      else "failure")
    val msg = apply_metis (get_thms (Proof.context_of st) (these thm_names))
  in
    if success
    then SOME ("success (" ^ prover_name ^ ": " ^ message ^ ")" ^ msg)
    else NONE
  end

fun invoke args = Mirabelle.register ("sledgehammer", sledgehammer_action args)

end
