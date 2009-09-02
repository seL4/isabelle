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

fun safe init done f x =
  let
    val y = init x
    val z = Exn.capture f y
    val _ = done y
  in Exn.release z end

val proverK = "prover"
val keepK = "keep"
val metisK = "metis"

fun sledgehammer_action args {pre=st, timeout, log, ...} =
  let
    val prover_name =
      AList.lookup (op =) args proverK
      |> the_default (hd (space_explode " " (AtpManager.get_atps ())))

    val thy = Proof.theory_of st
 
    val prover = the (AtpManager.get_prover prover_name thy)
    val atp_timeout = AtpManager.get_timeout () 

    (* run sledgehammer *)
    fun init NONE = !AtpWrapper.destdir
      | init (SOME path) =
          let
            (* Warning: we implicitly assume single-threaded execution here! *)
            val old = !AtpWrapper.destdir
            val _ = AtpWrapper.destdir := path
          in old end
    fun done path = AtpWrapper.destdir := path
    fun sh _ =
      let
        val atp = prover atp_timeout NONE NONE prover_name 1
        val (success, (message, thm_names), _, _, _) =
          TimeLimit.timeLimit timeout atp (Proof.get_goal st)
      in (success, message, SOME thm_names) end
      handle ResHolClause.TOO_TRIVIAL => (true, "trivial", SOME [])
    val (success, message, thm_names) = safe init done sh
      (AList.lookup (op =) args keepK)
    val _ =
      if success then log (quote prover_name ^ " succeeded:\n" ^ message)
      else log (prover_name ^ " failed")

    (* try metis *)
    fun get_thms ctxt = maps (thms_of_name ctxt)
    fun metis thms ctxt = MetisTools.metis_tac ctxt thms
    fun log_metis s =
      log ("applying metis: " ^ s)
    fun apply_metis thms =
      if Mirabelle.can_apply timeout (metis thms) st
      then "succeeded" else "failed"
    val _ =
      if not (AList.defined (op =) args metisK) then ()
      else
        these thm_names
        |> get_thms (Proof.context_of st)
        |> apply_metis
        |> log_metis
  in () end

fun invoke args = Mirabelle.register ("sledgehammer", sledgehammer_action args)

end
