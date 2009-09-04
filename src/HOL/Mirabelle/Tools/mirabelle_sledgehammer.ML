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
val full_typesK = "full_types"

val sh_tag = "sledgehammer: "
val metis_tag = "metis (sledgehammer): "


local

fun init NONE = !AtpWrapper.destdir
  | init (SOME path) =
      let
        (* Warning: we implicitly assume single-threaded execution here! *)
        val old = !AtpWrapper.destdir
        val _ = AtpWrapper.destdir := path
      in old end

fun done path = AtpWrapper.destdir := path

fun run prover_name timeout st _ =
  let
    val prover = the (AtpManager.get_prover prover_name (Proof.theory_of st))
    val atp_timeout = AtpManager.get_timeout () 
    val atp = prover atp_timeout NONE NONE prover_name 1
    val (success, (message, thm_names), time, _, _, _) =
      TimeLimit.timeLimit timeout atp (Proof.get_goal st)
  in if success then (message, SOME (time, thm_names)) else (message, NONE) end
  handle ResHolClause.TOO_TRIVIAL => ("trivial", SOME (0, []))
       | TimeLimit.TimeOut => ("timeout", NONE)
       | ERROR msg => ("error: " ^ msg, NONE)

in

fun run_sledgehammer args thm_names {pre=st, timeout, log, ...} =
  let
    val prover_name =
      AList.lookup (op =) args proverK
      |> the_default (hd (space_explode " " (AtpManager.get_atps ())))
    val dir = AList.lookup (op =) args keepK
    val (msg, result) = safe init done (run prover_name timeout st) dir
    val _ =
      if is_some result
      then log (sh_tag ^ "succeeded (" ^ string_of_int (fst (the result)) ^
        ") [" ^ prover_name ^ "]:\n" ^ msg)
      else log (sh_tag ^ "failed: " ^ msg)
  in change thm_names (K (Option.map snd result)) end

end


fun with_time true t = "succeeded (" ^ string_of_int t ^ ")"
  | with_time false t = "failed (" ^ string_of_int t ^ ")"

fun run_metis args thm_names {pre=st, timeout, log, ...} =
  let
    fun get_thms ctxt = maps (thms_of_name ctxt)
    fun metis thms ctxt = MetisTools.metis_tac ctxt thms
    fun apply_metis thms = Mirabelle.can_apply timeout (metis thms) st
    fun timed_metis thms =
      uncurry with_time (Mirabelle.cpu_time apply_metis thms)
      handle TimeLimit.TimeOut => "timeout"
           | ERROR msg => "error: " ^ msg
    fun log_metis s = log (metis_tag ^ s)
  in
    if not (AList.defined (op =) args metisK) then ()
    else if is_none (!thm_names) then ()
    else
      log "-----"
      |> K (these (!thm_names))
      |> get_thms (Proof.context_of st)
      |> timed_metis
      |> log_metis
  end


fun sledgehammer_action args (st as {log, ...}) =
  let
    val thm_names = ref (NONE : string list option)
    val _ = Mirabelle.catch sh_tag (run_sledgehammer args thm_names) st
    val _ = Mirabelle.catch metis_tag (run_metis args thm_names) st
  in () end

fun invoke args =
  let
    val _ = AtpManager.set_full_types (AList.defined (op =) args full_typesK)
  in Mirabelle.register (sledgehammer_action args) end

end
