(* Title:  mirabelle_sledgehammer.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

val proverK = "prover"
val keepK = "keep"
val metisK = "metis"
val full_typesK = "full_types"

fun sh_tag id = "#" ^ string_of_int id ^ " sledgehammer: "
fun metis_tag id = "#" ^ string_of_int id ^ " metis (sledgehammer): "


datatype data = Data of {
  sh_calls: int,
  sh_success: int,
  sh_time: int,
  metis_calls: int,
  metis_success: int,
  metis_time: int,
  metis_timeout: int }

fun make_data (sh_calls, sh_success, sh_time, metis_calls, metis_success,
    metis_time, metis_timeout) =
  Data {sh_calls=sh_calls, sh_success=sh_success, sh_time=sh_time,
    metis_calls=metis_calls, metis_success=metis_success,
    metis_time=metis_time, metis_timeout=metis_timeout}

fun map_data f (Data {sh_calls, sh_success, sh_time, metis_calls,
    metis_success, metis_time, metis_timeout}) =
  make_data (f (sh_calls, sh_success, sh_time, metis_calls, metis_success,
    metis_time, metis_timeout))

val empty_data = make_data (0, 0, 0, 0, 0, 0, 0)

val inc_sh_calls = map_data (fn (sh_calls, sh_success, sh_time, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls + 1, sh_success,
  sh_time, metis_calls, metis_success, metis_time, metis_timeout))

val inc_sh_success = map_data (fn (sh_calls, sh_success, sh_time, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls, sh_success + 1,
  sh_time, metis_calls, metis_success, metis_time, metis_timeout))

fun inc_sh_time t = map_data (fn (sh_calls, sh_success, sh_time, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls, sh_success,
  sh_time + t, metis_calls, metis_success, metis_time, metis_timeout))

val inc_metis_calls = map_data (fn (sh_calls, sh_success, sh_time, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls, sh_success,
  sh_time, metis_calls + 1, metis_success, metis_time, metis_timeout))

val inc_metis_success = map_data (fn (sh_calls, sh_success, sh_time,
  metis_calls, metis_success, metis_time, metis_timeout) => (sh_calls,
  sh_success, sh_time, metis_calls, metis_success + 1, metis_time,
  metis_timeout))

fun inc_metis_time t = map_data (fn (sh_calls, sh_success, sh_time,
  metis_calls, metis_success, metis_time, metis_timeout) => (sh_calls,
  sh_success, sh_time, metis_calls, metis_success, metis_time + t,
  metis_timeout))

val inc_metis_timeout = map_data (fn (sh_calls, sh_success, sh_time,
  metis_calls, metis_success, metis_time, metis_timeout) => (sh_calls,
  sh_success, sh_time, metis_calls, metis_success, metis_time,
  metis_timeout + 1))


local

val str = string_of_int
val str3 = Real.fmt (StringCvt.FIX (SOME 3))
fun percentage a b = string_of_int (a * 100 div b)
fun time t = Real.fromInt t / 1000.0
fun avg_time t n =
  if n > 0 then (Real.fromInt t / 1000.0) / Real.fromInt n else 0.0

fun log_sh_data log sh_calls sh_success sh_time =
 (log ("Total number of sledgehammer calls: " ^ str sh_calls);
  log ("Number of successful sledgehammer calls: " ^ str sh_success);
  log ("Success rate: " ^ percentage sh_success sh_calls ^ "%");
  log ("Total time for successful sledgehammer calls: " ^ str3 (time sh_time));
  log ("Average time for successful sledgehammer calls: " ^
    str3 (avg_time sh_time sh_success)))

fun log_metis_data log sh_success metis_calls metis_success metis_time
    metis_timeout =
 (log ("Total number of metis calls: " ^ str metis_calls);
  log ("Number of successful metis calls: " ^ str metis_success);
  log ("Number of metis timeouts: " ^ str metis_timeout);
  log ("Number of metis exceptions: " ^
    str (sh_success - metis_success - metis_timeout));
  log ("Success rate: " ^ percentage metis_success metis_calls ^ "%");
  log ("Total time for successful metis calls: " ^ str3 (time metis_time));
  log ("Average time for successful metis calls: " ^
    str3 (avg_time metis_time metis_success)))

in

fun log_data id log (Data {sh_calls, sh_success, sh_time, metis_calls,
    metis_success, metis_time, metis_timeout}) =
  if sh_calls > 0
  then
   (log ("\n\n\nReport #" ^ string_of_int id ^ ":\n");
    log_sh_data log sh_calls sh_success sh_time;
    log "";
    if metis_calls > 0 then log_metis_data log sh_success metis_calls
      metis_success metis_time metis_timeout else ())
  else ()

end


(* Warning: we implicitly assume single-threaded execution here! *)
val data = ref ([] : (int * data) list)

fun init id thy = (change data (cons (id, empty_data)); thy)
fun done id {log, ...} =
  AList.lookup (op =) (!data) id
  |> Option.map (log_data id log)
  |> K ()

fun change_data id f = (change data (AList.map_entry (op =) id f); ())


local

fun safe init done f x =
  let
    val y = init x
    val z = Exn.capture f y
    val _ = done y
  in Exn.release z end

fun init_sh NONE = !AtpWrapper.destdir
  | init_sh (SOME path) =
      let
        (* Warning: we implicitly assume single-threaded execution here! *)
        val old = !AtpWrapper.destdir
        val _ = AtpWrapper.destdir := path
      in old end

fun done_sh path = AtpWrapper.destdir := path

fun run_sh prover_name timeout st _ =
  let
    val prover = the (AtpManager.get_prover prover_name (Proof.theory_of st))
    val atp_timeout = AtpManager.get_timeout () 
    val atp = prover atp_timeout NONE NONE prover_name 1
    val ((success, (message, thm_names), time, _, _, _), time') =
      TimeLimit.timeLimit timeout (Mirabelle.cpu_time atp) (Proof.get_goal st)
  in
    if success then (message, SOME (time + time', thm_names))
    else (message, NONE)
  end
  handle ResHolClause.TOO_TRIVIAL => ("trivial", SOME (0, []))
       | TimeLimit.TimeOut => ("timeout", NONE)
       | ERROR msg => ("error: " ^ msg, NONE)

in

fun run_sledgehammer args thm_names id {pre=st, timeout, log, ...} =
  let
    val _ = change_data id inc_sh_calls 
    val prover_name =
      AList.lookup (op =) args proverK
      |> the_default (hd (space_explode " " (AtpManager.get_atps ())))
    val dir = AList.lookup (op =) args keepK
    val (msg, result) =
      safe init_sh done_sh (run_sh prover_name timeout st) dir
    val _ =
      if is_some result
      then
        let
          val time = fst (the result)
          val _ = change_data id inc_sh_success
          val _ = change_data id (inc_sh_time time)
        in
          log (sh_tag id ^ "succeeded (" ^ string_of_int time ^ ") [" ^
            prover_name ^ "]:\n" ^ msg)
        end
      else log (sh_tag id ^ "failed: " ^ msg)
  in change thm_names (K (Option.map snd result)) end

end


local

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

in

fun run_metis args thm_names id {pre=st, timeout, log, ...} =
  let
    fun get_thms ctxt = maps (thms_of_name ctxt)

    fun metis thms ctxt = MetisTools.metis_tac ctxt thms
    fun apply_metis thms = Mirabelle.can_apply timeout (metis thms) st

    fun with_time (false, t) = "failed (" ^ string_of_int t ^ ")"
      | with_time (true, t) = (change_data id inc_metis_success;
          change_data id (inc_metis_time t);
          "succeeded (" ^ string_of_int t ^ ")")
    fun timed_metis thms = with_time (Mirabelle.cpu_time apply_metis thms)
      handle TimeLimit.TimeOut => (change_data id inc_metis_timeout; "timeout")
           | ERROR msg => "error: " ^ msg

    val _ = log "-----"
    val _ = change_data id inc_metis_calls
  in
    thm_names
    |> get_thms (Proof.context_of st)
    |> timed_metis
    |> log o prefix (metis_tag id) 
  end

end


fun sledgehammer_action args id (st as {log, ...}) =
  let
    val thm_names = ref (NONE : string list option)
    val _ = Mirabelle.catch sh_tag (run_sledgehammer args thm_names) id st
  in
    if AList.defined (op =) args metisK andalso is_some (!thm_names)
    then Mirabelle.catch metis_tag (run_metis args (these (!thm_names))) id st
    else ()
  end

fun invoke args =
  let
    val _ = AtpManager.set_full_types (AList.defined (op =) args full_typesK)
  in Mirabelle.register (init, sledgehammer_action args, done) end

end
