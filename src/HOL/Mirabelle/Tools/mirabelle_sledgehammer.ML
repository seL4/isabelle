(* Title:  mirabelle_sledgehammer.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

val proverK = "prover"
val keepK = "keep"
val metisK = "metis"
val full_typesK = "full_types"
val minimizeK = "minimize"
val minimize_timeoutK = "minimize_timeout"

fun sh_tag id = "#" ^ string_of_int id ^ " sledgehammer: "
fun minimize_tag id = "#" ^ string_of_int id ^ " minimize (sledgehammer): "
fun metis_tag id = "#" ^ string_of_int id ^ " metis (sledgehammer): "

val separator = "-----"


datatype data = Data of {
  sh_calls: int,
  sh_success: int,
  sh_time_isa: int,
  sh_time_atp: int,
  metis_calls: int,
  metis_success: int,
  metis_time: int,
  metis_timeout: int }

fun make_data (sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls, metis_success,
    metis_time, metis_timeout) =
  Data {sh_calls=sh_calls, sh_success=sh_success, sh_time_isa=sh_time_isa,
    sh_time_atp=sh_time_atp,
    metis_calls=metis_calls, metis_success=metis_success,
    metis_time=metis_time, metis_timeout=metis_timeout}

fun map_data f (Data {sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls,
    metis_success, metis_time, metis_timeout}) =
  make_data (f (sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls, metis_success,
    metis_time, metis_timeout))

val empty_data = make_data (0, 0, 0, 0, 0, 0, 0, 0)

val inc_sh_calls = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls + 1, sh_success,
  sh_time_isa, sh_time_atp, metis_calls, metis_success, metis_time, metis_timeout))

val inc_sh_success = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls, sh_success + 1,
  sh_time_isa, sh_time_atp, metis_calls, metis_success, metis_time, metis_timeout))

fun inc_sh_time_isa t = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls, sh_success,
  sh_time_isa + t, sh_time_atp, metis_calls, metis_success, metis_time, metis_timeout))

fun inc_sh_time_atp t = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls, sh_success,
  sh_time_isa, sh_time_atp + t, metis_calls, metis_success, metis_time, metis_timeout))

val inc_metis_calls = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls,
  metis_success, metis_time, metis_timeout) => (sh_calls, sh_success,
  sh_time_isa, sh_time_atp, metis_calls + 1, metis_success, metis_time, metis_timeout))

val inc_metis_success = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp,
  metis_calls, metis_success, metis_time, metis_timeout) => (sh_calls,
  sh_success, sh_time_isa, sh_time_atp, metis_calls, metis_success + 1, metis_time,
  metis_timeout))

fun inc_metis_time t = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp,
  metis_calls, metis_success, metis_time, metis_timeout) => (sh_calls,
  sh_success, sh_time_isa, sh_time_atp, metis_calls, metis_success, metis_time + t,
  metis_timeout))

val inc_metis_timeout = map_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp,
  metis_calls, metis_success, metis_time, metis_timeout) => (sh_calls,
  sh_success, sh_time_isa, sh_time_atp, metis_calls, metis_success, metis_time,
  metis_timeout + 1))


local

val str = string_of_int
val str3 = Real.fmt (StringCvt.FIX (SOME 3))
fun percentage a b = string_of_int (a * 100 div b)
fun time t = Real.fromInt t / 1000.0
fun avg_time t n =
  if n > 0 then (Real.fromInt t / 1000.0) / Real.fromInt n else 0.0

fun log_sh_data log sh_calls sh_success sh_time_isa sh_time_atp =
 (log ("Total number of sledgehammer calls: " ^ str sh_calls);
  log ("Number of successful sledgehammer calls: " ^ str sh_success);
  log ("Success rate: " ^ percentage sh_success sh_calls ^ "%");
  log ("Total time for successful sledgehammer calls (Isabelle): " ^ str3 (time sh_time_isa));
  log ("Total time for successful sledgehammer calls (ATP): " ^ str3 (time sh_time_atp));
  log ("Average time for successful sledgehammer calls (Isabelle): " ^
    str3 (avg_time sh_time_isa sh_success));
  log ("Average time for successful sledgehammer calls (ATP): " ^
    str3 (avg_time sh_time_atp sh_success))
  )

fun log_metis_data log sh_calls sh_success metis_calls metis_success metis_time
    metis_timeout =
 (log ("Total number of metis calls: " ^ str metis_calls);
  log ("Number of successful metis calls: " ^ str metis_success);
  log ("Number of metis timeouts: " ^ str metis_timeout);
  log ("Number of metis exceptions: " ^
    str (sh_success - metis_success - metis_timeout));
  log ("Success rate: " ^ percentage metis_success sh_calls ^ "%");
  log ("Total time for successful metis calls: " ^ str3 (time metis_time));
  log ("Average time for successful metis calls: " ^
    str3 (avg_time metis_time metis_success)))

in

fun log_data id log (Data {sh_calls, sh_success, sh_time_isa, sh_time_atp, metis_calls,
    metis_success, metis_time, metis_timeout}) =
  if sh_calls > 0
  then
   (log ("\n\n\nReport #" ^ string_of_int id ^ ":\n");
    log_sh_data log sh_calls sh_success sh_time_isa sh_time_atp;
    log "";
    if metis_calls > 0 then log_metis_data log sh_calls sh_success metis_calls
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


fun get_atp thy args =
  AList.lookup (op =) args proverK
  |> the_default (hd (space_explode " " (AtpManager.get_atps ())))
  |> (fn name => (name, the (AtpManager.get_prover name thy)))

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

fun run_sh (prover_name, prover) timeout st _ =
  let
    val atp = prover (Time.toSeconds timeout) NONE NONE prover_name 1
    val ((success, (message, thm_names), atp_time, _, _, _), sh_time) =
      Mirabelle.cpu_time atp (Proof.get_goal st)
  in
    if success then (message, SOME (atp_time, sh_time, thm_names))
    else (message, NONE)
  end
  handle ResHolClause.TOO_TRIVIAL => ("trivial", SOME (0, 0, []))
       | ERROR msg => ("error: " ^ msg, NONE)

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

fun run_sledgehammer args named_thms id {pre=st, timeout, log, ...} =
  let
    val _ = change_data id inc_sh_calls 
    val atp as (prover_name, _) = get_atp (Proof.theory_of st) args
    val dir = AList.lookup (op =) args keepK
    val (msg, result) = safe init_sh done_sh (run_sh atp timeout st) dir
  in
    (case result of
      SOME (atp_time, sh_time, names) =>
        let
          val _ = change_data id inc_sh_success
          val _ = change_data id (inc_sh_time_isa sh_time)
          val _ = change_data id (inc_sh_time_atp atp_time)

          fun get_thms name = (name, thms_of_name (Proof.context_of st) name)
          val _ = named_thms := SOME (map get_thms names)
        in
          log (sh_tag id ^ "succeeded (" ^ string_of_int atp_time ^ "+" ^
            string_of_int sh_time ^ ") [" ^ prover_name ^ "]:\n" ^ msg)
        end
    | NONE => log (sh_tag id ^ "failed: " ^ msg))
  end

end


fun run_minimize args named_thms id {pre=st, log, ...} =
  let
    val (prover_name, prover) = get_atp (Proof.theory_of st) args
    val minimize = AtpMinimal.minimalize prover prover_name
    val timeout =
      AList.lookup (op =) args minimize_timeoutK
      |> Option.map (fst o read_int o explode)
      |> the_default 5
    val _ = log separator
  in
    (case minimize timeout st (these (!named_thms)) of
      (SOME named_thms', msg) =>
        if length named_thms' = length (these (!named_thms))
        then log (minimize_tag id ^ "already minimal")
        else
         (named_thms := SOME named_thms';
          log (minimize_tag id ^ "succeeded:\n" ^ msg))
    | (NONE, msg) => log (minimize_tag id ^ "failed: " ^ msg))
  end


fun run_metis args named_thms id {pre=st, timeout, log, ...} =
  let
    fun metis thms ctxt = MetisTools.metis_tac ctxt thms
    fun apply_metis thms = Mirabelle.can_apply timeout (metis thms) st

    fun with_time (false, t) = "failed (" ^ string_of_int t ^ ")"
      | with_time (true, t) = (change_data id inc_metis_success;
          change_data id (inc_metis_time t);
          "succeeded (" ^ string_of_int t ^ ")")
    fun timed_metis thms = with_time (Mirabelle.cpu_time apply_metis thms)
      handle TimeLimit.TimeOut => (change_data id inc_metis_timeout; "timeout")
           | ERROR msg => "error: " ^ msg

    val _ = log separator
    val _ = change_data id inc_metis_calls
  in
    maps snd named_thms
    |> timed_metis
    |> log o prefix (metis_tag id) 
  end


fun sledgehammer_action args id (st as {log, ...}) =
  let
    val named_thms = ref (NONE : (string * thm list) list option)

    fun if_enabled k f =
      if AList.defined (op =) args k andalso is_some (!named_thms)
      then f id st else ()

    val _ = Mirabelle.catch sh_tag (run_sledgehammer args named_thms) id st
    val _ = if_enabled minimizeK
      (Mirabelle.catch minimize_tag (run_minimize args named_thms))
    val _ = if_enabled metisK
      (Mirabelle.catch metis_tag (run_metis args (these (!named_thms))))
  in () end

fun invoke args =
  let
    val args = (metisK,"yes") :: args; (* always enable metis *)
    val _ = AtpManager.set_full_types (AList.defined (op =) args full_typesK)
  in Mirabelle.register (init, sledgehammer_action args, done) end

end
