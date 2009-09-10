(* Title:  mirabelle_sledgehammer.ML
   Author: Jasmin Blanchette and Sascha Boehme and Tobias Nipkow
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

val proverK = "prover"
val prover_timeoutK = "prover_timeout"
val keepK = "keep"
val full_typesK = "full_types"
val minimizeK = "minimize"
val minimize_timeoutK = "minimize_timeout"

fun sh_tag id = "#" ^ string_of_int id ^ " sledgehammer: "
fun minimize_tag id = "#" ^ string_of_int id ^ " minimize (sledgehammer): "
fun metis_tag id = "#" ^ string_of_int id ^ " metis (sledgehammer): "

val separator = "-----"


datatype sh_data = ShData of {
  calls: int,
  success: int,
  time_isa: int,
  time_atp: int,
  time_atp_fail: int}

datatype me_data = MeData of {
  calls: int,
  success: int,
  time: int,
  timeout: int,
  lemmas: int
  }


(* The first me_data component is only used if "minimize" is on.
   Then it records how metis behaves with un-minimized lemmas.
*)
datatype data = Data of sh_data * me_data * me_data

fun make_sh_data (sh_calls, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail) =
  ShData{calls=sh_calls, success=sh_success, time_isa=sh_time_isa,
    time_atp=sh_time_atp, time_atp_fail=sh_time_atp_fail}

fun make_me_data (me_calls, me_success, me_time, me_timeout, me_lemmas) =
  MeData{calls=me_calls, success=me_success, time=me_time, timeout=me_timeout, lemmas=me_lemmas}

val empty_data = Data(make_sh_data (0, 0, 0, 0, 0), make_me_data(0, 0, 0, 0, 0), make_me_data(0, 0, 0, 0, 0))

fun map_sh_data f
  (Data (ShData{calls, success, time_isa, time_atp, time_atp_fail}, meda0, meda)) =
  Data (make_sh_data (f (calls, success, time_isa, time_atp, time_atp_fail)),
        meda0, meda)

fun map_me_data0 f (Data (shda, MeData{calls,success,time,timeout,lemmas}, meda)) =
  Data(shda, make_me_data(f (calls,success,time,timeout,lemmas)), meda)

fun map_me_data f (Data (shda, meda0, MeData{calls,success,time,timeout,lemmas})) =
  Data(shda, meda0, make_me_data(f (calls,success,time,timeout,lemmas)))

val inc_sh_calls = map_sh_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail)
  => (sh_calls + 1, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail))

val inc_sh_success = map_sh_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail)
  => (sh_calls, sh_success + 1, sh_time_isa, sh_time_atp, sh_time_atp_fail))

fun inc_sh_time_isa t = map_sh_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail)
  => (sh_calls, sh_success, sh_time_isa + t, sh_time_atp, sh_time_atp_fail))

fun inc_sh_time_atp t = map_sh_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail)
  => (sh_calls, sh_success, sh_time_isa, sh_time_atp + t, sh_time_atp_fail))

fun inc_sh_time_atp_fail t = map_sh_data (fn (sh_calls, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail)
  => (sh_calls, sh_success, sh_time_isa, sh_time_atp, sh_time_atp_fail + t))

val inc_metis_calls = map_me_data (fn (calls, success, time, timeout, lemmas)
  => (calls + 1, success, time, timeout, lemmas))

val inc_metis_success = map_me_data (fn (calls,success,time,timeout,lemmas)
  => (calls, success + 1, time, timeout, lemmas))

fun inc_metis_time t = map_me_data (fn (calls,success,time,timeout,lemmas)
  => (calls, success, time + t, timeout, lemmas))

val inc_metis_timeout = map_me_data (fn (calls,success,time,timeout,lemmas)
  => (calls, success, time, timeout + 1, lemmas))

fun inc_metis_lemmas n = map_me_data (fn (calls,success,time,timeout,lemmas)
  => (calls, success, time, timeout, lemmas + n))

val inc_metis_calls0 = map_me_data0 (fn (calls, success, time, timeout, lemmas)
  => (calls + 1, success, time, timeout, lemmas))

val inc_metis_success0 = map_me_data0 (fn (calls,success,time,timeout,lemmas)
  => (calls, success + 1, time, timeout, lemmas))

fun inc_metis_time0 t = map_me_data0 (fn (calls,success,time,timeout,lemmas)
  => (calls, success, time + t, timeout, lemmas))

val inc_metis_timeout0 = map_me_data0 (fn (calls,success,time,timeout,lemmas)
  => (calls, success, time, timeout + 1, lemmas))

fun inc_metis_lemmas0 n = map_me_data0 (fn (calls,success,time,timeout,lemmas)
  => (calls, success, time, timeout, lemmas + n))

local

val str = string_of_int
val str3 = Real.fmt (StringCvt.FIX (SOME 3))
fun percentage a b = string_of_int (a * 100 div b)
fun time t = Real.fromInt t / 1000.0
fun avg_time t n =
  if n > 0 then (Real.fromInt t / 1000.0) / Real.fromInt n else 0.0

fun log_sh_data log sh_calls sh_success sh_time_isa sh_time_atp sh_time_atp_fail =
 (log ("Total number of sledgehammer calls: " ^ str sh_calls);
  log ("Number of successful sledgehammer calls: " ^ str sh_success);
  log ("Success rate: " ^ percentage sh_success sh_calls ^ "%");
  log ("Total time for sledgehammer calls (Isabelle): " ^ str3 (time sh_time_isa));
  log ("Total time for successful sledgehammer calls (ATP): " ^ str3 (time sh_time_atp));
  log ("Total time for failed sledgehammer calls (ATP): " ^ str3 (time sh_time_atp_fail));
  log ("Average time for sledgehammer calls (Isabelle): " ^
    str3 (avg_time sh_time_isa sh_calls));
  log ("Average time for successful sledgehammer calls (ATP): " ^
    str3 (avg_time sh_time_atp sh_success));
  log ("Average time for failed sledgehammer calls (ATP): " ^
    str3 (avg_time sh_time_atp_fail (sh_calls - sh_success)))
  )

fun log_metis_data log tag sh_calls sh_success metis_calls metis_success metis_time
    metis_timeout metis_lemmas =
 (log ("Total number of " ^ tag ^ "metis calls: " ^ str metis_calls);
  log ("Number of successful " ^ tag ^ "metis calls: " ^ str metis_success);
  log ("Number of " ^ tag ^ "metis timeouts: " ^ str metis_timeout);
  log ("Number of " ^ tag ^ "metis exceptions: " ^
    str (sh_success - metis_success - metis_timeout));
  log ("Success rate: " ^ percentage metis_success sh_calls ^ "%");
  log ("Number of " ^ tag ^ "metis lemmas: " ^ str metis_lemmas);
  log ("Total time for successful metis calls: " ^ str3 (time metis_time));
  log ("Average time for successful metis calls: " ^
    str3 (avg_time metis_time metis_success)))

in

fun log_data id log (Data (ShData{calls=sh_calls, success=sh_success, time_isa=sh_time_isa, time_atp=sh_time_atp, time_atp_fail=sh_time_atp_fail}, MeData{calls=metis_calls0,
    success=metis_success0, time=metis_time0, timeout=metis_timeout0, lemmas=metis_lemmas0}, MeData{calls=metis_calls,
    success=metis_success, time=metis_time, timeout=metis_timeout, lemmas=metis_lemmas})) =
  if sh_calls > 0
  then
   (log ("\n\n\nReport #" ^ string_of_int id ^ ":\n");
    log_sh_data log sh_calls sh_success sh_time_isa sh_time_atp sh_time_atp_fail;
    log "";
    if metis_calls > 0 then log_metis_data log "" sh_calls sh_success metis_calls
      metis_success metis_time metis_timeout metis_lemmas else ();
    log "";
    if metis_calls0 > 0
      then log_metis_data log "unminimized " sh_calls sh_success metis_calls0
              metis_success0 metis_time0 metis_timeout0 metis_lemmas0
      else ()
   )
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

datatype sh_result =
  SH_OK of int * int * string list |
  SH_FAIL of int * int |
  SH_ERROR

fun run_sh (prover_name, prover) timeout st _ =
  let
    val atp = prover timeout NONE NONE prover_name 1
    val ((success, (message, thm_names), time_atp, _, _, _), time_isa) =
      Mirabelle.cpu_time atp (Proof.get_goal st)
  in
    if success then (message, SH_OK (time_isa, time_atp, thm_names))
    else (message, SH_FAIL(time_isa, time_atp))
  end
  handle ResHolClause.TOO_TRIVIAL => ("trivial", SH_OK (0, 0, []))
       | ERROR msg => ("error: " ^ msg, SH_ERROR)

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

fun run_sledgehammer args named_thms id {pre=st, log, ...} =
  let
    val _ = change_data id inc_sh_calls
    val atp as (prover_name, _) = get_atp (Proof.theory_of st) args
    val dir = AList.lookup (op =) args keepK
    val timeout = Mirabelle.get_int_setting args (prover_timeoutK, 30)
    val (msg, result) = safe init_sh done_sh (run_sh atp timeout st) dir
  in
    case result of
      SH_OK (time_isa, time_atp, names) =>
        let
          val _ = change_data id inc_sh_success
          val _ = change_data id (inc_sh_time_isa time_isa)
          val _ = change_data id (inc_sh_time_atp time_atp)

          fun get_thms name = (name, thms_of_name (Proof.context_of st) name)
          val _ = named_thms := SOME (map get_thms names)
        in
          log (sh_tag id ^ "succeeded (" ^ string_of_int time_isa ^ "+" ^
            string_of_int time_atp ^ ") [" ^ prover_name ^ "]:\n" ^ msg)
        end
    | SH_FAIL (time_isa, time_atp) =>
        let
          val _ = change_data id (inc_sh_time_isa time_isa)
          val _ = change_data id (inc_sh_time_atp_fail time_atp)
        in log (sh_tag id ^ "failed: " ^ msg) end
    | SH_ERROR => log (sh_tag id ^ "failed: " ^ msg)
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


fun run_metis (inc_metis_calls, inc_metis_success, inc_metis_time, inc_metis_timeout, inc_metis_lemmas) args named_thms id {pre=st, timeout, log, ...} =
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
    val _ = change_data id (inc_metis_lemmas (length named_thms))
  in
    maps snd named_thms
    |> timed_metis
    |> log o prefix (metis_tag id) 
  end

fun sledgehammer_action args id (st as {log, ...}) =
  let
    val metis_fns = (inc_metis_calls, inc_metis_success, inc_metis_time, inc_metis_timeout, inc_metis_lemmas)
    val metis0_fns = (inc_metis_calls0, inc_metis_success0, inc_metis_time0, inc_metis_timeout0, inc_metis_lemmas0)
    val named_thms = ref (NONE : (string * thm list) list option)

    fun if_enabled k f =
      if AList.defined (op =) args k andalso is_some (!named_thms)
      then f id st else ()

    val _ = Mirabelle.catch sh_tag (run_sledgehammer args named_thms) id st
    val _ = if_enabled minimizeK
      (Mirabelle.catch metis_tag (run_metis metis0_fns args (these (!named_thms))))
    val _ = if is_some (!named_thms)
      then Mirabelle.catch minimize_tag (run_minimize args named_thms) id st
      else ()
    val _ = if is_some (!named_thms)
      then Mirabelle.catch metis_tag (run_metis metis_fns args (these (!named_thms))) id st
      else ()
  in () end

fun invoke args =
  let
    val _ = AtpManager.set_full_types (AList.defined (op =) args full_typesK)
  in Mirabelle.register (init, sledgehammer_action args, done) end

end
