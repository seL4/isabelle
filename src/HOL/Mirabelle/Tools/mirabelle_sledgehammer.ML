(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer.ML
    Author:     Jasmin Blanchette and Sascha Boehme and Tobias Nipkow, TU Munich
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

val proverK = "prover"
val prover_timeoutK = "prover_timeout"
val prover_hard_timeoutK = "prover_hard_timeout"
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
  lemmas: int,
  max_lems: int,
  time_isa: int,
  time_atp: int,
  time_atp_fail: int}

datatype me_data = MeData of {
  calls: int,
  success: int,
  proofs: int,
  time: int,
  timeout: int,
  lemmas: int,
  max_lems: int,
  posns: Position.T list
  }

datatype min_data = MinData of {
  succs: int,
  ab_ratios: int,
  it_ratios: int
  }

(* The first me_data component is only used if "minimize" is on.
   Then it records how metis behaves with un-minimized lemmas.
*)
datatype data = Data of sh_data * me_data * min_data * me_data

fun make_sh_data
      (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail) =
  ShData{calls=calls, success=success, lemmas=lemmas, max_lems=max_lems,
         time_isa=time_isa, time_atp=time_atp, time_atp_fail=time_atp_fail}

fun make_min_data (succs, ab_ratios, it_ratios) =
  MinData{succs=succs, ab_ratios=ab_ratios, it_ratios=it_ratios}

fun make_me_data (calls,success,proofs,time,timeout,lemmas,max_lems,posns) =
  MeData{calls=calls, success=success, proofs=proofs, time=time,
         timeout=timeout, lemmas=lemmas, max_lems=max_lems, posns=posns}

val empty_data =
  Data(make_sh_data (0, 0, 0, 0, 0, 0, 0),
       make_me_data(0, 0, 0, 0, 0, 0, 0, []),
       MinData{succs=0, ab_ratios=0, it_ratios=0},
       make_me_data(0, 0, 0, 0, 0, 0, 0, []))

fun map_sh_data f
    (Data(ShData{calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail},
          meda0, minda, meda)) =
  Data (make_sh_data (f (calls,success,lemmas,max_lems,
                         time_isa,time_atp,time_atp_fail)),
        meda0, minda, meda)

fun map_min_data f
  (Data(shda, meda0, MinData{succs,ab_ratios,it_ratios}, meda)) =
  Data(shda, meda0, make_min_data(f(succs,ab_ratios,it_ratios)), meda)

fun map_me_data0 f (Data (shda, MeData{calls,success,proofs,time,timeout,lemmas,max_lems,posns}, minda, meda)) =
  Data(shda, make_me_data(f (calls,success,proofs,time,timeout,lemmas,max_lems,posns)), minda, meda)

fun map_me_data f (Data (shda, meda0, minda, MeData{calls,success,proofs,time,timeout,lemmas,max_lems,posns})) =
  Data(shda, meda0, minda, make_me_data(f (calls,success,proofs,time,timeout,lemmas,max_lems,posns)))

val inc_sh_calls =  map_sh_data
  (fn (calls, success, lemmas,max_lems, time_isa, time_atp, time_atp_fail)
    => (calls + 1, success, lemmas,max_lems, time_isa, time_atp, time_atp_fail))

val inc_sh_success = map_sh_data
  (fn (calls, success, lemmas,max_lems, time_isa, time_atp, time_atp_fail)
    => (calls, success + 1, lemmas,max_lems, time_isa, time_atp, time_atp_fail))

fun inc_sh_lemmas n = map_sh_data
  (fn (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail)
    => (calls,success,lemmas+n,max_lems,time_isa,time_atp,time_atp_fail))

fun inc_sh_max_lems n = map_sh_data
  (fn (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail)
    => (calls,success,lemmas,Int.max(max_lems,n),time_isa,time_atp,time_atp_fail))

fun inc_sh_time_isa t = map_sh_data
  (fn (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail)
    => (calls,success,lemmas,max_lems,time_isa + t,time_atp,time_atp_fail))

fun inc_sh_time_atp t = map_sh_data
  (fn (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail)
    => (calls,success,lemmas,max_lems,time_isa,time_atp + t,time_atp_fail))

fun inc_sh_time_atp_fail t = map_sh_data
  (fn (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail)
    => (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail + t))

val inc_min_succs = map_min_data
  (fn (succs,ab_ratios,it_ratios) => (succs+1, ab_ratios, it_ratios))

fun inc_min_ab_ratios r = map_min_data
  (fn (succs, ab_ratios, it_ratios) => (succs, ab_ratios+r, it_ratios))

fun inc_min_it_ratios r = map_min_data
  (fn (succs, ab_ratios, it_ratios) => (succs, ab_ratios, it_ratios+r))

val inc_metis_calls = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls + 1, success, proofs, time, timeout, lemmas,max_lems,posns))

val inc_metis_success = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success + 1, proofs, time, timeout, lemmas,max_lems,posns))

val inc_metis_proofs = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs + 1, time, timeout, lemmas,max_lems,posns))

fun inc_metis_time t = map_me_data
 (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
  => (calls, success, proofs, time + t, timeout, lemmas,max_lems,posns))

val inc_metis_timeout = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs, time, timeout + 1, lemmas,max_lems,posns))

fun inc_metis_lemmas n = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs, time, timeout, lemmas+n, max_lems, posns))

fun inc_metis_max_lems n = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls,success,proofs,time,timeout,lemmas,Int.max(max_lems,n), posns))

fun inc_metis_posns pos = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs, time, timeout, lemmas,max_lems, pos::posns))

val inc_metis_calls0 = map_me_data0 
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls + 1, success, proofs, time, timeout, lemmas,max_lems,posns))

val inc_metis_success0 = map_me_data0
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success + 1, proofs, time, timeout, lemmas,max_lems,posns))

val inc_metis_proofs0 = map_me_data0
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs + 1, time, timeout, lemmas,max_lems,posns))

fun inc_metis_time0 t = map_me_data0
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs, time + t, timeout, lemmas,max_lems,posns))

val inc_metis_timeout0 = map_me_data0
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs, time, timeout + 1, lemmas,max_lems,posns))

fun inc_metis_lemmas0 n = map_me_data0
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs, time, timeout, lemmas+n, max_lems, posns))

fun inc_metis_max_lems0 n = map_me_data0
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls,success,proofs,time,timeout,lemmas,Int.max(max_lems,n), posns))

fun inc_metis_posns0 pos = map_me_data0
  (fn (calls,success,proofs,time,timeout,lemmas,max_lems,posns)
    => (calls, success, proofs, time, timeout, lemmas,max_lems, pos::posns))

local

val str = string_of_int
val str3 = Real.fmt (StringCvt.FIX (SOME 3))
fun percentage a b = string_of_int (a * 100 div b)
fun time t = Real.fromInt t / 1000.0
fun avg_time t n =
  if n > 0 then (Real.fromInt t / 1000.0) / Real.fromInt n else 0.0

fun log_sh_data log calls success lemmas max_lems time_isa time_atp time_atp_fail =
 (log ("Total number of sledgehammer calls: " ^ str calls);
  log ("Number of successful sledgehammer calls: " ^ str success);
  log ("Number of sledgehammer lemmas: " ^ str lemmas);
  log ("Max number of sledgehammer lemmas: " ^ str max_lems);
  log ("Success rate: " ^ percentage success calls ^ "%");
  log ("Total time for sledgehammer calls (Isabelle): " ^ str3 (time time_isa));
  log ("Total time for successful sledgehammer calls (ATP): " ^ str3 (time time_atp));
  log ("Total time for failed sledgehammer calls (ATP): " ^ str3 (time time_atp_fail));
  log ("Average time for sledgehammer calls (Isabelle): " ^
    str3 (avg_time time_isa calls));
  log ("Average time for successful sledgehammer calls (ATP): " ^
    str3 (avg_time time_atp success));
  log ("Average time for failed sledgehammer calls (ATP): " ^
    str3 (avg_time time_atp_fail (calls - success)))
  )


fun str_of_pos pos =
  let val str0 = string_of_int o the_default 0
  in str0 (Position.line_of pos) ^ ":" ^ str0 (Position.column_of pos) end

fun log_metis_data log tag sh_calls sh_success metis_calls metis_success metis_proofs metis_time
    metis_timeout metis_lemmas metis_max_lems metis_posns =
 (log ("Total number of " ^ tag ^ "metis calls: " ^ str metis_calls);
  log ("Number of successful " ^ tag ^ "metis calls: " ^ str metis_success ^
    " (proof: " ^ str metis_proofs ^ ")");
  log ("Number of " ^ tag ^ "metis timeouts: " ^ str metis_timeout);
  log ("Success rate: " ^ percentage metis_success sh_calls ^ "%");
  log ("Number of successful " ^ tag ^ "metis lemmas: " ^ str metis_lemmas);
  log ("Max number of successful " ^ tag ^ "metis lemmas: " ^ str metis_max_lems);
  log ("Total time for successful metis calls: " ^ str3 (time metis_time));
  log ("Average time for successful metis calls: " ^
    str3 (avg_time metis_time metis_success));
  if tag=""
  then log ("Proved: " ^ space_implode " " (map str_of_pos metis_posns))
  else ()
 )

fun log_min_data log succs ab_ratios it_ratios =
  (log ("Number of successful minimizations: " ^ string_of_int succs);
   log ("After/before ratios: " ^ string_of_int ab_ratios);
   log ("Iterations ratios: " ^ string_of_int it_ratios)
  )

in

fun log_data id log (Data
   (ShData{calls=sh_calls, lemmas=sh_lemmas,  max_lems=sh_max_lems, success=sh_success,
      time_isa=sh_time_isa,time_atp=sh_time_atp,time_atp_fail=sh_time_atp_fail},
    MeData{calls=metis_calls0, proofs=metis_proofs0,
      success=metis_success0, time=metis_time0, timeout=metis_timeout0,
      lemmas=metis_lemmas0,max_lems=metis_max_lems0,posns=metis_posns0},
    MinData{succs=min_succs, ab_ratios=ab_ratios, it_ratios=it_ratios},
    MeData{calls=metis_calls, proofs=metis_proofs,
      success=metis_success, time=metis_time, timeout=metis_timeout,
      lemmas=metis_lemmas,max_lems=metis_max_lems,posns=metis_posns})) =
  if sh_calls > 0
  then
   (log ("\n\n\nReport #" ^ string_of_int id ^ ":\n");
    log_sh_data log sh_calls sh_success sh_lemmas sh_max_lems sh_time_isa sh_time_atp sh_time_atp_fail;
    log "";
    if metis_calls > 0 then log_metis_data log "" sh_calls sh_success metis_calls
      metis_success metis_proofs metis_time metis_timeout metis_lemmas metis_max_lems metis_posns else ();
    log "";
    if metis_calls0 > 0
      then (log_min_data log min_succs ab_ratios it_ratios; log "";
            log_metis_data log "unminimized " sh_calls sh_success metis_calls0
              metis_success0 metis_proofs0 metis_time0 metis_timeout0 metis_lemmas0  metis_max_lems0 metis_posns0)
      else ()
   )
  else ()

end


(* Warning: we implicitly assume single-threaded execution here! *)
val data = Unsynchronized.ref ([] : (int * data) list)

fun init id thy = (Unsynchronized.change data (cons (id, empty_data)); thy)
fun done id ({log, ...}: Mirabelle.done_args) =
  AList.lookup (op =) (!data) id
  |> Option.map (log_data id log)
  |> K ()

fun change_data id f = (Unsynchronized.change data (AList.map_entry (op =) id f); ())


fun get_atp thy args =
  AList.lookup (op =) args proverK
  |> the_default (hd (space_explode " " (AtpManager.get_atps ())))
  |> (fn name => (name, the (AtpManager.get_prover name thy)))

local

datatype sh_result =
  SH_OK of int * int * string list |
  SH_FAIL of int * int |
  SH_ERROR

fun run_sh prover hard_timeout timeout dir st =
  let
    val (ctxt, goal) = Proof.get_goal st
    val ctxt' = ctxt |> is_some dir ? Config.put AtpWrapper.destdir (the dir)
    val atp = prover (AtpWrapper.atp_problem_of_goal
      (AtpManager.get_full_types ()) 1 (ctxt', goal))

    val time_limit =
      (case hard_timeout of
        NONE => I
      | SOME secs => TimeLimit.timeLimit (Time.fromSeconds secs))
    val (AtpWrapper.Prover_Result {success, message, theorem_names,
      runtime=time_atp, ...}, time_isa) =
      time_limit (Mirabelle.cpu_time atp) timeout
  in
    if success then (message, SH_OK (time_isa, time_atp, theorem_names))
    else (message, SH_FAIL(time_isa, time_atp))
  end
  handle ResHolClause.TOO_TRIVIAL => ("trivial", SH_OK (0, 0, []))
       | ERROR msg => ("error: " ^ msg, SH_ERROR)
       | TimeLimit.TimeOut => ("timeout", SH_ERROR)

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

fun run_sledgehammer args named_thms id ({pre=st, log, ...}: Mirabelle.run_args) =
  let
    val _ = change_data id inc_sh_calls
    val (prover_name, prover) = get_atp (Proof.theory_of st) args
    val dir = AList.lookup (op =) args keepK
    val timeout = Mirabelle.get_int_setting args (prover_timeoutK, 30)
    val hard_timeout = AList.lookup (op =) args prover_hard_timeoutK
      |> Option.map (fst o read_int o explode)
    val (msg, result) = run_sh prover hard_timeout timeout dir st
  in
    case result of
      SH_OK (time_isa, time_atp, names) =>
        let fun get_thms name = (name, thms_of_name (Proof.context_of st) name)
        in
          change_data id inc_sh_success;
          change_data id (inc_sh_lemmas (length names));
          change_data id (inc_sh_max_lems (length names));
          change_data id (inc_sh_time_isa time_isa);
          change_data id (inc_sh_time_atp time_atp);
          named_thms := SOME (map get_thms names);
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


fun run_minimize args named_thms id ({pre=st, log, ...}: Mirabelle.run_args) =
  let
    val n0 = length (these (!named_thms))
    val (prover_name, prover) = get_atp (Proof.theory_of st) args
    val minimize = AtpMinimal.minimalize prover prover_name
    val timeout =
      AList.lookup (op =) args minimize_timeoutK
      |> Option.map (fst o read_int o explode)
      |> the_default 5
    val _ = log separator
  in
    case minimize timeout st (these (!named_thms)) of
      (SOME (named_thms',its), msg) =>
        (change_data id inc_min_succs;
         change_data id (inc_min_ab_ratios ((100 * length named_thms') div n0));
         change_data id (inc_min_it_ratios ((100*its) div n0));
         if length named_thms' = n0
         then log (minimize_tag id ^ "already minimal")
         else (named_thms := SOME named_thms';
               log (minimize_tag id ^ "succeeded:\n" ^ msg))
        )
    | (NONE, msg) => log (minimize_tag id ^ "failed: " ^ msg)
  end


fun run_metis (inc_metis_calls, inc_metis_success, inc_metis_proofs, inc_metis_time, inc_metis_timeout,
    inc_metis_lemmas, inc_metis_max_lems, inc_metis_posns) args name named_thms id
    ({pre=st, timeout, log, pos, ...}: Mirabelle.run_args) =
  let
    fun metis thms ctxt = MetisTools.metis_tac ctxt thms
    fun apply_metis thms = Mirabelle.can_apply timeout (metis thms) st

    fun with_time (false, t) = "failed (" ^ string_of_int t ^ ")"
      | with_time (true, t) = (change_data id inc_metis_success;
          change_data id (inc_metis_lemmas (length named_thms));
          change_data id (inc_metis_max_lems (length named_thms));
          change_data id (inc_metis_time t);
          change_data id (inc_metis_posns pos);
          if name = "proof" then change_data id inc_metis_proofs else ();
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

fun sledgehammer_action args id (st as {log, pre, name, ...}: Mirabelle.run_args) =
  let val goal = Thm.major_prem_of(snd(snd(Proof.get_goal pre))) in
  if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal
  then () else
  let
    val metis_fns = (inc_metis_calls, inc_metis_success, inc_metis_proofs, inc_metis_time,
        inc_metis_timeout, inc_metis_lemmas,  inc_metis_max_lems, inc_metis_posns)
    val metis0_fns = (inc_metis_calls0, inc_metis_success0, inc_metis_proofs0, inc_metis_time0,
        inc_metis_timeout0, inc_metis_lemmas0, inc_metis_max_lems0, inc_metis_posns0)
    val named_thms = Unsynchronized.ref (NONE : (string * thm list) list option)
    val minimize = AList.defined (op =) args minimizeK
  in 
    Mirabelle.catch sh_tag (run_sledgehammer args named_thms) id st;
    if is_some (!named_thms)
      then
       (if minimize
          then Mirabelle.catch metis_tag (run_metis metis0_fns args name (these (!named_thms))) id st
          else ();
       if minimize andalso not(null(these(!named_thms)))
         then Mirabelle.catch minimize_tag (run_minimize args named_thms) id st
         else ();
       Mirabelle.catch metis_tag (run_metis metis_fns args name (these (!named_thms))) id st)
    else ()
  end
  end

fun invoke args =
  let
    val _ = AtpManager.set_full_types (AList.defined (op =) args full_typesK)
  in Mirabelle.register (init, sledgehammer_action args, done) end

end
