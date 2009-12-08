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
val metis_ftK = "metis_ft"

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
  lemmas: int * int * int,
  posns: Position.T list
  }

datatype min_data = MinData of {
  succs: int,
  ab_ratios: int,
  it_ratios: int
  }

fun make_sh_data
      (calls,success,lemmas,max_lems,time_isa,time_atp,time_atp_fail) =
  ShData{calls=calls, success=success, lemmas=lemmas, max_lems=max_lems,
         time_isa=time_isa, time_atp=time_atp, time_atp_fail=time_atp_fail}

fun make_min_data (succs, ab_ratios, it_ratios) =
  MinData{succs=succs, ab_ratios=ab_ratios, it_ratios=it_ratios}

fun make_me_data (calls,success,proofs,time,timeout,lemmas,posns) =
  MeData{calls=calls, success=success, proofs=proofs, time=time,
         timeout=timeout, lemmas=lemmas, posns=posns}

val empty_sh_data = make_sh_data (0, 0, 0, 0, 0, 0, 0)
val empty_min_data = make_min_data(0, 0, 0)
val empty_me_data = make_me_data(0, 0, 0, 0, 0, (0,0,0), [])

fun tuple_of_sh_data (ShData {calls, success, lemmas, max_lems, time_isa,
  time_atp, time_atp_fail}) = (calls, success, lemmas, max_lems, time_isa,
  time_atp, time_atp_fail)

fun tuple_of_min_data (MinData {succs, ab_ratios, it_ratios}) =
  (succs, ab_ratios, it_ratios)

fun tuple_of_me_data (MeData {calls, success, proofs, time, timeout, lemmas,
  posns}) = (calls, success, proofs, time, timeout, lemmas, posns)


datatype metis = Unminimized | Minimized | UnminimizedFT | MinimizedFT

datatype data = Data of {
  sh: sh_data,
  min: min_data,
  me_u: me_data, (* metis with unminimized set of lemmas *)
  me_m: me_data, (* metis with minimized set of lemmas *)
  me_uft: me_data, (* metis with unminimized set of lemmas and fully-typed *)
  me_mft: me_data, (* metis with minimized set of lemmas and fully-typed *)
  mini: bool   (* with minimization *)
  }

fun make_data (sh, min, me_u, me_m, me_uft, me_mft, mini) =
  Data {sh=sh, min=min, me_u=me_u, me_m=me_m, me_uft=me_uft, me_mft=me_mft,
    mini=mini}

val empty_data = make_data (empty_sh_data, empty_min_data,
  empty_me_data, empty_me_data, empty_me_data, empty_me_data, false)

fun map_sh_data f (Data {sh, min, me_u, me_m, me_uft, me_mft, mini}) =
  let val sh' = make_sh_data (f (tuple_of_sh_data sh))
  in make_data (sh', min, me_u, me_m, me_uft, me_mft, mini) end

fun map_min_data f (Data {sh, min, me_u, me_m, me_uft, me_mft, mini}) =
  let val min' = make_min_data (f (tuple_of_min_data min))
  in make_data (sh, min', me_u, me_m, me_uft, me_mft, mini) end

fun map_me_data f m (Data {sh, min, me_u, me_m, me_uft, me_mft, mini}) =
  let
    fun map_me g Unminimized   (u, m, uft, mft) = (g u, m, uft, mft)
      | map_me g Minimized     (u, m, uft, mft) = (u, g m, uft, mft)
      | map_me g UnminimizedFT (u, m, uft, mft) = (u, m, g uft, mft)
      | map_me g MinimizedFT   (u, m, uft, mft) = (u, m, uft, g mft)

    val f' = make_me_data o f o tuple_of_me_data

    val (me_u', me_m', me_uft', me_mft') =
      map_me f' m (me_u, me_m, me_uft, me_mft)
  in make_data (sh, min, me_u', me_m', me_uft', me_mft', mini) end

fun set_mini mini (Data {sh, min, me_u, me_m, me_uft, me_mft, ...}) =
  make_data (sh, min, me_u, me_m, me_uft, me_mft, mini)

fun inc_max (n:int) (s,sos,m) = (s+n, sos + n*n, Int.max(m,n));

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
  (fn (calls,success,proofs,time,timeout,lemmas,posns)
    => (calls + 1, success, proofs, time, timeout, lemmas,posns))

val inc_metis_success = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,posns)
    => (calls, success + 1, proofs, time, timeout, lemmas,posns))

val inc_metis_proofs = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,posns)
    => (calls, success, proofs + 1, time, timeout, lemmas,posns))

fun inc_metis_time m t = map_me_data
 (fn (calls,success,proofs,time,timeout,lemmas,posns)
  => (calls, success, proofs, time + t, timeout, lemmas,posns)) m

val inc_metis_timeout = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,posns)
    => (calls, success, proofs, time, timeout + 1, lemmas,posns))

fun inc_metis_lemmas m n = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,posns)
    => (calls, success, proofs, time, timeout, inc_max n lemmas, posns)) m

fun inc_metis_posns m pos = map_me_data
  (fn (calls,success,proofs,time,timeout,lemmas,posns)
    => (calls, success, proofs, time, timeout, lemmas, pos::posns)) m

local

val str = string_of_int
val str3 = Real.fmt (StringCvt.FIX (SOME 3))
fun percentage a b = string_of_int (a * 100 div b)
fun time t = Real.fromInt t / 1000.0
fun avg_time t n =
  if n > 0 then (Real.fromInt t / 1000.0) / Real.fromInt n else 0.0

fun log_sh_data log
    (calls, success, lemmas, max_lems, time_isa, time_atp, time_atp_fail) =
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

fun log_me_data log tag sh_calls (metis_calls, metis_success,
    metis_proofs, metis_time, metis_timeout, (lemmas, lems_sos, lems_max),
    metis_posns) =
 (log ("Total number of " ^ tag ^ "metis calls: " ^ str metis_calls);
  log ("Number of successful " ^ tag ^ "metis calls: " ^ str metis_success ^
    " (proof: " ^ str metis_proofs ^ ")");
  log ("Number of " ^ tag ^ "metis timeouts: " ^ str metis_timeout);
  log ("Success rate: " ^ percentage metis_success sh_calls ^ "%");
  log ("Number of successful " ^ tag ^ "metis lemmas: " ^ str lemmas);
  log ("SOS of successful " ^ tag ^ "metis lemmas: " ^ str lems_sos);
  log ("Max number of successful " ^ tag ^ "metis lemmas: " ^ str lems_max);
  log ("Total time for successful " ^ tag ^ "metis calls: " ^ str3 (time metis_time));
  log ("Average time for successful " ^ tag ^ "metis calls: " ^
    str3 (avg_time metis_time metis_success));
  if tag=""
  then log ("Proved: " ^ space_implode " " (map str_of_pos metis_posns))
  else ()
 )

fun log_min_data log (succs, ab_ratios, it_ratios) =
  (log ("Number of successful minimizations: " ^ string_of_int succs);
   log ("After/before ratios: " ^ string_of_int ab_ratios);
   log ("Iterations ratios: " ^ string_of_int it_ratios)
  )

in

fun log_data id log (Data {sh, min, me_u, me_m, me_uft, me_mft, mini}) =
  let
    val ShData {calls=sh_calls, ...} = sh

    fun app_if (MeData {calls, ...}) f = if calls > 0 then f () else ()
    fun log_me tag m =
      log_me_data log tag sh_calls (tuple_of_me_data m)
    fun log_metis (tag1, m1) (tag2, m2) = app_if m1 (fn () =>
      (log_me tag1 m1; log ""; app_if m2 (fn () => log_me tag2 m2)))
  in
    if sh_calls > 0
    then
     (log ("\n\n\nReport #" ^ string_of_int id ^ ":\n");
      log_sh_data log (tuple_of_sh_data sh);
      log "";
      if not mini
      then log_metis ("", me_u) ("fully-typed ", me_uft)
      else
        app_if me_u (fn () =>
         (log_metis ("unminimized ", me_u) ("unminimized fully-typed ", me_uft);
          log "";
          app_if me_m (fn () =>
            (log_min_data log (tuple_of_min_data min); log "";
             log_metis ("", me_m) ("fully-typed ", me_mft))))))
    else ()
  end

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
  let
    fun default_atp_name () = hd (ATP_Manager.get_atps ())
      handle Empty => error "No ATP available."
    fun get_prover name =
      (case ATP_Manager.get_prover thy name of
        SOME prover => (name, prover)
      | NONE => error ("Bad ATP: " ^ quote name))
  in
    (case AList.lookup (op =) args proverK of
      SOME name => get_prover name
    | NONE => get_prover (default_atp_name ()))
  end

local

datatype sh_result =
  SH_OK of int * int * string list |
  SH_FAIL of int * int |
  SH_ERROR

fun run_sh prover hard_timeout timeout dir st =
  let
    val {context = ctxt, facts, goal} = Proof.raw_goal st   (* FIXME ?? *)
    val change_dir = (fn SOME d => Config.put ATP_Wrapper.destdir d | _ => I)
    val ctxt' =
      ctxt
      |> change_dir dir
      |> Config.put ATP_Wrapper.measure_runtime true
    val problem = ATP_Wrapper.problem_of_goal (! ATP_Manager.full_types) 1 (ctxt', (facts, goal));

    val time_limit =
      (case hard_timeout of
        NONE => I
      | SOME secs => TimeLimit.timeLimit (Time.fromSeconds secs))
    val ({success, message, theorem_names, runtime=time_atp, ...}: ATP_Wrapper.prover_result,
        time_isa) = time_limit (Mirabelle.cpu_time (fn t => prover t problem)) timeout
  in
    if success then (message, SH_OK (time_isa, time_atp, theorem_names))
    else (message, SH_FAIL(time_isa, time_atp))
  end
  handle Res_HOL_Clause.TOO_TRIVIAL => ("trivial", SH_OK (0, 0, []))
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
    val minimize = ATP_Minimal.minimalize prover prover_name
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


fun run_metis full m name named_thms id
    ({pre=st, timeout, log, pos, ...}: Mirabelle.run_args) =
  let
    fun metis thms ctxt =
      if full then MetisTools.metisFT_tac ctxt thms
      else MetisTools.metis_tac ctxt thms
    fun apply_metis thms = Mirabelle.can_apply timeout (metis thms) st

    fun with_time (false, t) = "failed (" ^ string_of_int t ^ ")"
      | with_time (true, t) = (change_data id (inc_metis_success m);
          change_data id (inc_metis_lemmas m (length named_thms));
          change_data id (inc_metis_time m t);
          change_data id (inc_metis_posns m pos);
          if name = "proof" then change_data id (inc_metis_proofs m) else ();
          "succeeded (" ^ string_of_int t ^ ")")
    fun timed_metis thms = with_time (Mirabelle.cpu_time apply_metis thms)
      handle TimeLimit.TimeOut => (change_data id (inc_metis_timeout m); "timeout")
           | ERROR msg => "error: " ^ msg

    val _ = log separator
    val _ = change_data id (inc_metis_calls m)
  in
    maps snd named_thms
    |> timed_metis
    |> log o prefix (metis_tag id) 
  end

fun sledgehammer_action args id (st as {pre, name, ...}: Mirabelle.run_args) =
  let val goal = Thm.major_prem_of (#goal (Proof.raw_goal pre))  (* FIXME ?? *) in
  if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal
  then () else
  let
    val named_thms = Unsynchronized.ref (NONE : (string * thm list) list option)
    val minimize = AList.defined (op =) args minimizeK
    val metis_ft = AList.defined (op =) args metis_ftK

    fun apply_metis m1 m2 =
      if metis_ft
      then
        Mirabelle.app_timeout metis_tag
          (run_metis false m1 name (these (!named_thms)))
          (Mirabelle.catch metis_tag
            (run_metis true m2 name (these (!named_thms)))) id st
      else
        Mirabelle.catch metis_tag
          (run_metis false m1 name (these (!named_thms))) id st
  in 
    change_data id (set_mini minimize);
    Mirabelle.catch sh_tag (run_sledgehammer args named_thms) id st;
    if is_some (!named_thms)
    then
     (apply_metis Unminimized UnminimizedFT;
      if minimize andalso not (null (these (!named_thms)))
      then
       (Mirabelle.catch minimize_tag (run_minimize args named_thms) id st;
        apply_metis Minimized MinimizedFT)
      else ())
    else ()
  end
  end

fun invoke args =
  let
    val _ = ATP_Manager.full_types := AList.defined (op =) args full_typesK
  in Mirabelle.register (init, sledgehammer_action args, done) end

end
