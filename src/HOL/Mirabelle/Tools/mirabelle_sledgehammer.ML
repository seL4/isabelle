(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer.ML
    Author:     Jasmin Blanchette and Sascha Boehme and Tobias Nipkow, TU Munich
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

val proverK = "prover"
val prover_timeoutK = "prover_timeout"
val keepK = "keep"
val full_typesK = "full_types"
val type_sysK = "type_sys"
val max_relevantK = "max_relevant"
val minimizeK = "minimize"
val minimize_timeoutK = "minimize_timeout"
val metis_ftK = "metis_ft"
val reconstructorK = "reconstructor"

fun sh_tag id = "#" ^ string_of_int id ^ " sledgehammer: "
fun minimize_tag id = "#" ^ string_of_int id ^ " minimize (sledgehammer): "
fun reconstructor_tag reconstructor id =
  "#" ^ string_of_int id ^ " " ^ (!reconstructor) ^ " (sledgehammer): "

val separator = "-----"


datatype sh_data = ShData of {
  calls: int,
  success: int,
  nontriv_calls: int,
  nontriv_success: int,
  lemmas: int,
  max_lems: int,
  time_isa: int,
  time_prover: int,
  time_prover_fail: int}

datatype re_data = ReData of {
  calls: int,
  success: int,
  nontriv_calls: int,
  nontriv_success: int,
  proofs: int,
  time: int,
  timeout: int,
  lemmas: int * int * int,
  posns: (Position.T * bool) list
  }

datatype min_data = MinData of {
  succs: int,
  ab_ratios: int
  }

fun make_sh_data
      (calls,success,nontriv_calls,nontriv_success,lemmas,max_lems,time_isa,
       time_prover,time_prover_fail) =
  ShData{calls=calls, success=success, nontriv_calls=nontriv_calls,
         nontriv_success=nontriv_success, lemmas=lemmas, max_lems=max_lems,
         time_isa=time_isa, time_prover=time_prover,
         time_prover_fail=time_prover_fail}

fun make_min_data (succs, ab_ratios) =
  MinData{succs=succs, ab_ratios=ab_ratios}

fun make_re_data (calls,success,nontriv_calls,nontriv_success,proofs,time,
                  timeout,lemmas,posns) =
  ReData{calls=calls, success=success, nontriv_calls=nontriv_calls,
         nontriv_success=nontriv_success, proofs=proofs, time=time,
         timeout=timeout, lemmas=lemmas, posns=posns}

val empty_sh_data = make_sh_data (0, 0, 0, 0, 0, 0, 0, 0, 0)
val empty_min_data = make_min_data (0, 0)
val empty_re_data = make_re_data (0, 0, 0, 0, 0, 0, 0, (0,0,0), [])

fun tuple_of_sh_data (ShData {calls, success, nontriv_calls, nontriv_success,
                              lemmas, max_lems, time_isa,
  time_prover, time_prover_fail}) = (calls, success, nontriv_calls,
  nontriv_success, lemmas, max_lems, time_isa, time_prover, time_prover_fail)

fun tuple_of_min_data (MinData {succs, ab_ratios}) = (succs, ab_ratios)

fun tuple_of_re_data (ReData {calls, success, nontriv_calls, nontriv_success,
  proofs, time, timeout, lemmas, posns}) = (calls, success, nontriv_calls,
  nontriv_success, proofs, time, timeout, lemmas, posns)


datatype reconstructor_mode =
  Unminimized | Minimized | UnminimizedFT | MinimizedFT

datatype data = Data of {
  sh: sh_data,
  min: min_data,
  re_u: re_data, (* reconstructor with unminimized set of lemmas *)
  re_m: re_data, (* reconstructor with minimized set of lemmas *)
  re_uft: re_data, (* reconstructor with unminimized set of lemmas and fully-typed *)
  re_mft: re_data, (* reconstructor with minimized set of lemmas and fully-typed *)
  mini: bool   (* with minimization *)
  }

fun make_data (sh, min, re_u, re_m, re_uft, re_mft, mini) =
  Data {sh=sh, min=min, re_u=re_u, re_m=re_m, re_uft=re_uft, re_mft=re_mft,
    mini=mini}

val empty_data = make_data (empty_sh_data, empty_min_data,
  empty_re_data, empty_re_data, empty_re_data, empty_re_data, false)

fun map_sh_data f (Data {sh, min, re_u, re_m, re_uft, re_mft, mini}) =
  let val sh' = make_sh_data (f (tuple_of_sh_data sh))
  in make_data (sh', min, re_u, re_m, re_uft, re_mft, mini) end

fun map_min_data f (Data {sh, min, re_u, re_m, re_uft, re_mft, mini}) =
  let val min' = make_min_data (f (tuple_of_min_data min))
  in make_data (sh, min', re_u, re_m, re_uft, re_mft, mini) end

fun map_re_data f m (Data {sh, min, re_u, re_m, re_uft, re_mft, mini}) =
  let
    fun map_me g Unminimized   (u, m, uft, mft) = (g u, m, uft, mft)
      | map_me g Minimized     (u, m, uft, mft) = (u, g m, uft, mft)
      | map_me g UnminimizedFT (u, m, uft, mft) = (u, m, g uft, mft)
      | map_me g MinimizedFT   (u, m, uft, mft) = (u, m, uft, g mft)

    val f' = make_re_data o f o tuple_of_re_data

    val (re_u', re_m', re_uft', re_mft') =
      map_me f' m (re_u, re_m, re_uft, re_mft)
  in make_data (sh, min, re_u', re_m', re_uft', re_mft', mini) end

fun set_mini mini (Data {sh, min, re_u, re_m, re_uft, re_mft, ...}) =
  make_data (sh, min, re_u, re_m, re_uft, re_mft, mini)

fun inc_max (n:int) (s,sos,m) = (s+n, sos + n*n, Int.max(m,n));

val inc_sh_calls =  map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover, time_prover_fail)
    => (calls + 1, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover, time_prover_fail))

val inc_sh_success = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover, time_prover_fail)
    => (calls, success + 1, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover, time_prover_fail))

val inc_sh_nontriv_calls =  map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover, time_prover_fail)
    => (calls, success, nontriv_calls + 1, nontriv_success, lemmas, max_lems, time_isa, time_prover, time_prover_fail))

val inc_sh_nontriv_success = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover, time_prover_fail)
    => (calls, success, nontriv_calls, nontriv_success + 1, lemmas,max_lems, time_isa, time_prover, time_prover_fail))

fun inc_sh_lemmas n = map_sh_data
  (fn (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa,time_prover,time_prover_fail)
    => (calls,success,nontriv_calls, nontriv_success, lemmas+n,max_lems,time_isa,time_prover,time_prover_fail))

fun inc_sh_max_lems n = map_sh_data
  (fn (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa,time_prover,time_prover_fail)
    => (calls,success,nontriv_calls, nontriv_success, lemmas,Int.max(max_lems,n),time_isa,time_prover,time_prover_fail))

fun inc_sh_time_isa t = map_sh_data
  (fn (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa,time_prover,time_prover_fail)
    => (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa + t,time_prover,time_prover_fail))

fun inc_sh_time_prover t = map_sh_data
  (fn (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa,time_prover,time_prover_fail)
    => (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa,time_prover + t,time_prover_fail))

fun inc_sh_time_prover_fail t = map_sh_data
  (fn (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa,time_prover,time_prover_fail)
    => (calls,success,nontriv_calls, nontriv_success, lemmas,max_lems,time_isa,time_prover,time_prover_fail + t))

val inc_min_succs = map_min_data
  (fn (succs,ab_ratios) => (succs+1, ab_ratios))

fun inc_min_ab_ratios r = map_min_data
  (fn (succs, ab_ratios) => (succs, ab_ratios+r))

val inc_reconstructor_calls = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls + 1, success, nontriv_calls, nontriv_success, proofs, time, timeout, lemmas,posns))

val inc_reconstructor_success = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success + 1, nontriv_calls, nontriv_success, proofs, time, timeout, lemmas,posns))

val inc_reconstructor_nontriv_calls = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls + 1, nontriv_success, proofs, time, timeout, lemmas,posns))

val inc_reconstructor_nontriv_success = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success + 1, proofs, time, timeout, lemmas,posns))

val inc_reconstructor_proofs = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs + 1, time, timeout, lemmas,posns))

fun inc_reconstructor_time m t = map_re_data
 (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
  => (calls, success, nontriv_calls, nontriv_success, proofs, time + t, timeout, lemmas,posns)) m

val inc_reconstructor_timeout = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs, time, timeout + 1, lemmas,posns))

fun inc_reconstructor_lemmas m n = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs, time, timeout, inc_max n lemmas, posns)) m

fun inc_reconstructor_posns m pos = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs, time, timeout, lemmas, pos::posns)) m

local

val str = string_of_int
val str3 = Real.fmt (StringCvt.FIX (SOME 3))
fun percentage a b = string_of_int (a * 100 div b)
fun time t = Real.fromInt t / 1000.0
fun avg_time t n =
  if n > 0 then (Real.fromInt t / 1000.0) / Real.fromInt n else 0.0

fun log_sh_data log
    (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover, time_prover_fail) =
 (log ("Total number of sledgehammer calls: " ^ str calls);
  log ("Number of successful sledgehammer calls: " ^ str success);
  log ("Number of sledgehammer lemmas: " ^ str lemmas);
  log ("Max number of sledgehammer lemmas: " ^ str max_lems);
  log ("Success rate: " ^ percentage success calls ^ "%");
  log ("Total number of nontrivial sledgehammer calls: " ^ str nontriv_calls);
  log ("Number of successful nontrivial sledgehammer calls: " ^ str nontriv_success);
  log ("Total time for sledgehammer calls (Isabelle): " ^ str3 (time time_isa));
  log ("Total time for successful sledgehammer calls (ATP): " ^ str3 (time time_prover));
  log ("Total time for failed sledgehammer calls (ATP): " ^ str3 (time time_prover_fail));
  log ("Average time for sledgehammer calls (Isabelle): " ^
    str3 (avg_time time_isa calls));
  log ("Average time for successful sledgehammer calls (ATP): " ^
    str3 (avg_time time_prover success));
  log ("Average time for failed sledgehammer calls (ATP): " ^
    str3 (avg_time time_prover_fail (calls - success)))
  )


fun str_of_pos (pos, triv) =
  let val str0 = string_of_int o the_default 0
  in
    str0 (Position.line_of pos) ^ ":" ^ str0 (Position.column_of pos) ^
    (if triv then "[T]" else "")
  end

fun log_re_data log tag sh_calls (re_calls, re_success, re_nontriv_calls,
     re_nontriv_success, re_proofs, re_time, re_timeout,
    (lemmas, lems_sos, lems_max), re_posns) =
 (log ("Total number of " ^ tag ^ "reconstructor calls: " ^ str re_calls);
  log ("Number of successful " ^ tag ^ "reconstructor calls: " ^ str re_success ^
    " (proof: " ^ str re_proofs ^ ")");
  log ("Number of " ^ tag ^ "reconstructor timeouts: " ^ str re_timeout);
  log ("Success rate: " ^ percentage re_success sh_calls ^ "%");
  log ("Total number of nontrivial " ^ tag ^ "reconstructor calls: " ^ str re_nontriv_calls);
  log ("Number of successful nontrivial " ^ tag ^ "reconstructor calls: " ^ str re_nontriv_success ^
    " (proof: " ^ str re_proofs ^ ")");
  log ("Number of successful " ^ tag ^ "reconstructor lemmas: " ^ str lemmas);
  log ("SOS of successful " ^ tag ^ "reconstructor lemmas: " ^ str lems_sos);
  log ("Max number of successful " ^ tag ^ "reconstructor lemmas: " ^ str lems_max);
  log ("Total time for successful " ^ tag ^ "reconstructor calls: " ^ str3 (time re_time));
  log ("Average time for successful " ^ tag ^ "reconstructor calls: " ^
    str3 (avg_time re_time re_success));
  if tag=""
  then log ("Proved: " ^ space_implode " " (map str_of_pos re_posns))
  else ()
 )

fun log_min_data log (succs, ab_ratios) =
  (log ("Number of successful minimizations: " ^ string_of_int succs);
   log ("After/before ratios: " ^ string_of_int ab_ratios)
  )

in

fun log_data id log (Data {sh, min, re_u, re_m, re_uft, re_mft, mini}) =
  let
    val ShData {calls=sh_calls, ...} = sh

    fun app_if (ReData {calls, ...}) f = if calls > 0 then f () else ()
    fun log_re tag m =
      log_re_data log tag sh_calls (tuple_of_re_data m)
    fun log_reconstructor (tag1, m1) (tag2, m2) = app_if m1 (fn () =>
      (log_re tag1 m1; log ""; app_if m2 (fn () => log_re tag2 m2)))
  in
    if sh_calls > 0
    then
     (log ("\n\n\nReport #" ^ string_of_int id ^ ":\n");
      log_sh_data log (tuple_of_sh_data sh);
      log "";
      if not mini
      then log_reconstructor ("", re_u) ("fully-typed ", re_uft)
      else
        app_if re_u (fn () =>
         (log_reconstructor ("unminimized ", re_u) ("unminimized fully-typed ", re_uft);
          log "";
          app_if re_m (fn () =>
            (log_min_data log (tuple_of_min_data min); log "";
             log_reconstructor ("", re_m) ("fully-typed ", re_mft))))))
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


fun get_prover ctxt args =
  let
    fun default_prover_name () =
      hd (#provers (Sledgehammer_Isar.default_params ctxt []))
      handle Empty => error "No ATP available."
    fun get_prover name =
      (name, Sledgehammer_Run.get_minimizing_prover ctxt false name)
  in
    (case AList.lookup (op =) args proverK of
      SOME name => get_prover name
    | NONE => get_prover (default_prover_name ()))
  end

type locality = Sledgehammer_Filter.locality

(* hack *)
fun reconstructor_from_msg args msg =
  (case AList.lookup (op =) args reconstructorK of
    SOME name => name
  | NONE =>
    if String.isSubstring "metisFT" msg then "metisFT"
    else if String.isSubstring "metis" msg then "metis"
    else "smt")

local

datatype sh_result =
  SH_OK of int * int * (string * locality) list |
  SH_FAIL of int * int |
  SH_ERROR

fun run_sh prover_name prover type_sys max_relevant hard_timeout timeout dir st =
  let
    val {context = ctxt, facts = chained_ths, goal} = Proof.goal st
    val i = 1
    fun change_dir (SOME dir) =
        Config.put Sledgehammer_Provers.dest_dir dir
        #> Config.put SMT_Config.debug_files
          (dir ^ "/" ^ Name.desymbolize false (ATP_Problem.timestamp ()) ^ "_"
          ^ serial_string ())
      | change_dir NONE = I
    val st' =
      st |> Proof.map_context
                (change_dir dir
                 #> Config.put Sledgehammer_Provers.measure_run_time true)
    val params as {type_sys, relevance_thresholds, max_relevant, slicing, ...} =
      Sledgehammer_Isar.default_params ctxt
          [("verbose", "true"),
           ("type_sys", type_sys),
           ("max_relevant", max_relevant),
           ("timeout", string_of_int timeout)]
    val default_max_relevant =
      Sledgehammer_Provers.default_max_relevant_for_prover ctxt slicing
        prover_name
    val is_built_in_const =
      Sledgehammer_Provers.is_built_in_const_for_prover ctxt prover_name
    val relevance_fudge =
      Sledgehammer_Provers.relevance_fudge_for_prover ctxt prover_name
    val relevance_override = {add = [], del = [], only = false}
    val (_, hyp_ts, concl_t) = Sledgehammer_Util.strip_subgoal goal i
    val fairly_sound =
      Sledgehammer_Provers.is_rich_type_sys_fairly_sound type_sys
    val time_limit =
      (case hard_timeout of
        NONE => I
      | SOME secs => TimeLimit.timeLimit (Time.fromSeconds secs))
    val ({outcome, message, used_facts, run_time_in_msecs}
         : Sledgehammer_Provers.prover_result,
        time_isa) = time_limit (Mirabelle.cpu_time (fn () =>
      let
        val facts =
          Sledgehammer_Filter.relevant_facts ctxt fairly_sound
              relevance_thresholds
              (the_default default_max_relevant max_relevant) is_built_in_const
              relevance_fudge relevance_override chained_ths hyp_ts concl_t
        val problem =
          {state = st', goal = goal, subgoal = i,
           subgoal_count = Sledgehammer_Util.subgoal_count st,
           facts = facts |> map Sledgehammer_Provers.Untranslated_Fact,
           smt_filter = NONE}
      in prover params (K "") problem end)) ()
      handle TimeLimit.TimeOut =>
             ({outcome = SOME ATP_Proof.TimedOut, message = "", used_facts = [],
               run_time_in_msecs = NONE}, ~1)
    val time_prover = run_time_in_msecs |> the_default ~1
  in
    case outcome of
      NONE => (message, SH_OK (time_isa, time_prover, used_facts))
    | SOME _ => (message, SH_FAIL (time_isa, time_prover))
  end
  handle ERROR msg => ("error: " ^ msg, SH_ERROR)

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (Proof_Context.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source
    |> Token.source {do_recover=SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse_Spec.xthms1 >> get) NONE
    |> Source.exhaust
  end

in

fun run_sledgehammer trivial args reconstructor named_thms id ({pre=st, log, ...}: Mirabelle.run_args) =
  let
    val triv_str = if trivial then "[T] " else ""
    val _ = change_data id inc_sh_calls
    val _ = if trivial then () else change_data id inc_sh_nontriv_calls
    val (prover_name, prover) = get_prover (Proof.context_of st) args
    val type_sys = AList.lookup (op =) args type_sysK |> the_default "smart"
    val max_relevant = AList.lookup (op =) args max_relevantK |> the_default "smart"
    val dir = AList.lookup (op =) args keepK
    val timeout = Mirabelle.get_int_setting args (prover_timeoutK, 30)
    (* always use a hard timeout, but give some slack so that the automatic
       minimizer has a chance to do its magic *)
    val hard_timeout = SOME (2 * timeout)
    val (msg, result) =
      run_sh prover_name prover type_sys max_relevant hard_timeout timeout dir st
  in
    case result of
      SH_OK (time_isa, time_prover, names) =>
        let
          fun get_thms (_, Sledgehammer_Filter.Chained) = NONE
            | get_thms (name, loc) =
              SOME ((name, loc), thms_of_name (Proof.context_of st) name)
        in
          change_data id inc_sh_success;
          if trivial then () else change_data id inc_sh_nontriv_success;
          change_data id (inc_sh_lemmas (length names));
          change_data id (inc_sh_max_lems (length names));
          change_data id (inc_sh_time_isa time_isa);
          change_data id (inc_sh_time_prover time_prover);
          reconstructor := reconstructor_from_msg args msg;
          named_thms := SOME (map_filter get_thms names);
          log (sh_tag id ^ triv_str ^ "succeeded (" ^ string_of_int time_isa ^ "+" ^
            string_of_int time_prover ^ ") [" ^ prover_name ^ "]:\n" ^ msg)
        end
    | SH_FAIL (time_isa, time_prover) =>
        let
          val _ = change_data id (inc_sh_time_isa time_isa)
          val _ = change_data id (inc_sh_time_prover_fail time_prover)
        in log (sh_tag id ^ triv_str ^ "failed: " ^ msg) end
    | SH_ERROR => log (sh_tag id ^ "failed: " ^ msg)
  end

end

fun run_minimize args reconstructor named_thms id
        ({pre=st, log, ...}: Mirabelle.run_args) =
  let
    val ctxt = Proof.context_of st
    val n0 = length (these (!named_thms))
    val (prover_name, _) = get_prover ctxt args
    val type_sys = AList.lookup (op =) args type_sysK |> the_default "smart"
    val timeout =
      AList.lookup (op =) args minimize_timeoutK
      |> Option.map (fst o read_int o raw_explode)  (* FIXME Symbol.explode (?) *)
      |> the_default 5
    val params as {explicit_apply, ...} = Sledgehammer_Isar.default_params ctxt
      [("provers", prover_name),
       ("verbose", "true"),
       ("type_sys", type_sys),
       ("timeout", string_of_int timeout)]
    val minimize =
      Sledgehammer_Minimize.minimize_facts prover_name params
          (SOME explicit_apply) true 1 (Sledgehammer_Util.subgoal_count st)
    val _ = log separator
  in
    case minimize st (these (!named_thms)) of
      (SOME named_thms', msg) =>
        (change_data id inc_min_succs;
         change_data id (inc_min_ab_ratios ((100 * length named_thms') div n0));
         if length named_thms' = n0
         then log (minimize_tag id ^ "already minimal")
         else (reconstructor := reconstructor_from_msg args msg;
               named_thms := SOME named_thms';
               log (minimize_tag id ^ "succeeded:\n" ^ msg))
        )
    | (NONE, msg) => log (minimize_tag id ^ "failed: " ^ msg)
  end


fun run_reconstructor trivial full m name reconstructor named_thms id
    ({pre=st, timeout, log, pos, ...}: Mirabelle.run_args) =
  let
    fun do_reconstructor thms ctxt =
      (if !reconstructor = "sledgehammer_tac" then
         (fn ctxt => fn thms =>
            Method.insert_tac thms THEN'
            Sledgehammer_Tactics.sledgehammer_as_unsound_oracle_tac ctxt)
       else if !reconstructor = "smt" then
         SMT_Solver.smt_tac
       else if full orelse !reconstructor = "metisFT" then
         Metis_Tactics.metisFT_tac
       else
         Metis_Tactics.metis_tac) ctxt thms
    fun apply_reconstructor thms =
      Mirabelle.can_apply timeout (do_reconstructor thms) st

    fun with_time (false, t) = "failed (" ^ string_of_int t ^ ")"
      | with_time (true, t) = (change_data id (inc_reconstructor_success m);
          if trivial then ()
          else change_data id (inc_reconstructor_nontriv_success m);
          change_data id (inc_reconstructor_lemmas m (length named_thms));
          change_data id (inc_reconstructor_time m t);
          change_data id (inc_reconstructor_posns m (pos, trivial));
          if name = "proof" then change_data id (inc_reconstructor_proofs m)
          else ();
          "succeeded (" ^ string_of_int t ^ ")")
    fun timed_reconstructor thms =
      (with_time (Mirabelle.cpu_time apply_reconstructor thms), true)
      handle TimeLimit.TimeOut => (change_data id (inc_reconstructor_timeout m);
               ("timeout", false))
           | ERROR msg => ("error: " ^ msg, false)

    val _ = log separator
    val _ = change_data id (inc_reconstructor_calls m)
    val _ = if trivial then ()
            else change_data id (inc_reconstructor_nontriv_calls m)
  in
    maps snd named_thms
    |> timed_reconstructor
    |>> log o prefix (reconstructor_tag reconstructor id)
    |> snd
  end

val try_timeout = seconds 5.0

fun sledgehammer_action args id (st as {pre, name, ...}: Mirabelle.run_args) =
  let val goal = Thm.major_prem_of (#goal (Proof.goal pre)) in
    if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal
    then () else
    let
      val reconstructor = Unsynchronized.ref ""
      val named_thms =
        Unsynchronized.ref (NONE : ((string * locality) * thm list) list option)
      val minimize = AList.defined (op =) args minimizeK
      val metis_ft = AList.defined (op =) args metis_ftK
      val trivial = Try.invoke_try (SOME try_timeout) ([], [], [], []) pre
        handle TimeLimit.TimeOut => false
      fun apply_reconstructor m1 m2 =
        if metis_ft
        then
          if not (Mirabelle.catch_result (reconstructor_tag reconstructor) false
              (run_reconstructor trivial false m1 name reconstructor
                   (these (!named_thms))) id st)
          then
            (Mirabelle.catch_result (reconstructor_tag reconstructor) false
              (run_reconstructor trivial true m2 name reconstructor
                   (these (!named_thms))) id st; ())
          else ()
        else
          (Mirabelle.catch_result (reconstructor_tag reconstructor) false
            (run_reconstructor trivial false m1 name reconstructor
                 (these (!named_thms))) id st; ())
    in 
      change_data id (set_mini minimize);
      Mirabelle.catch sh_tag (run_sledgehammer trivial args reconstructor
                                               named_thms) id st;
      if is_some (!named_thms)
      then
       (apply_reconstructor Unminimized UnminimizedFT;
        if minimize andalso not (null (these (!named_thms)))
        then
         (Mirabelle.catch minimize_tag
              (run_minimize args reconstructor named_thms) id st;
          apply_reconstructor Minimized MinimizedFT)
        else ())
      else ()
    end
  end

fun invoke args =
  let
    val _ = Sledgehammer_Isar.full_types := AList.defined (op =) args full_typesK
  in Mirabelle.register (init, sledgehammer_action args, done) end

end
