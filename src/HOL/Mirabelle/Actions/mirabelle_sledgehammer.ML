(*  Title:      HOL/Mirabelle/Actions/mirabelle_sledgehammer.ML
    Author:     Jasmin Blanchette and Sascha Boehme and Tobias Nipkow, TU Munich
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

(*To facilitate synching the description of Mirabelle Sledgehammer parameters
 (in ../lib/Tools/mirabelle) with the parameters actually used by this
 interface, the former extracts PARAMETER and DESCRIPTION from code below which
 has this pattern (provided it appears in a single line):
   val .*K = "PARAMETER" (*DESCRIPTION*)
*)
(*NOTE: descriptions mention parameters (particularly NAME) without a defined range.*)
val proverK = "prover" (*=NAME: name of the external prover to call*)
val prover_timeoutK = "prover_timeout" (*=TIME: timeout for invoked ATP (seconds of process time)*)
val keepK = "keep" (*=PATH: path where to keep temporary files created by sledgehammer*)
val minimizeK = "minimize" (*: enable minimization of theorem set found by sledgehammer*)
                           (*refers to minimization attempted by Mirabelle*)
val minimize_timeoutK = "minimize_timeout" (*=TIME: timeout for each minimization step (seconds of*)

val reconstructorK = "reconstructor" (*=NAME: how to reconstruct proofs (ie. using metis/smt)*)
val metis_ftK = "metis_ft" (*: apply metis with fully-typed encoding to the theorems found by sledgehammer*)

val max_relevantK = "max_relevant" (*=NUM: max. relevant clauses to use*)
val max_callsK = "max_calls" (*=NUM: max. no. of calls to sledgehammer*)
val preplay_timeoutK = "preplay_timeout" (*=TIME: timeout for finding reconstructed proof*)
val sh_minimizeK = "sh_minimize" (*: instruct sledgehammer to run its minimizer*)

val check_trivialK = "check_trivial" (*: check if goals are "trivial" (false by default)*)
val type_encK = "type_enc" (*=STRING: type encoding scheme*)
val lam_transK = "lam_trans" (*=STRING: lambda translation scheme*)
val strictK = "strict" (*=BOOL: run in strict mode*)
val sliceK = "slice" (*=BOOL: allow sledgehammer-level strategy-scheduling*)
val uncurried_aliasesK = "uncurried_aliases" (*=SMART_BOOL: use fresh function names to alias curried applications*)
val e_selection_heuristicK = "e_selection_heuristic" (*: FIXME*)
val term_orderK = "term_order" (*: FIXME*)
val force_sosK = "force_sos" (*: use SOS*)
val max_new_mono_instancesK = "max_new_mono_instances" (*=NUM: max. new monomorphic instances*)
val max_mono_itersK = "max_mono_iters" (*=NUM: max. iterations of monomorphiser*)

fun sh_tag id = "#" ^ string_of_int id ^ " sledgehammer: "
fun minimize_tag id = "#" ^ string_of_int id ^ " minimize (sledgehammer): "
fun reconstructor_tag reconstructor id =
  "#" ^ string_of_int id ^ " " ^ (!reconstructor) ^ " (sledgehammer): "

val separator = "-----"

val preplay_timeout_default = "4"
(*FIXME sensible to have Mirabelle-level Sledgehammer defaults?*)

(*If a key is present in args then augment a list with its pair*)
(*This is used to avoid fixing default values at the Mirabelle level, and
  instead use the default values of the tool (Sledgehammer in this case).*)
fun available_parameter args key label list =
  let
    val value = AList.lookup (op =) args key
  in if is_some value then (label, the value) :: list else list end


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

val str0 = string_of_int o the_default 0

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
  str0 (Position.line_of pos) (* ^ ":" ^ str0 (Position.offset_of pos) *) ^
  (if triv then "[T]" else "")

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
      handle List.Empty => error "No ATP available."
    fun get_prover name =
      (name, Sledgehammer_Run.get_minimizing_prover ctxt
                Sledgehammer_Provers.Normal name)
  in
    (case AList.lookup (op =) args proverK of
      SOME name => get_prover name
    | NONE => get_prover (default_prover_name ()))
  end

type stature = ATP_Problem_Generate.stature

(* hack *)
fun reconstructor_from_msg args msg =
  (case AList.lookup (op =) args reconstructorK of
    SOME name => name
  | NONE =>
    if String.isSubstring "metis (" msg then
      msg |> Substring.full
          |> Substring.position "metis ("
          |> snd |> Substring.position ")"
          |> fst |> Substring.string
          |> suffix ")"
    else if String.isSubstring "metis" msg then
      "metis"
    else
      "smt")

local

datatype sh_result =
  SH_OK of int * int * (string * stature) list |
  SH_FAIL of int * int |
  SH_ERROR

fun run_sh prover_name prover type_enc strict max_relevant slice lam_trans
        uncurried_aliases e_selection_heuristic term_order force_sos
        hard_timeout timeout preplay_timeout sh_minimizeLST
        max_new_mono_instancesLST max_mono_itersLST dir pos st =
  let
    val {context = ctxt, facts = chained_ths, goal} = Proof.goal st
    val i = 1
    fun set_file_name (SOME dir) =
        Config.put Sledgehammer_Provers.dest_dir dir
        #> Config.put Sledgehammer_Provers.problem_prefix
          ("prob_" ^ str0 (Position.line_of pos) ^ "__")
        #> Config.put SMT_Config.debug_files
          (dir ^ "/" ^ Name.desymbolize false (ATP_Util.timestamp ()) ^ "_"
          ^ serial_string ())
      | set_file_name NONE = I
    val st' =
      st
      |> Proof.map_context
           (set_file_name dir
            #> (Option.map (Config.put ATP_Systems.e_selection_heuristic)
                  e_selection_heuristic |> the_default I)
            #> (Option.map (Config.put ATP_Systems.term_order)
                  term_order |> the_default I)
            #> (Option.map (Config.put ATP_Systems.force_sos)
                  force_sos |> the_default I))
    val params as {relevance_thresholds, max_relevant, slice, ...} =
      Sledgehammer_Isar.default_params ctxt
         ([("verbose", "true"),
           ("type_enc", type_enc),
           ("strict", strict),
           ("lam_trans", lam_trans |> the_default "smart"),
           ("uncurried_aliases", uncurried_aliases |> the_default "smart"),
           ("max_relevant", max_relevant),
           ("slice", slice),
           ("timeout", string_of_int timeout),
           ("preplay_timeout", preplay_timeout)]
          |> sh_minimizeLST (*don't confuse the two minimization flags*)
          |> max_new_mono_instancesLST
          |> max_mono_itersLST)
    val default_max_relevant =
      Sledgehammer_Provers.default_max_relevant_for_prover ctxt slice
        prover_name
    val is_appropriate_prop =
      Sledgehammer_Provers.is_appropriate_prop_for_prover ctxt prover_name
    val is_built_in_const =
      Sledgehammer_Provers.is_built_in_const_for_prover ctxt prover_name
    val relevance_fudge =
      Sledgehammer_Provers.relevance_fudge_for_prover ctxt prover_name
    val relevance_override = {add = [], del = [], only = false}
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal i
    val time_limit =
      (case hard_timeout of
        NONE => I
      | SOME secs => TimeLimit.timeLimit (Time.fromSeconds secs))
    fun failed failure =
      ({outcome = SOME failure, used_facts = [], run_time = Time.zeroTime,
        preplay =
          K (ATP_Proof_Reconstruct.Failed_to_Play Sledgehammer_Provers.plain_metis),
        message = K "", message_tail = ""}, ~1)
    val ({outcome, used_facts, run_time, preplay, message, message_tail}
         : Sledgehammer_Provers.prover_result,
        time_isa) = time_limit (Mirabelle.cpu_time (fn () =>
      let
        val _ = if is_appropriate_prop concl_t then ()
                else raise Fail "inappropriate"
        val ho_atp = Sledgehammer_Provers.is_ho_atp ctxt prover_name
        val facts =
          Sledgehammer_Filter.nearly_all_facts ctxt ho_atp relevance_override
            chained_ths hyp_ts concl_t
          |> filter (is_appropriate_prop o prop_of o snd)
          |> Sledgehammer_Filter.relevant_facts ctxt relevance_thresholds
                 (the_default default_max_relevant max_relevant)
                 is_built_in_const relevance_fudge relevance_override
                 chained_ths hyp_ts concl_t
        val problem =
          {state = st', goal = goal, subgoal = i,
           subgoal_count = Sledgehammer_Util.subgoal_count st,
           facts = facts |> map Sledgehammer_Provers.Untranslated_Fact,
           smt_filter = NONE}
      in prover params (K (K (K ""))) problem end)) ()
      handle TimeLimit.TimeOut => failed ATP_Proof.TimedOut
           | Fail "inappropriate" => failed ATP_Proof.Inappropriate
    val time_prover = run_time |> Time.toMilliseconds
    val msg = message (preplay ()) ^ message_tail
  in
    case outcome of
      NONE => (msg, SH_OK (time_isa, time_prover, used_facts))
    | SOME _ => (msg, SH_FAIL (time_isa, time_prover))
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

fun run_sledgehammer trivial args reconstructor named_thms id
      ({pre=st, log, pos, ...}: Mirabelle.run_args) =
  let
    val triv_str = if trivial then "[T] " else ""
    val _ = change_data id inc_sh_calls
    val _ = if trivial then () else change_data id inc_sh_nontriv_calls
    val (prover_name, prover) = get_prover (Proof.context_of st) args
    val type_enc = AList.lookup (op =) args type_encK |> the_default "smart"
    val strict = AList.lookup (op =) args strictK |> the_default "false"
    val max_relevant = AList.lookup (op =) args max_relevantK |> the_default "smart"
    val slice = AList.lookup (op =) args sliceK |> the_default "true"
    val lam_trans = AList.lookup (op =) args lam_transK
    val uncurried_aliases = AList.lookup (op =) args uncurried_aliasesK
    val e_selection_heuristic = AList.lookup (op =) args e_selection_heuristicK
    val term_order = AList.lookup (op =) args term_orderK
    val force_sos = AList.lookup (op =) args force_sosK
      |> Option.map (curry (op <>) "false")
    val dir = AList.lookup (op =) args keepK
    val timeout = Mirabelle.get_int_setting args (prover_timeoutK, 30)
    (* always use a hard timeout, but give some slack so that the automatic
       minimizer has a chance to do its magic *)
    val preplay_timeout = AList.lookup (op =) args preplay_timeoutK
      |> the_default preplay_timeout_default
    val sh_minimizeLST = available_parameter args sh_minimizeK "minimize"
    val max_new_mono_instancesLST =
      available_parameter args max_new_mono_instancesK max_new_mono_instancesK
    val max_mono_itersLST = available_parameter args max_mono_itersK max_mono_itersK
    val hard_timeout = SOME (2 * timeout)
    val (msg, result) =
      run_sh prover_name prover type_enc strict max_relevant slice lam_trans
        uncurried_aliases e_selection_heuristic term_order force_sos
        hard_timeout timeout preplay_timeout sh_minimizeLST
        max_new_mono_instancesLST max_mono_itersLST dir pos st
  in
    case result of
      SH_OK (time_isa, time_prover, names) =>
        let
          fun get_thms (name, stature) =
            try (thms_of_name (Proof.context_of st)) name
            |> Option.map (pair (name, stature))
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
    val type_enc = AList.lookup (op =) args type_encK |> the_default "smart"
    val strict = AList.lookup (op =) args strictK |> the_default "false"
    val timeout =
      AList.lookup (op =) args minimize_timeoutK
      |> Option.map (fst o read_int o raw_explode)  (* FIXME Symbol.explode (?) *)
      |> the_default 5
    val preplay_timeout = AList.lookup (op =) args preplay_timeoutK
      |> the_default preplay_timeout_default
    val sh_minimizeLST = available_parameter args sh_minimizeK "minimize"
    val max_new_mono_instancesLST =
      available_parameter args max_new_mono_instancesK max_new_mono_instancesK
    val max_mono_itersLST = available_parameter args max_mono_itersK max_mono_itersK
    val params = Sledgehammer_Isar.default_params ctxt
     ([("provers", prover_name),
       ("verbose", "true"),
       ("type_enc", type_enc),
       ("strict", strict),
       ("timeout", string_of_int timeout),
       ("preplay_timeout", preplay_timeout)]
      |> sh_minimizeLST (*don't confuse the two minimization flags*)
      |> max_new_mono_instancesLST
      |> max_mono_itersLST)
    val minimize =
      Sledgehammer_Minimize.minimize_facts prover_name params
          true 1 (Sledgehammer_Util.subgoal_count st)
    val _ = log separator
    val (used_facts, (preplay, message, message_tail)) =
      minimize st (these (!named_thms))
    val msg = message (preplay ()) ^ message_tail
  in
    case used_facts of
      SOME named_thms' =>
        (change_data id inc_min_succs;
         change_data id (inc_min_ab_ratios ((100 * length named_thms') div n0));
         if length named_thms' = n0
         then log (minimize_tag id ^ "already minimal")
         else (reconstructor := reconstructor_from_msg args msg;
               named_thms := SOME named_thms';
               log (minimize_tag id ^ "succeeded:\n" ^ msg))
        )
    | NONE => log (minimize_tag id ^ "failed: " ^ msg)
  end

fun override_params prover type_enc timeout =
  [("provers", prover),
   ("max_relevant", "0"),
   ("type_enc", type_enc),
   ("strict", "true"),
   ("slice", "false"),
   ("timeout", timeout |> Time.toSeconds |> string_of_int)]

fun run_reconstructor trivial full m name reconstructor named_thms id
    ({pre=st, timeout, log, pos, ...}: Mirabelle.run_args) =
  let
    fun do_reconstructor named_thms ctxt =
      let
        val ref_of_str =
          suffix ";" #> Outer_Syntax.scan Position.none #> Parse_Spec.xthm
          #> fst
        val thms = named_thms |> maps snd
        val facts = named_thms |> map (ref_of_str o fst o fst)
        val relevance_override = {add = facts, del = [], only = true}
        fun my_timeout time_slice =
          timeout |> Time.toReal |> curry Real.* time_slice |> Time.fromReal
        fun sledge_tac time_slice prover type_enc =
          Sledgehammer_Tactics.sledgehammer_as_oracle_tac ctxt
            (override_params prover type_enc (my_timeout time_slice))
            relevance_override
      in
        if !reconstructor = "sledgehammer_tac" then
          sledge_tac 0.2 ATP_Systems.z3_tptpN "mono_native"
          ORELSE' sledge_tac 0.2 ATP_Systems.eN "mono_guards??"
          ORELSE' sledge_tac 0.2 ATP_Systems.vampireN "mono_guards??"
          ORELSE' sledge_tac 0.2 ATP_Systems.spassN "poly_tags"
          ORELSE' Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN
            ctxt thms
        else if !reconstructor = "smt" then
          SMT_Solver.smt_tac ctxt thms
        else if full then
          Metis_Tactic.metis_tac [ATP_Proof_Reconstruct.full_typesN]
            ATP_Proof_Reconstruct.metis_default_lam_trans ctxt thms
        else if String.isPrefix "metis (" (!reconstructor) then
          let
            val (type_encs, lam_trans) =
              !reconstructor
              |> Outer_Syntax.scan Position.start
              |> filter Token.is_proper |> tl
              |> Metis_Tactic.parse_metis_options |> fst
              |>> the_default [ATP_Proof_Reconstruct.partial_typesN]
              ||> the_default ATP_Proof_Reconstruct.metis_default_lam_trans
          in Metis_Tactic.metis_tac type_encs lam_trans ctxt thms end
        else if !reconstructor = "metis" then
          Metis_Tactic.metis_tac [] ATP_Proof_Reconstruct.metis_default_lam_trans ctxt
            thms
        else
          K all_tac
      end
    fun apply_reconstructor named_thms =
      Mirabelle.can_apply timeout (do_reconstructor named_thms) st

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
    fun timed_reconstructor named_thms =
      (with_time (Mirabelle.cpu_time apply_reconstructor named_thms), true)
      handle TimeLimit.TimeOut => (change_data id (inc_reconstructor_timeout m);
               ("timeout", false))
           | ERROR msg => ("error: " ^ msg, false)

    val _ = log separator
    val _ = change_data id (inc_reconstructor_calls m)
    val _ = if trivial then ()
            else change_data id (inc_reconstructor_nontriv_calls m)
  in
    named_thms
    |> timed_reconstructor
    |>> log o prefix (reconstructor_tag reconstructor id)
    |> snd
  end

val try_timeout = seconds 5.0

(* crude hack *)
val num_sledgehammer_calls = Unsynchronized.ref 0

fun sledgehammer_action args id (st as {pre, name, ...}: Mirabelle.run_args) =
  let val goal = Thm.major_prem_of (#goal (Proof.goal pre)) in
    if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal
    then () else
    let
      val max_calls =
        AList.lookup (op =) args max_callsK |> the_default "10000000"
        |> Int.fromString |> the
      val _ = num_sledgehammer_calls := !num_sledgehammer_calls + 1;
    in
      if !num_sledgehammer_calls > max_calls then ()
      else
        let
          val reconstructor = Unsynchronized.ref ""
          val named_thms =
            Unsynchronized.ref (NONE : ((string * stature) * thm list) list option)
          val minimize = AList.defined (op =) args minimizeK
          val metis_ft = AList.defined (op =) args metis_ftK
          val trivial =
            if AList.lookup (op =) args check_trivialK |> the_default "false"
                            |> Bool.fromString |> the then
              Try0.try0 (SOME try_timeout) ([], [], [], []) pre
              handle TimeLimit.TimeOut => false
            else false
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
  end

fun invoke args =
  Mirabelle.register (init, sledgehammer_action args, done)

end
