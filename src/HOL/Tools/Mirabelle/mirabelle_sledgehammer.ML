(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer.ML
    Author:     Jasmin Blanchette and Sascha Boehme and Tobias Nipkow, TU Munich

Mirabelle action: "sledgehammer".
*)

structure Mirabelle_Sledgehammer : MIRABELLE_ACTION =
struct

(*To facilitate synching the description of Mirabelle Sledgehammer parameters
 (in ../lib/Tools/mirabelle) with the parameters actually used by this
 interface, the former extracts PARAMETER and DESCRIPTION from code below which
 has this pattern (provided it appears in a single line):
   val .*K = "PARAMETER" (*DESCRIPTION*)
*)
(* NOTE: Do not forget to update the Sledgehammer documentation to reflect changes here. *)

val check_trivialK = "check_trivial" (*=BOOL: check if goals are "trivial"*)
val e_selection_heuristicK = "e_selection_heuristic" (*=STRING: E clause selection heuristic*)
val fact_filterK = "fact_filter" (*=STRING: fact filter*)
val force_sosK = "force_sos" (*=BOOL: use set-of-support (in Vampire)*)
val isar_proofsK = "isar_proofs" (*=SMART_BOOL: enable Isar proof generation*)
val keepK = "keep" (*=PATH: path where to keep temporary files created by sledgehammer*)
val lam_transK = "lam_trans" (*=STRING: lambda translation scheme*)
val max_callsK = "max_calls" (*=NUM: max. no. of calls to sledgehammer*)
val max_factsK = "max_facts" (*=NUM: max. relevant clauses to use*)
val max_mono_itersK = "max_mono_iters" (*=NUM: max. iterations of monomorphiser*)
val max_new_mono_instancesK = "max_new_mono_instances" (*=NUM: max. new monomorphic instances*)
val max_relevantK = "max_relevant" (*=NUM: max. relevant clauses to use*)
val minimizeK = "minimize" (*=BOOL: instruct sledgehammer to run its minimizer*)
val preplay_timeoutK = "preplay_timeout" (*=TIME: timeout for finding reconstructed proof*)
val proof_methodK = "proof_method" (*=STRING: how to reconstruct proofs (ie. using metis/smt)*)
val proverK = "prover" (*=STRING: name of the external prover to call*)
val prover_timeoutK = "prover_timeout" (*=TIME: timeout for invoked ATP (seconds of process time)*)
val sliceK = "slice" (*=BOOL: allow sledgehammer-level strategy-scheduling*)
val smt_proofsK = "smt_proofs" (*=BOOL: enable SMT proof generation*)
val strictK = "strict" (*=BOOL: run in strict mode*)
val strideK = "stride" (*=NUM: run every nth goal*)
val term_orderK = "term_order" (*=STRING: term order (in E)*)
val type_encK = "type_enc" (*=STRING: type encoding scheme*)
val uncurried_aliasesK = "uncurried_aliases" (*=SMART_BOOL: use fresh function names to alias curried applications*)

fun sh_tag id = "#" ^ string_of_int id ^ " sledgehammer: "
fun proof_method_tag meth id = "#" ^ string_of_int id ^ " " ^ (!meth) ^ " (sledgehammer): "

val separator = "-----"

(*FIXME sensible to have Mirabelle-level Sledgehammer defaults?*)
(*defaults used in this Mirabelle action*)
val preplay_timeout_default = "1"
val lam_trans_default = "smart"
val uncurried_aliases_default = "smart"
val fact_filter_default = "smart"
val type_enc_default = "smart"
val strict_default = "false"
val stride_default = 1
val max_facts_default = "smart"
val slice_default = "true"
val max_calls_default = 10000000
val check_trivial_default = false

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

fun make_sh_data
      (calls,success,nontriv_calls,nontriv_success,lemmas,max_lems,time_isa,
       time_prover,time_prover_fail) =
  ShData{calls=calls, success=success, nontriv_calls=nontriv_calls,
         nontriv_success=nontriv_success, lemmas=lemmas, max_lems=max_lems,
         time_isa=time_isa, time_prover=time_prover,
         time_prover_fail=time_prover_fail}

fun make_re_data (calls,success,nontriv_calls,nontriv_success,proofs,time,
                  timeout,lemmas,posns) =
  ReData{calls=calls, success=success, nontriv_calls=nontriv_calls,
         nontriv_success=nontriv_success, proofs=proofs, time=time,
         timeout=timeout, lemmas=lemmas, posns=posns}

val empty_sh_data = make_sh_data (0, 0, 0, 0, 0, 0, 0, 0, 0)
val empty_re_data = make_re_data (0, 0, 0, 0, 0, 0, 0, (0,0,0), [])

fun tuple_of_sh_data (ShData {calls, success, nontriv_calls, nontriv_success,
                              lemmas, max_lems, time_isa,
  time_prover, time_prover_fail}) = (calls, success, nontriv_calls,
  nontriv_success, lemmas, max_lems, time_isa, time_prover, time_prover_fail)

fun tuple_of_re_data (ReData {calls, success, nontriv_calls, nontriv_success,
  proofs, time, timeout, lemmas, posns}) = (calls, success, nontriv_calls,
  nontriv_success, proofs, time, timeout, lemmas, posns)

datatype data = Data of {
  sh: sh_data,
  re_u: re_data (* proof method with unminimized set of lemmas *)
  }

fun make_data (sh, re_u) = Data {sh=sh, re_u=re_u}

val empty_data = make_data (empty_sh_data, empty_re_data)

fun map_sh_data f (Data {sh, re_u}) =
  let val sh' = make_sh_data (f (tuple_of_sh_data sh))
  in make_data (sh', re_u) end

fun map_re_data f (Data {sh, re_u}) =
  let
    val f' = make_re_data o f o tuple_of_re_data
    val re_u' = f' re_u
  in make_data (sh, re_u') end

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

val inc_proof_method_calls = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls + 1, success, nontriv_calls, nontriv_success, proofs, time, timeout, lemmas,posns))

val inc_proof_method_success = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success + 1, nontriv_calls, nontriv_success, proofs, time, timeout, lemmas,posns))

val inc_proof_method_nontriv_calls = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls + 1, nontriv_success, proofs, time, timeout, lemmas,posns))

val inc_proof_method_nontriv_success = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success + 1, proofs, time, timeout, lemmas,posns))

val inc_proof_method_proofs = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs + 1, time, timeout, lemmas,posns))

fun inc_proof_method_time t = map_re_data
 (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
  => (calls, success, nontriv_calls, nontriv_success, proofs, time + t, timeout, lemmas,posns))

val inc_proof_method_timeout = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs, time, timeout + 1, lemmas,posns))

fun inc_proof_method_lemmas n = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs, time, timeout, inc_max n lemmas, posns))

fun inc_proof_method_posns pos = map_re_data
  (fn (calls,success,nontriv_calls, nontriv_success, proofs,time,timeout,lemmas,posns)
    => (calls, success, nontriv_calls, nontriv_success, proofs, time, timeout, lemmas, pos::posns))

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
  str0 (Position.line_of pos) ^ ":" ^ str0 (Position.offset_of pos) ^
  (if triv then "[T]" else "")

fun log_re_data log tag sh_calls (re_calls, re_success, re_nontriv_calls,
     re_nontriv_success, re_proofs, re_time, re_timeout,
    (lemmas, lems_sos, lems_max), re_posns) =
 (log ("Total number of " ^ tag ^ "proof method calls: " ^ str re_calls);
  log ("Number of successful " ^ tag ^ "proof method calls: " ^ str re_success ^
    " (proof: " ^ str re_proofs ^ ")");
  log ("Number of " ^ tag ^ "proof method timeouts: " ^ str re_timeout);
  log ("Success rate: " ^ percentage re_success sh_calls ^ "%");
  log ("Total number of nontrivial " ^ tag ^ "proof method calls: " ^ str re_nontriv_calls);
  log ("Number of successful nontrivial " ^ tag ^ "proof method calls: " ^ str re_nontriv_success ^
    " (proof: " ^ str re_proofs ^ ")");
  log ("Number of successful " ^ tag ^ "proof method lemmas: " ^ str lemmas);
  log ("SOS of successful " ^ tag ^ "proof method lemmas: " ^ str lems_sos);
  log ("Max number of successful " ^ tag ^ "proof method lemmas: " ^ str lems_max);
  log ("Total time for successful " ^ tag ^ "proof method calls: " ^ str3 (time re_time));
  log ("Average time for successful " ^ tag ^ "proof method calls: " ^
    str3 (avg_time re_time re_success));
  if tag=""
  then log ("Proved: " ^ space_implode " " (map str_of_pos re_posns))
  else ()
 )

in

fun log_data id log (Data {sh, re_u}) =
  let
    val ShData {calls=sh_calls, ...} = sh

    fun app_if (ReData {calls, ...}) f = if calls > 0 then f () else ()
    fun log_re tag m =
      log_re_data log tag sh_calls (tuple_of_re_data m)
    fun log_proof_method (tag1, m1) = app_if m1 (fn () => (log_re tag1 m1; log ""))
  in
    if sh_calls > 0
    then
     (log ("\n\n\nReport #" ^ string_of_int id ^ ":\n");
      log_sh_data log (tuple_of_sh_data sh);
      log "";
      log_proof_method ("", re_u))
    else ()
  end

end

(* Warning: we implicitly assume single-threaded execution here *)
val data = Unsynchronized.ref ([] : (int * data) list)

fun init id thy = (Unsynchronized.change data (cons (id, empty_data)); thy)
fun done id ({log, ...}: Mirabelle.done_args) =
  AList.lookup (op =) (!data) id
  |> Option.map (log_data id log)
  |> K ()

fun change_data id f = (Unsynchronized.change data (AList.map_entry (op =) id f); ())

fun get_prover_name thy args =
  let
    fun default_prover_name () =
      hd (#provers (Sledgehammer_Commands.default_params thy []))
      handle List.Empty => error "No ATP available"
  in
    (case AList.lookup (op =) args proverK of
      SOME name => name
    | NONE => default_prover_name ())
  end

fun get_prover ctxt name params goal =
  let
    val learn = Sledgehammer_MaSh.mash_learn_proof ctxt params (Thm.prop_of goal)
  in
    Sledgehammer_Prover_Minimize.get_minimizing_prover ctxt Sledgehammer_Prover.Normal learn name
  end

type stature = ATP_Problem_Generate.stature

fun is_good_line s =
  (String.isSubstring " ms)" s orelse String.isSubstring " s)" s)
  andalso not (String.isSubstring "(> " s)
  andalso not (String.isSubstring ", > " s)
  andalso not (String.isSubstring "may fail" s)

(* Fragile hack *)
fun proof_method_from_msg args msg =
  (case AList.lookup (op =) args proof_methodK of
    SOME name =>
    if name = "smart" then
      if exists is_good_line (split_lines msg) then
        "none"
      else
        "fail"
    else
      name
  | NONE =>
    if exists is_good_line (split_lines msg) then
      "none" (* trust the preplayed proof *)
    else if String.isSubstring "metis (" msg then
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

fun run_sh prover_name fact_filter type_enc strict max_facts slice
      lam_trans uncurried_aliases e_selection_heuristic term_order force_sos
      hard_timeout timeout preplay_timeout isar_proofsLST smt_proofsLST
      minimizeLST max_new_mono_instancesLST max_mono_itersLST dir pos st =
  let
    val thy = Proof.theory_of st
    val {context = ctxt, facts = chained_ths, goal} = Proof.goal st
    val i = 1
    fun set_file_name (SOME dir) =
        Config.put Sledgehammer_Prover_ATP.atp_dest_dir dir
        #> Config.put Sledgehammer_Prover_ATP.atp_problem_prefix
          ("prob_" ^ str0 (Position.line_of pos) ^ "__")
        #> Config.put SMT_Config.debug_files
          (dir ^ "/" ^ Name.desymbolize (SOME false) (ATP_Util.timestamp ()) ^ "_"
          ^ serial_string ())
      | set_file_name NONE = I
    val st' =
      st
      |> Proof.map_context
           (set_file_name dir
            #> (Option.map (Config.put Sledgehammer_ATP_Systems.e_selection_heuristic)
                  e_selection_heuristic |> the_default I)
            #> (Option.map (Config.put Sledgehammer_ATP_Systems.term_order)
                  term_order |> the_default I)
            #> (Option.map (Config.put Sledgehammer_ATP_Systems.force_sos)
                  force_sos |> the_default I))
    val params as {max_facts, minimize, preplay_timeout, ...} =
      Sledgehammer_Commands.default_params thy
         ([(* ("verbose", "true"), *)
           ("fact_filter", fact_filter),
           ("type_enc", type_enc),
           ("strict", strict),
           ("lam_trans", lam_trans |> the_default lam_trans_default),
           ("uncurried_aliases", uncurried_aliases |> the_default uncurried_aliases_default),
           ("max_facts", max_facts),
           ("slice", slice),
           ("timeout", string_of_int timeout),
           ("preplay_timeout", preplay_timeout)]
          |> isar_proofsLST
          |> smt_proofsLST
          |> minimizeLST (*don't confuse the two minimization flags*)
          |> max_new_mono_instancesLST
          |> max_mono_itersLST)
    val default_max_facts =
      Sledgehammer_Prover_Minimize.default_max_facts_of_prover ctxt prover_name
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal i ctxt
    val time_limit =
      (case hard_timeout of
        NONE => I
      | SOME secs => Timeout.apply (Time.fromSeconds secs))
    fun failed failure =
      ({outcome = SOME failure, used_facts = [], used_from = [],
        preferred_methss = (Sledgehammer_Proof_Methods.Auto_Method, []), run_time = Time.zeroTime,
        message = K ""}, ~1)
    val ({outcome, used_facts, preferred_methss, run_time, message, ...}
         : Sledgehammer_Prover.prover_result,
         time_isa) = time_limit (Mirabelle.cpu_time (fn () =>
      let
        val ho_atp = Sledgehammer_Prover_ATP.is_ho_atp ctxt prover_name
        val keywords = Thy_Header.get_keywords' ctxt
        val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
        val facts =
          Sledgehammer_Fact.nearly_all_facts ctxt ho_atp
              Sledgehammer_Fact.no_fact_override keywords css_table chained_ths
              hyp_ts concl_t
        val factss =
          facts
          |> Sledgehammer_MaSh.relevant_facts ctxt params prover_name
                 (the_default default_max_facts max_facts)
                 Sledgehammer_Fact.no_fact_override hyp_ts concl_t
          |> tap (fn factss =>
                     "Line " ^ str0 (Position.line_of pos) ^ ": " ^
                     Sledgehammer.string_of_factss factss
                     |> writeln)
        val prover = get_prover ctxt prover_name params goal
        val problem =
          {comment = "", state = st', goal = goal, subgoal = i,
           subgoal_count = Sledgehammer_Util.subgoal_count st, factss = factss, found_proof = I}
      in prover params problem end)) ()
      handle Timeout.TIMEOUT _ => failed ATP_Proof.TimedOut
           | Fail "inappropriate" => failed ATP_Proof.Inappropriate
    val time_prover = run_time |> Time.toMilliseconds
    val msg = message (fn () => Sledgehammer.play_one_line_proof minimize preplay_timeout used_facts
      st' i preferred_methss)
  in
    (case outcome of
      NONE => (msg, SH_OK (time_isa, time_prover, used_facts))
    | SOME _ => (msg, SH_FAIL (time_isa, time_prover)))
  end
  handle ERROR msg => ("error: " ^ msg, SH_ERROR)

in

fun run_sledgehammer trivial args proof_method named_thms id
      ({pre=st, log, pos, ...}: Mirabelle.run_args) =
  let
    val thy = Proof.theory_of st
    val triv_str = if trivial then "[T] " else ""
    val _ = change_data id inc_sh_calls
    val _ = if trivial then () else change_data id inc_sh_nontriv_calls
    val prover_name = get_prover_name thy args
    val fact_filter = AList.lookup (op =) args fact_filterK |> the_default fact_filter_default
    val type_enc = AList.lookup (op =) args type_encK |> the_default type_enc_default
    val strict = AList.lookup (op =) args strictK |> the_default strict_default
    val max_facts =
      (case AList.lookup (op =) args max_factsK of
        SOME max => max
      | NONE =>
        (case AList.lookup (op =) args max_relevantK of
          SOME max => max
        | NONE => max_facts_default))
    val slice = AList.lookup (op =) args sliceK |> the_default slice_default
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
    val isar_proofsLST = available_parameter args isar_proofsK "isar_proofs"
    val smt_proofsLST = available_parameter args smt_proofsK "smt_proofs"
    val minimizeLST = available_parameter args minimizeK "minimize"
    val max_new_mono_instancesLST =
      available_parameter args max_new_mono_instancesK max_new_mono_instancesK
    val max_mono_itersLST = available_parameter args max_mono_itersK max_mono_itersK
    val hard_timeout = SOME (4 * timeout)
    val (msg, result) =
      run_sh prover_name fact_filter type_enc strict max_facts slice lam_trans
        uncurried_aliases e_selection_heuristic term_order force_sos
        hard_timeout timeout preplay_timeout isar_proofsLST smt_proofsLST
        minimizeLST max_new_mono_instancesLST max_mono_itersLST dir pos st
  in
    (case result of
      SH_OK (time_isa, time_prover, names) =>
        let
          fun get_thms (name, stature) =
            try (Sledgehammer_Util.thms_of_name (Proof.context_of st))
              name
            |> Option.map (pair (name, stature))
        in
          change_data id inc_sh_success;
          if trivial then () else change_data id inc_sh_nontriv_success;
          change_data id (inc_sh_lemmas (length names));
          change_data id (inc_sh_max_lems (length names));
          change_data id (inc_sh_time_isa time_isa);
          change_data id (inc_sh_time_prover time_prover);
          proof_method := proof_method_from_msg args msg;
          named_thms := SOME (map_filter get_thms names);
          log (sh_tag id ^ triv_str ^ "succeeded (" ^ string_of_int time_isa ^ "+" ^
            string_of_int time_prover ^ ") [" ^ prover_name ^ "]:\n" ^ msg)
        end
    | SH_FAIL (time_isa, time_prover) =>
        let
          val _ = change_data id (inc_sh_time_isa time_isa)
          val _ = change_data id (inc_sh_time_prover_fail time_prover)
        in log (sh_tag id ^ triv_str ^ "failed: " ^ msg) end
    | SH_ERROR => log (sh_tag id ^ "failed: " ^ msg))
  end

end

fun override_params prover type_enc timeout =
  [("provers", prover),
   ("max_facts", "0"),
   ("type_enc", type_enc),
   ("strict", "true"),
   ("slice", "false"),
   ("timeout", timeout |> Time.toSeconds |> string_of_int)]

fun run_proof_method trivial full name meth named_thms id
    ({pre=st, timeout, log, pos, ...}: Mirabelle.run_args) =
  let
    fun do_method named_thms ctxt =
      let
        val ref_of_str = (* FIXME proper wrapper for parser combinators *)
          suffix ";" #> Token.explode (Thy_Header.get_keywords' ctxt) Position.none
          #> Parse.thm #> fst
        val thms = named_thms |> maps snd
        val facts = named_thms |> map (ref_of_str o fst o fst)
        val fact_override = {add = facts, del = [], only = true}
        fun my_timeout time_slice =
          timeout |> Time.toReal |> curry (op *) time_slice |> Time.fromReal
        fun sledge_tac time_slice prover type_enc =
          Sledgehammer_Tactics.sledgehammer_as_oracle_tac ctxt
            (override_params prover type_enc (my_timeout time_slice)) fact_override []
      in
        if !meth = "sledgehammer_tac" then
          sledge_tac 0.2 ATP_Proof.vampireN "mono_native"
          ORELSE' sledge_tac 0.2 ATP_Proof.eN "poly_guards??"
          ORELSE' sledge_tac 0.2 ATP_Proof.spassN "mono_native"
          ORELSE' sledge_tac 0.2 ATP_Proof.z3_tptpN "poly_tags??"
          ORELSE' SMT_Solver.smt_tac ctxt thms
        else if !meth = "smt" then
          SMT_Solver.smt_tac ctxt thms
        else if full then
          Metis_Tactic.metis_tac [ATP_Proof_Reconstruct.full_typesN]
            ATP_Proof_Reconstruct.default_metis_lam_trans ctxt thms
        else if String.isPrefix "metis (" (!meth) then
          let
            val (type_encs, lam_trans) =
              !meth
              |> Token.explode (Thy_Header.get_keywords' ctxt) Position.start
              |> filter Token.is_proper |> tl
              |> Metis_Tactic.parse_metis_options |> fst
              |>> the_default [ATP_Proof_Reconstruct.partial_typesN]
              ||> the_default ATP_Proof_Reconstruct.default_metis_lam_trans
          in Metis_Tactic.metis_tac type_encs lam_trans ctxt thms end
        else if !meth = "metis" then
          Metis_Tactic.metis_tac [] ATP_Proof_Reconstruct.default_metis_lam_trans ctxt thms
        else if !meth = "none" then
          K all_tac
        else if !meth = "fail" then
          K no_tac
        else
          (warning ("Unknown method " ^ quote (!meth)); K no_tac)
      end
    fun apply_method named_thms =
      Mirabelle.can_apply timeout (do_method named_thms) st

    fun with_time (false, t) = "failed (" ^ string_of_int t ^ ")"
      | with_time (true, t) = (change_data id inc_proof_method_success;
          if trivial then ()
          else change_data id inc_proof_method_nontriv_success;
          change_data id (inc_proof_method_lemmas (length named_thms));
          change_data id (inc_proof_method_time t);
          change_data id (inc_proof_method_posns (pos, trivial));
          if name = "proof" then change_data id inc_proof_method_proofs else ();
          "succeeded (" ^ string_of_int t ^ ")")
    fun timed_method named_thms =
      (with_time (Mirabelle.cpu_time apply_method named_thms), true)
      handle Timeout.TIMEOUT _ => (change_data id inc_proof_method_timeout; ("timeout", false))
           | ERROR msg => ("error: " ^ msg, false)

    val _ = log separator
    val _ = change_data id inc_proof_method_calls
    val _ = if trivial then () else change_data id inc_proof_method_nontriv_calls
  in
    named_thms
    |> timed_method
    |>> log o prefix (proof_method_tag meth id)
    |> snd
  end

val try_timeout = seconds 5.0

(* crude hack *)
val num_sledgehammer_calls = Unsynchronized.ref 0
val remaining_stride = Unsynchronized.ref stride_default

fun sledgehammer_action args =
  let
    val stride = Mirabelle.get_int_setting args (strideK, stride_default)
    val max_calls = Mirabelle.get_int_setting args (max_callsK, max_calls_default)
    val check_trivial = Mirabelle.get_bool_setting args (check_trivialK, check_trivial_default)
  in
    fn id => fn (st as {pre, name, log, ...}: Mirabelle.run_args) =>
      let val goal = Thm.major_prem_of (#goal (Proof.goal pre)) in
        if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal then
          ()
        else if !remaining_stride > 1 then
          (* We still have some steps to do *)
          (remaining_stride := !remaining_stride - 1;
          log "Skipping because of stride")
        else
          (* This was the last step, now run the action *)
          let
            val _ = remaining_stride := stride
            val _ = num_sledgehammer_calls := !num_sledgehammer_calls + 1
          in
            if !num_sledgehammer_calls > max_calls then
              log "Skipping because max number of calls reached"
            else
              let
                val meth = Unsynchronized.ref ""
                val named_thms =
                  Unsynchronized.ref (NONE : ((string * stature) * thm list) list option)
                val trivial =
                  if check_trivial then
                    Try0.try0 (SOME try_timeout) ([], [], [], []) pre
                    handle Timeout.TIMEOUT _ => false
                  else false
                fun apply_method () =
                  (Mirabelle.catch_result (proof_method_tag meth) false
                    (run_proof_method trivial false name meth (these (!named_thms))) id st; ())
              in
                Mirabelle.catch sh_tag (run_sledgehammer trivial args meth named_thms) id st;
                if is_some (!named_thms) then apply_method () else ()
              end
          end
      end
  end

fun invoke args =
  Mirabelle.register (init, sledgehammer_action args, done)

end
