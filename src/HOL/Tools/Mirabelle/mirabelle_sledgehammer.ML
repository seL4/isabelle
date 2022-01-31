(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Sascha Boehme, TU Munich
    Author:     Tobias Nipkow, TU Munich
    Author:     Makarius
    Author:     Martin Desharnais, UniBw Munich, MPI-INF Saarbruecken

Mirabelle action: "sledgehammer".
*)

structure Mirabelle_Sledgehammer: MIRABELLE_ACTION =
struct

(*To facilitate synching the description of Mirabelle Sledgehammer parameters
 (in ../lib/Tools/mirabelle) with the parameters actually used by this
 interface, the former extracts PARAMETER and DESCRIPTION from code below which
 has this pattern (provided it appears in a single line):
   val .*K = "PARAMETER" (*DESCRIPTION*)
*)
(* NOTE: Do not forget to update the Sledgehammer documentation to reflect changes here. *)

val check_trivialK = "check_trivial" (*=BOOL: check if goals are "trivial"*)
val keep_probsK = "keep_probs" (*=BOOL: keep temporary problem files created by sledgehammer*)
val keep_proofsK = "keep_proofs" (*=BOOL: keep temporary proof files created by ATPs*)
val proof_methodK = "proof_method" (*=STRING: how to reconstruct proofs (e.g. using metis)*)
val term_orderK = "term_order" (*=STRING: term order (in E)*)

(*defaults used in this Mirabelle action*)
val check_trivial_default = false
val keep_probs_default = false
val keep_proofs_default = false

datatype sh_data = ShData of {
  calls: int,
  success: int,
  nontriv_calls: int,
  nontriv_success: int,
  lemmas: int,
  max_lems: int,
  time_isa: int,
  time_prover: int}

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
       time_prover) =
  ShData{calls=calls, success=success, nontriv_calls=nontriv_calls,
         nontriv_success=nontriv_success, lemmas=lemmas, max_lems=max_lems,
         time_isa=time_isa, time_prover=time_prover}

fun make_re_data (calls,success,nontriv_calls,nontriv_success,proofs,time,
                  timeout,lemmas,posns) =
  ReData{calls=calls, success=success, nontriv_calls=nontriv_calls,
         nontriv_success=nontriv_success, proofs=proofs, time=time,
         timeout=timeout, lemmas=lemmas, posns=posns}

val empty_sh_data = make_sh_data (0, 0, 0, 0, 0, 0, 0, 0)
val empty_re_data = make_re_data (0, 0, 0, 0, 0, 0, 0, (0,0,0), [])

fun tuple_of_sh_data (ShData {calls, success, nontriv_calls, nontriv_success, lemmas, max_lems,
    time_isa, time_prover}) =
  (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover)

fun tuple_of_re_data (ReData {calls, success, nontriv_calls, nontriv_success,
  proofs, time, timeout, lemmas, posns}) = (calls, success, nontriv_calls,
  nontriv_success, proofs, time, timeout, lemmas, posns)

datatype data = Data of {
  sh: sh_data,
  re_u: re_data (* proof method with unminimized set of lemmas *)
  }

type change_data = (data -> data) -> unit

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
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover) =>
    (calls + 1, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover))

val inc_sh_success = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover) =>
    (calls, success + 1, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover))

val inc_sh_nontriv_calls =  map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover) =>
    (calls, success, nontriv_calls + 1, nontriv_success, lemmas, max_lems, time_isa, time_prover))

val inc_sh_nontriv_success = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas,max_lems, time_isa, time_prover) =>
    (calls, success, nontriv_calls, nontriv_success + 1, lemmas,max_lems, time_isa, time_prover))

fun inc_sh_lemmas n = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover) =>
    (calls, success, nontriv_calls, nontriv_success, lemmas+n, max_lems, time_isa, time_prover))

fun inc_sh_max_lems n = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover) =>
    (calls, success,nontriv_calls, nontriv_success, lemmas, Int.max (max_lems, n), time_isa,
     time_prover))

fun inc_sh_time_isa t = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover) =>
    (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa + t, time_prover))

fun inc_sh_time_prover t = map_sh_data
  (fn (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover) =>
    (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover + t))

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
fun ms t = Real.fromInt t / 1000.0
fun avg_time t n =
  if n > 0 then (Real.fromInt t / 1000.0) / Real.fromInt n else 0.0

fun log_sh_data (ShData {calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa,
      time_prover}) =
  "\nTotal number of sledgehammer calls: " ^ str calls ^
  "\nNumber of successful sledgehammer calls: " ^ str success ^
  "\nNumber of sledgehammer lemmas: " ^ str lemmas ^
  "\nMax number of sledgehammer lemmas: " ^ str max_lems ^
  "\nSuccess rate: " ^ percentage success calls ^ "%" ^
  "\nTotal number of nontrivial sledgehammer calls: " ^ str nontriv_calls ^
  "\nNumber of successful nontrivial sledgehammer calls: " ^ str nontriv_success ^
  "\nTotal time for sledgehammer calls (Isabelle): " ^ str3 (ms time_isa) ^
  "\nTotal time for successful sledgehammer calls (ATP): " ^ str3 (ms time_prover) ^
  "\nAverage time for sledgehammer calls (Isabelle): " ^
    str3 (avg_time time_isa calls) ^
  "\nAverage time for successful sledgehammer calls (ATP): " ^
    str3 (avg_time time_prover success)

fun log_re_data sh_calls (ReData {calls, success, nontriv_calls, nontriv_success, proofs, time,
      timeout, lemmas = (lemmas, lems_sos, lems_max), posns}) =
  let
    val proved =
      posns |> map (fn (pos, triv) =>
        str0 (Position.line_of pos) ^ ":" ^ str0 (Position.offset_of pos) ^
        (if triv then "[T]" else ""))
  in
    "\nTotal number of proof method calls: " ^ str calls ^
    "\nNumber of successful proof method calls: " ^ str success ^
      " (proof: " ^ str proofs ^ ")" ^
    "\nNumber of proof method timeouts: " ^ str timeout ^
    "\nSuccess rate: " ^ percentage success sh_calls ^ "%" ^
    "\nTotal number of nontrivial proof method calls: " ^ str nontriv_calls ^
    "\nNumber of successful nontrivial proof method calls: " ^ str nontriv_success ^
      " (proof: " ^ str proofs ^ ")" ^
    "\nNumber of successful proof method lemmas: " ^ str lemmas ^
    "\nSOS of successful proof method lemmas: " ^ str lems_sos ^
    "\nMax number of successful proof method lemmas: " ^ str lems_max ^
    "\nTotal time for successful proof method calls: " ^ str3 (ms time) ^
    "\nAverage time for successful proof method calls: " ^ str3 (avg_time time success) ^
    "\nProved: " ^ space_implode " " proved
  end

in

fun log_data (Data {sh, re_u}) =
  let
    val ShData {calls=sh_calls, ...} = sh
    val ReData {calls=re_calls, ...} = re_u
  in
    if sh_calls > 0 then
      let val text1 = log_sh_data sh in
        if re_calls > 0 then text1 ^ "\n" ^ log_re_data sh_calls re_u else text1
      end
    else
      ""
  end

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

fun run_sh params term_order keep pos state =
  let
    fun set_file_name (SOME (dir, keep_probs, keep_proofs)) =
        let
          val filename = "prob_" ^
            StringCvt.padLeft #"0" 5 (str0 (Position.line_of pos)) ^ "_" ^
            StringCvt.padLeft #"0" 6 (str0 (Position.offset_of pos))
        in
          Config.put Sledgehammer_Prover_ATP.atp_problem_prefix (filename ^ "__")
          #> (keep_probs ? Config.put Sledgehammer_Prover_ATP.atp_problem_dest_dir dir)
          #> (keep_proofs ? Config.put Sledgehammer_Prover_ATP.atp_proof_dest_dir dir)
          #> Config.put SMT_Config.debug_files (dir ^ "/" ^ filename ^ "__" ^ serial_string ())
        end
      | set_file_name NONE = I
    val state' =
      state
      |> Proof.map_context
           (set_file_name keep
            #> (Option.map (Config.put Sledgehammer_ATP_Systems.term_order)
                  term_order |> the_default I))

    val ((_, (sledgehammer_outcome, msg)), cpu_time) = Mirabelle.cpu_time (fn () =>
      Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal NONE 1
        Sledgehammer_Fact.no_fact_override state') ()
  in
    (sledgehammer_outcome, msg, cpu_time)
  end
  handle
    ERROR msg => (Sledgehammer.SH_Unknown, " error: " ^ msg, 0)
  | _ => (Sledgehammer.SH_Unknown, " error: unexpected error", 0)

in

fun run_sledgehammer (params as {provers, ...}) output_dir term_order
  keep_probs keep_proofs proof_method_from_msg thy_index trivial pos st =
  let
    val thy = Proof.theory_of st
    val thy_name = Context.theory_name thy
    val triv_str = if trivial then "[T] " else ""
    val keep =
      if keep_probs orelse keep_proofs then
        let val subdir = StringCvt.padLeft #"0" 4 (string_of_int thy_index) ^ "_" ^ thy_name in
          Path.append output_dir (Path.basic subdir)
          |> Isabelle_System.make_directory
          |> Path.implode
          |> (fn dir => SOME (dir, keep_probs, keep_proofs))
        end
      else
        NONE
    val prover_name = hd provers
    val (sledgehamer_outcome, msg, cpu_time) = run_sh params term_order keep pos st
    val (time_prover, change_data, proof_method_and_used_thms) =
      (case sledgehamer_outcome of
        Sledgehammer.SH_Some {used_facts, run_time, ...} =>
        let
          val num_used_facts = length used_facts
          val time_prover = Time.toMilliseconds run_time
          fun get_thms (name, stature) =
            try (Sledgehammer_Util.thms_of_name (Proof.context_of st))
              name
            |> Option.map (pair (name, stature))
          val change_data =
            inc_sh_success
            #> not trivial ? inc_sh_nontriv_success
            #> inc_sh_lemmas num_used_facts
            #> inc_sh_max_lems num_used_facts
            #> inc_sh_time_prover time_prover
        in
          (SOME time_prover, change_data,
           SOME (proof_method_from_msg msg, map_filter get_thms used_facts))
        end
      | _ => (NONE, I, NONE))
    val outcome_msg =
      "(SH " ^ string_of_int cpu_time ^ "ms" ^
      (case time_prover of NONE => "" | SOME ms => ", ATP " ^ string_of_int ms ^ "ms") ^
      ") [" ^ prover_name ^ "]: "
  in
    (sledgehamer_outcome, triv_str ^ outcome_msg ^ msg, change_data #> inc_sh_time_isa cpu_time,
     proof_method_and_used_thms)
  end

end

fun override_params prover type_enc timeout =
  [("provers", prover),
   ("max_facts", "0"),
   ("type_enc", type_enc),
   ("strict", "true"),
   ("slice", "false"),
   ("timeout", timeout |> Time.toSeconds |> string_of_int)]

fun run_proof_method trivial full name meth named_thms timeout pos st =
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
        if meth = "sledgehammer_tac" then
          sledge_tac 0.25 ATP_Proof.vampireN "mono_native"
          ORELSE' sledge_tac 0.25 ATP_Proof.eN "poly_guards??"
          ORELSE' sledge_tac 0.25 ATP_Proof.spassN "mono_native"
          ORELSE' SMT_Solver.smt_tac ctxt thms
        else if meth = "smt" then
          SMT_Solver.smt_tac ctxt thms
        else if full then
          Metis_Tactic.metis_tac [ATP_Proof_Reconstruct.full_typesN]
            ATP_Proof_Reconstruct.default_metis_lam_trans ctxt thms
        else if String.isPrefix "metis (" meth then
          let
            val (type_encs, lam_trans) =
              meth
              |> Token.explode (Thy_Header.get_keywords' ctxt) Position.start
              |> filter Token.is_proper |> tl
              |> Metis_Tactic.parse_metis_options |> fst
              |>> the_default [ATP_Proof_Reconstruct.partial_typesN]
              ||> the_default ATP_Proof_Reconstruct.default_metis_lam_trans
          in Metis_Tactic.metis_tac type_encs lam_trans ctxt thms end
        else if meth = "metis" then
          Metis_Tactic.metis_tac [] ATP_Proof_Reconstruct.default_metis_lam_trans ctxt thms
        else if meth = "none" then
          K all_tac
        else if meth = "fail" then
          K no_tac
        else
          (warning ("Unknown method " ^ quote meth); K no_tac)
      end
    fun apply_method named_thms =
      Mirabelle.can_apply timeout (do_method named_thms) st

    fun with_time (false, t) = ("failed (" ^ string_of_int t ^ ")", I)
      | with_time (true, t) =
          ("succeeded (" ^ string_of_int t ^ ")",
           inc_proof_method_success
           #> not trivial ? inc_proof_method_nontriv_success
           #> inc_proof_method_lemmas (length named_thms)
           #> inc_proof_method_time t
           #> inc_proof_method_posns (pos, trivial)
           #> name = "proof" ? inc_proof_method_proofs)
    fun timed_method named_thms =
      with_time (Mirabelle.cpu_time apply_method named_thms)
        handle Timeout.TIMEOUT _ => ("timeout", inc_proof_method_timeout)
          | ERROR msg => ("error: " ^ msg, I)
  in
    timed_method named_thms
    |> apsnd (fn change_data => change_data
      #> inc_proof_method_calls
      #> not trivial ? inc_proof_method_nontriv_calls)
  end

val try0 = Try0.try0 (SOME (Time.fromSeconds 5)) ([], [], [], [])

fun make_action ({arguments, timeout, output_dir, ...} : Mirabelle.action_context) =
  let
    (* Parse Mirabelle-specific parameters *)
    val check_trivial =
      Mirabelle.get_bool_argument arguments (check_trivialK, check_trivial_default)
    val keep_probs = Mirabelle.get_bool_argument arguments (keep_probsK, keep_probs_default)
    val keep_proofs = Mirabelle.get_bool_argument arguments (keep_proofsK, keep_proofs_default)
    val term_order = AList.lookup (op =) arguments term_orderK
    val proof_method_from_msg = proof_method_from_msg arguments

    val params = Sledgehammer_Commands.default_params \<^theory> arguments

    val data = Synchronized.var "Mirabelle_Sledgehammer.data" empty_data

    val init_msg = "Params for sledgehammer: " ^ Sledgehammer_Prover.string_of_params params

    fun run ({theory_index, name, pos, pre, ...} : Mirabelle.command) =
      let val goal = Thm.major_prem_of (#goal (Proof.goal pre)) in
        if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal then
          ""
        else
          let
            val trivial = check_trivial andalso try0 pre handle Timeout.TIMEOUT _ => false
            val (outcome, log1, change_data1, proof_method_and_used_thms) =
              run_sledgehammer params output_dir term_order keep_probs keep_proofs
                proof_method_from_msg theory_index trivial pos pre
            val (log2, change_data2) =
              (case proof_method_and_used_thms of
                SOME (proof_method, used_thms) =>
                run_proof_method trivial false name proof_method used_thms timeout pos pre
                |> apfst (prefix (proof_method ^ " (sledgehammer): "))
              | NONE => ("", I))
            val () = Synchronized.change data
              (change_data1 #> change_data2 #> inc_sh_calls #> not trivial ? inc_sh_nontriv_calls)
          in
            log1 ^ "\n" ^ log2
            |> Symbol.trim_blanks
            |> prefix_lines (Sledgehammer.short_string_of_sledgehammer_outcome outcome ^ " ")
          end
      end

    fun finalize () = log_data (Synchronized.value data)
  in (init_msg, {run = run, finalize = finalize}) end

val () = Mirabelle.register_action "sledgehammer" make_action

end
