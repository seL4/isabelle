(*  Title:      HOL/Tools/Mirabelle/mirabelle_sledgehammer.ML
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
val exhaustive_preplayK = "exhaustive_preplay" (*=BOOL: show exhaustive preplay data*)
val keep_probsK = "keep_probs" (*=BOOL: keep temporary problem files created by sledgehammer*)
val keep_proofsK = "keep_proofs" (*=BOOL: keep temporary proof files created by ATPs*)

(*defaults used in this Mirabelle action*)
val check_trivial_default = false
val exhaustive_preplay_default = false
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

fun make_sh_data
      (calls,success,nontriv_calls,nontriv_success,lemmas,max_lems,time_isa,
       time_prover) =
  ShData{calls=calls, success=success, nontriv_calls=nontriv_calls,
         nontriv_success=nontriv_success, lemmas=lemmas, max_lems=max_lems,
         time_isa=time_isa, time_prover=time_prover}

val empty_sh_data = make_sh_data (0, 0, 0, 0, 0, 0, 0, 0)

fun tuple_of_sh_data (ShData {calls, success, nontriv_calls, nontriv_success, lemmas, max_lems,
    time_isa, time_prover}) =
  (calls, success, nontriv_calls, nontriv_success, lemmas, max_lems, time_isa, time_prover)

fun map_sh_data f sh = make_sh_data (f (tuple_of_sh_data sh))

val inc_sh_calls = map_sh_data
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

in

fun log_data (sh as ShData {calls=sh_calls, ...}) =
  if sh_calls > 0 then
    log_sh_data sh
  else
    ""

end

local

fun run_sh params keep pos state =
  \<^try>\<open>
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
      val state' = state
        |> Proof.map_context (set_file_name keep)

      val ((_, (sledgehammer_outcome, msg)), cpu_time) = Mirabelle.cpu_time (fn () =>
        Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal NONE 1
          Sledgehammer_Fact.no_fact_override state') ()
    in
      (sledgehammer_outcome, msg, cpu_time)
    end
    catch ERROR msg => (Sledgehammer.SH_Unknown, " error: " ^ msg, 0)
      | _ => (Sledgehammer.SH_Unknown, " error: unexpected error", 0)
  \<close>

in

fun run_sledgehammer (params as {provers, ...}) output_dir keep_probs keep_proofs
    exhaustive_preplay thy_index trivial pos st =
  let
    val triv_str = if trivial then "[T] " else ""
    val keep =
      if keep_probs orelse keep_proofs then
        let
          val thy_long_name = Context.theory_long_name (Proof.theory_of st)
          val session_name = Long_Name.qualifier thy_long_name
          val thy_name = Long_Name.base_name thy_long_name
          val subdir = StringCvt.padLeft #"0" 4 (string_of_int thy_index) ^ "_" ^ thy_name
        in
          Path.append (Path.append output_dir (Path.basic session_name)) (Path.basic subdir)
          |> Isabelle_System.make_directory
          |> Path.implode
          |> (fn dir => SOME (dir, keep_probs, keep_proofs))
        end
      else
        NONE
    val prover_name = hd provers
    val (sledgehamer_outcome, msg, cpu_time) = run_sh params keep pos st
    val (time_prover, change_data, exhaustive_preplay_msg) =
      (case sledgehamer_outcome of
        Sledgehammer.SH_Some ({used_facts, run_time, ...}, preplay_results) =>
        let
          val num_used_facts = length used_facts
          val time_prover = Time.toMilliseconds run_time
          val change_data =
            inc_sh_success
            #> not trivial ? inc_sh_nontriv_success
            #> inc_sh_lemmas num_used_facts
            #> inc_sh_max_lems num_used_facts
            #> inc_sh_time_prover time_prover

          val exhaustive_preplay_msg =
            if exhaustive_preplay then
              preplay_results
              |> map
                (fn (meth, (play_outcome, used_facts)) =>
                    "Preplay: " ^ Sledgehammer_Proof_Methods.string_of_proof_method
                      (map (ATP_Util.content_of_pretty o fst) used_facts) meth ^
                    " (" ^ Sledgehammer_Proof_Methods.string_of_play_outcome play_outcome ^ ")")
              |> cat_lines
            else
              ""
        in
          (SOME time_prover, change_data, exhaustive_preplay_msg)
        end
      | _ => (NONE, I, ""))
    val outcome_msg =
      "(SH " ^ string_of_int cpu_time ^ "ms" ^
      (case time_prover of NONE => "" | SOME ms => ", ATP " ^ string_of_int ms ^ "ms") ^
      ") [" ^ prover_name ^ "]: "
  in
    (sledgehamer_outcome, triv_str ^ outcome_msg ^ Protocol_Message.clean_output msg ^
       (if exhaustive_preplay_msg = "" then "" else ("\n" ^ exhaustive_preplay_msg)),
     change_data #> inc_sh_time_isa cpu_time)
  end

end

val try0 = not o null o Try0.try0 (SOME (Time.fromSeconds 5)) []

fun make_action ({arguments, timeout, output_dir, ...} : Mirabelle.action_context) =
  let
    (* Parse Mirabelle-specific parameters *)
    val check_trivial =
      Mirabelle.get_bool_argument arguments (check_trivialK, check_trivial_default)
    val keep_probs = Mirabelle.get_bool_argument arguments (keep_probsK, keep_probs_default)
    val keep_proofs = Mirabelle.get_bool_argument arguments (keep_proofsK, keep_proofs_default)
    val exhaustive_preplay =
      Mirabelle.get_bool_argument arguments (exhaustive_preplayK, exhaustive_preplay_default)

    val params = Sledgehammer_Commands.default_params \<^theory> arguments

    val data = Synchronized.var "Mirabelle_Sledgehammer.data" empty_sh_data

    val init_msg = "Params for sledgehammer: " ^ Sledgehammer_Prover.string_of_params params

    fun run ({theory_index, pos, pre, ...} : Mirabelle.command) =
      let val goal = Thm.major_prem_of (#goal (Proof.goal pre)) in
        if can Logic.dest_conjunction goal orelse can Logic.dest_equals goal then
          ""
        else
          let
            val trivial = check_trivial andalso try0 pre handle Timeout.TIMEOUT _ => false
            val (outcome, log, change_data) =
              run_sledgehammer params output_dir keep_probs keep_proofs exhaustive_preplay
                theory_index trivial pos pre
            val () = Synchronized.change data
              (change_data #> inc_sh_calls #> not trivial ? inc_sh_nontriv_calls)
          in
            log
            |> Symbol.trim_blanks
            |> prefix_lines (Sledgehammer.short_string_of_sledgehammer_outcome outcome ^ " ")
          end
      end

    fun finalize () = log_data (Synchronized.value data)
  in (init_msg, {run = run, finalize = finalize}) end

val () = Mirabelle.register_action "sledgehammer" make_action

end
