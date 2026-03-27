(*  Title:      HOL/Tools/Mirabelle/mirabelle_isar_annotate.ML
    Author:     Lukas Stevens, Københavns Universitet

Mirabelle action: "isar_annotate"

    This action tests whether Sledgehammer_Isar_Annotate has the roundtrip property,
    i.e. whether printing type annotated goals yield the same goal after reparsing.
*)

structure Mirabelle_Isar_Annotate: MIRABELLE_ACTION =
struct

datatype Reparse_Result =
  Timeout | Success | Failure of {annotated_goal_string: string, reparsed_goal: term}

fun string_of_reparse_result Timeout = "timeout"
  | string_of_reparse_result Success = "success"
  | string_of_reparse_result (Failure _) = "failure"

fun reparse_isar_annotate (ctxt : Proof.context) (goal : term) =
  let
    val annotated_goal =
      singleton (Syntax.uncheck_terms ctxt) goal
      |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt
    val annotated_goal_string =
      Sledgehammer_Isar_Annotate.pretty_annotated_term ctxt annotated_goal
      |> Pretty.pure_string_of
    val reparsed_goal = Syntax.read_term ctxt annotated_goal_string
  in
    if Envir.aeconv (goal, reparsed_goal) then Success
    else Failure {annotated_goal_string = annotated_goal_string, reparsed_goal = reparsed_goal}
  end

fun try_reparse_isar_annotate timeout ctxt goal_term =
  Timeout.apply timeout (fn () =>
    reparse_isar_annotate ctxt goal_term handle Timeout.TIMEOUT _ => Timeout)
  

datatype stats = Stats of {calls: int, success: int, failure: int, timeout: int}

val empty_stats = Stats {calls = 0, success = 0, failure = 0, timeout = 0}

fun inc_call (Stats {calls, success, failure, timeout}) =
  Stats {calls = calls + 1, success = success, failure = failure, timeout = timeout}
fun inc_success (Stats {calls, success, failure, timeout}) =
  Stats {calls = calls, success = success + 1, failure = failure, timeout = timeout}
fun inc_failure (Stats {calls, success, failure, timeout}) =
  Stats {calls = calls, success = success, failure = failure + 1, timeout = timeout}
fun inc_timeout (Stats {calls, success, failure, timeout}) =
  Stats {calls = calls, success = success, failure = failure, timeout = timeout + 1}
fun inc_reparse_result Timeout = inc_timeout
  | inc_reparse_result Success = inc_success
  | inc_reparse_result (Failure _) = inc_failure

fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    val data = Synchronized.var "Mirabelle_Isar_Annotate.data" empty_stats
    fun run ({pre, ...} : Mirabelle.command) =
      let
        val {context = ctxt, goal, ...} = Proof.goal pre
        val goal_term = Thm.major_prem_of goal |> perhaps (try HOLogic.dest_Trueprop)
        val goal_string =
          Syntax.pretty_term ctxt goal_term |> Pretty.pure_string_of 
        val ({cpu, ...}, reparse_result) =
          Timing.timing (try_reparse_isar_annotate timeout ctxt goal_term) ()
        val () = Synchronized.change data (inc_reparse_result reparse_result o inc_call)
        val cpu_ms = Time.toMilliseconds cpu
      in
        "result: " ^ string_of_reparse_result reparse_result ^
        "\ngoal_term: " ^ goal_string ^
        (case reparse_result of
          Failure {annotated_goal_string, reparsed_goal} =>
            "\nraw_goal_term: " ^ @{make_string} goal_term ^
            "\nannotated_goal_term: " ^ annotated_goal_string ^
            "\nraw_reparsed_goal_term: " ^ @{make_string} reparsed_goal
        | _ => "") ^
        "\ncpu_ms: " ^ string_of_int cpu_ms
      end
    fun finalize () =
      let val Stats {calls, success, failure, timeout} = Synchronized.value data in
        if calls > 0 then
          "\nTotal calls: " ^ string_of_int calls ^
          "\nSuccesses: " ^ string_of_int success ^
          "\nFailures: " ^ string_of_int failure ^
          "\nTimeouts: " ^ string_of_int timeout ^
          "\nSuccess rate: " ^
            Real.fmt (StringCvt.FIX (SOME 1))
              (100.0 * Real.fromInt success / Real.fromInt calls) ^ "%"
        else ""
      end
  in ("", {run = run, finalize = finalize}) end
val () = Mirabelle.register_action "isar_annotate" make_action

end
