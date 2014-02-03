(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_reconstructor.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Reconstructors.
*)

signature SLEDGEHAMMER_RECONSTRUCTOR =
sig
  type stature = ATP_Problem_Generate.stature

  datatype reconstructor =
    Metis of string * string |
    SMT

  datatype play_outcome =
    Played of Time.time |
    Play_Timed_Out of Time.time |
    Play_Failed |
    Not_Played

  type minimize_command = string list -> string
  type one_line_params =
    (reconstructor * play_outcome) * string * (string * stature) list * minimize_command * int * int

  val smtN : string

  val string_of_reconstructor : reconstructor -> string
  val string_of_play_outcome : play_outcome -> string
  val play_outcome_ord : play_outcome * play_outcome -> order

  val one_line_proof_text : int -> one_line_params -> string
  val silence_reconstructors : bool -> Proof.context -> Proof.context
end;

structure Sledgehammer_Reconstructor : SLEDGEHAMMER_RECONSTRUCTOR =
struct

open ATP_Util
open ATP_Problem_Generate
open ATP_Proof_Reconstruct

datatype reconstructor =
  Metis of string * string |
  SMT

datatype play_outcome =
  Played of Time.time |
  Play_Timed_Out of Time.time |
  Play_Failed |
  Not_Played

type minimize_command = string list -> string
type one_line_params =
  (reconstructor * play_outcome) * string * (string * stature) list * minimize_command * int * int

val smtN = "smt"

fun string_of_reconstructor (Metis (type_enc, lam_trans)) = metis_call type_enc lam_trans
  | string_of_reconstructor SMT = smtN

fun string_of_play_outcome (Played time) = string_of_ext_time (false, time)
  | string_of_play_outcome (Play_Timed_Out time) = string_of_ext_time (true, time) ^ ", timed out"
  | string_of_play_outcome Play_Failed = "failed"
  | string_of_play_outcome _ = "unknown"

fun play_outcome_ord (Played time1, Played time2) =
    int_ord (pairself Time.toMilliseconds (time1, time2))
  | play_outcome_ord (Played _, _) = LESS
  | play_outcome_ord (_, Played _) = GREATER
  | play_outcome_ord (Not_Played, Not_Played) = EQUAL
  | play_outcome_ord (Not_Played, _) = LESS
  | play_outcome_ord (_, Not_Played) = GREATER
  | play_outcome_ord (Play_Timed_Out time1, Play_Timed_Out time2) =
    int_ord (pairself Time.toMilliseconds (time1, time2))
  | play_outcome_ord (Play_Timed_Out _, _) = LESS
  | play_outcome_ord (_, Play_Timed_Out _) = GREATER
  | play_outcome_ord (Play_Failed, Play_Failed) = EQUAL

(* FIXME: Various bugs, esp. with "unfolding"
fun unusing_chained_facts _ 0 = ""
  | unusing_chained_facts used_chaineds num_chained =
    if length used_chaineds = num_chained then ""
    else if null used_chaineds then "(* using no facts *) "
    else "(* using only " ^ space_implode " " used_chaineds ^ " *) "
*)

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n =
    "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n

fun command_call name [] =
    name |> not (Symbol_Pos.is_identifier name) ? enclose "(" ")"
  | command_call name args = "(" ^ name ^ " " ^ space_implode " " args ^ ")"

fun reconstructor_command reconstr i n used_chaineds num_chained ss =
  (* unusing_chained_facts used_chaineds num_chained ^ *)
  apply_on_subgoal i n ^ command_call (string_of_reconstructor reconstr) ss

fun show_time NONE = ""
  | show_time (SOME ext_time) = " (" ^ string_of_ext_time ext_time ^ ")"

fun try_command_line banner time command =
  banner ^ ": " ^ Active.sendback_markup [Markup.padding_command] command ^ show_time time ^ "."

fun minimize_line _ [] = ""
  | minimize_line minimize_command ss =
    (case minimize_command ss of
      "" => ""
    | command => "\nTo minimize: " ^ Active.sendback_markup [Markup.padding_command] command ^ ".")

fun split_used_facts facts =
  facts
  |> List.partition (fn (_, (sc, _)) => sc = Chained)
  |> pairself (sort_distinct (string_ord o pairself fst))

fun one_line_proof_text num_chained
    ((reconstr, play), banner, used_facts, minimize_command, subgoal, subgoal_count) =
  let
    val (chained, extra) = split_used_facts used_facts

    val (failed, ext_time) =
      (case play of
        Played time => (false, (SOME (false, time)))
      | Play_Timed_Out time => (false, SOME (true, time))
      | Play_Failed => (true, NONE)
      | Not_Played => (false, NONE))

    val try_line =
      map fst extra
      |> reconstructor_command reconstr subgoal subgoal_count (map fst chained) num_chained
      |> (if failed then
            enclose "One-line proof reconstruction failed: "
              ".\n(Invoking \"sledgehammer\" with \"[strict]\" might solve this.)"
          else
            try_command_line banner ext_time)
  in
    try_line ^ minimize_line minimize_command (map fst (extra @ chained))
  end

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_reconstructors debug =
  Try0.silence_methods debug
  #> Config.put SMT_Config.verbose debug

end;
