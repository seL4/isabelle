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

  val string_of_play_outcome: play_outcome -> string

  type minimize_command = string list -> string
  type one_line_params =
    (reconstructor * play_outcome) * string * (string * stature) list * minimize_command * int * int

  val smtN : string

  val silence_reconstructors : bool -> Proof.context -> Proof.context
end;

structure Sledgehammer_Reconstructor : SLEDGEHAMMER_RECONSTRUCTOR =
struct

open ATP_Util
open ATP_Problem_Generate

datatype reconstructor =
  Metis of string * string |
  SMT

datatype play_outcome =
  Played of Time.time |
  Play_Timed_Out of Time.time |
  Play_Failed |
  Not_Played

fun string_of_play_outcome (Played time) = string_of_ext_time (false, time)
  | string_of_play_outcome (Play_Timed_Out time) = string_of_ext_time (true, time) ^ ", timed out"
  | string_of_play_outcome Play_Failed = "failed"
  | string_of_play_outcome _ = "unknown"

type minimize_command = string list -> string
type one_line_params =
  (reconstructor * play_outcome) * string * (string * stature) list * minimize_command * int * int

val smtN = "smt"

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_reconstructors debug =
  Config.put Metis_Tactic.verbose debug
  #> Config.put SMT_Config.verbose debug
  #> Config.put Lin_Arith.verbose debug
  #> (not debug ?
    (Context_Position.set_visible false
     #> Proof_Context.background_theory (fn thy =>
       thy
       |> Context_Position.set_visible_global false
       |> Config.put_global Unify.trace_bound (Config.get_global thy Unify.search_bound))))

end;
