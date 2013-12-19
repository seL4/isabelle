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
end;

structure Sledgehammer_Reconstructor : SLEDGEHAMMER_RECONSTRUCTOR =
struct

open ATP_Problem_Generate

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

end;
