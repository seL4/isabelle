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

  datatype play =
    Played of reconstructor * Time.time |
    Trust_Playable of reconstructor * Time.time option |
    Failed_to_Play of reconstructor

  type minimize_command = string list -> string
  type one_line_params = play * string * (string * stature) list * minimize_command * int * int

  val smtN : string
end;

structure Sledgehammer_Reconstructor : SLEDGEHAMMER_RECONSTRUCTOR =
struct

open ATP_Problem_Generate

datatype reconstructor =
  Metis of string * string |
  SMT

datatype play =
  Played of reconstructor * Time.time |
  Trust_Playable of reconstructor * Time.time option |
  Failed_to_Play of reconstructor

type minimize_command = string list -> string
type one_line_params = play * string * (string * stature) list * minimize_command * int * int

val smtN = "smt"

end;
