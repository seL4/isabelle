(*  Title:      Pure/Thy/thy_syn.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Syntax for thy files.
*)

signature THY_SYN =
sig
  val add_syntax: string list ->
    (string * (ThyParse.token list -> (string * string) * ThyParse.token list)) list
    -> unit
  val parse: string -> string -> string
end;

structure ThySyn: THY_SYN =
struct

(* current syntax *)

val keywords = ref ThyParse.pure_keywords;
val sections = ref ThyParse.pure_sections;

fun make_syntax () =
  ThyParse.make_syntax (! keywords) (!sections);

val syntax = ref (make_syntax ());


(* augment syntax *)

fun add_syntax keys sects =
 (keywords := (keys union ! keywords);
  sections := sects @ ! sections;
  syntax := make_syntax ());


(* parse *)

fun parse name txt =
  ThyParse.parse_thy (! syntax) name txt;

end;
