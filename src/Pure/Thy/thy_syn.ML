(*  Title:      Pure/Thy/thy_syn.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Provide syntax for *old-style* theory files.
*)

signature BASIC_THY_SYN =
sig
  val delete_tmpfiles: bool ref
end;

signature THY_SYN =
sig
  include BASIC_THY_SYN
  val add_syntax: string list ->
    (string * (ThyParse.token list -> (string * string) * ThyParse.token list)) list
    -> unit
  val get_lexicon: unit -> Scan.lexicon
  val load_thy: string -> string list -> unit
end;

structure ThySyn: THY_SYN =
struct


(* current syntax *)

val keywords = ref ThyParse.pure_keywords;
val sections = ref ThyParse.pure_sections;

fun make_syntax () =
  ThyParse.make_syntax (! keywords) (!sections);

val syntax = ref (make_syntax ());

fun get_lexicon () = ThyParse.get_lexicon (! syntax);


(* augment syntax *)

fun add_syntax keys sects =
 (keywords := (keys union ! keywords);
  sections := sects @ ! sections;
  syntax := make_syntax ());


(* load_thy *)

val delete_tmpfiles = ref true;

fun load_thy name chs =
  let
    val tmp_path = File.tmp_path (ThyLoad.ml_path (name ^ "_thy"));
    val txt_out = ThyParse.parse_thy (! syntax) chs;
  in
    File.write tmp_path txt_out;
    File.symbol_use tmp_path;
    if ! delete_tmpfiles then File.rm tmp_path else ()
  end;


end;


structure BasicThySyn: BASIC_THY_SYN = ThySyn;
open BasicThySyn;
