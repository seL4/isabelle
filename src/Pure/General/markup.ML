(*  Title:      Pure/General/markup.ML
    ID:         $Id$
    Author:     Makarius

Common markup elements.
*)

signature MARKUP =
sig
  type property = string * string
  type T = string * property list
  val nameN: string
  val kindN: string
  val pos_lineN: string
  val pos_nameN: string
  val none: T
  val indentN: string
  val blockN: string val block: int -> T
  val breakN: string val break: int -> T
  val fbreakN: string val fbreak: T
  val classN: string val class: string -> T
  val tyconN: string val tycon: string -> T
  val constN: string val const: string -> T
  val axiomN: string val axiom: string -> T
  val sortN: string val sort: T
  val typN: string val typ: T
  val termN: string val term: T
  val keywordN: string val keyword: string -> T
  val commandN: string val command: string -> T
  val promptN: string val prompt: T
  val stateN: string val state: T
  val no_stateN: string val no_state: T
  val subgoalN: string val subgoal: T
end;

structure Markup: MARKUP =
struct

(* basic markup *)

type property = string * string;
type T = string * property list;

val none = ("", []);

val nameN = "name";
val kindN = "kind";
val pos_lineN = "pos_line";
val pos_nameN = "pos_name";

fun markup kind = (kind, (kind, []): T);
fun markup_string kind prop = (kind, fn s => (kind, [(prop, s)]): T);
fun markup_int kind prop = (kind, fn i => (kind, [(prop, string_of_int i)]): T);


(* pretty printing *)

val indentN = "indent";
val (blockN, block) = markup_int "block" indentN;

val widthN = "width";
val (breakN, break) = markup_int "break" widthN;

val (fbreakN, fbreak) = markup "fbreak";


(* logical entities *)

val (classN, class) = markup_string "class" nameN;
val (tyconN, tycon) = markup_string "tycon" nameN;
val (constN, const) = markup_string "const" nameN;
val (axiomN, axiom) = markup_string "axiom" nameN;


(* inner syntax *)

val (sortN, sort) = markup "sort";
val (typN, typ) = markup "typ";
val (termN, term) = markup "term";


(* outer syntax *)

val (keywordN, keyword) = markup_string "keyword" nameN;
val (commandN, command) = markup_string "command" nameN;


(* toplevel *)

val (promptN, prompt) = markup "prompt";
val (stateN, state) = markup "state";
val (no_stateN, no_state) = markup "no_state";
val (subgoalN, subgoal) = markup "subgoal";

end;
