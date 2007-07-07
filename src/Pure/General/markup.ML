(*  Title:      Pure/General/markup.ML
    ID:         $Id$
    Author:     Makarius

Common markup elements.
*)

signature MARKUP =
sig
  type property = string * string
  val nameN: string
  val pos_lineN: string
  val pos_nameN: string
  type T = string * property list
  val none: T
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

(* properties *)

type property = string * string;

val nameN = "name";
val pos_lineN = "pos_line";
val pos_nameN = "pos_name";


(* markup *)

type T = string * property list;

val none = ("", []);

fun markup kind = (kind, (kind, []): T);
fun markup_name kind = (kind, fn name => (kind, [(nameN, name)]): T);


(* logical entities *)

val (classN, class) = markup_name "class";
val (tyconN, tycon) = markup_name "tycon";
val (constN, const) = markup_name "const";
val (axiomN, axiom) = markup_name "axiom";


(* inner syntax *)

val (sortN, sort) = markup "sort";
val (typN, typ) = markup "typ";
val (termN, term) = markup "term";


(* outer syntax *)

val (keywordN, keyword) = markup_name "keyword";
val (commandN, command) = markup_name "command";


(* toplevel *)

val (promptN, prompt) = markup "prompt";
val (stateN, state) = markup "state";
val (no_stateN, no_state) = markup "no_state";
val (subgoalN, subgoal) = markup "subgoal";

end;
