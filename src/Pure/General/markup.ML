(*  Title:      Pure/General/markup.ML
    ID:         $Id$
    Author:     Makarius

Common markup elements.
*)

signature MARKUP =
sig
  type property = string * string
  type T = string * property list
  val none: T
  val property: string * string -> T -> T
  val nameN: string
  val add_name: string -> T -> T
  val posN: string
  val add_pos: Position.T -> T -> T
  val classN: string
  val class: string -> T
  val tyconN: string
  val tycon: string -> T
  val constN: string
  val const: string -> T
  val axiomN: string
  val axiom: string -> T
  val sortN: string
  val sort: T
  val typN: string
  val typ: T
  val termN: string
  val term: T
  val propN: string
  val prop: T
  val thmN: string
  val thm: T
  val keywordN: string
  val keyword: string -> T
  val commandN: string
  val command: string -> T
end;

structure Markup: MARKUP =
struct

type property = string * string;
type T = string * property list;

val none = ("", []);


(* properties *)

fun property x (name, xs) : T = (name, x :: xs);

val nameN = "name";
fun add_name x = property (nameN, x);

val posN = "pos";
fun add_pos x = property (posN, Position.str_of x);


(* logical entities *)

val classN = "class";
fun class name = (classN, [(nameN, name)]);

val tyconN = "tycon";
fun tycon name = (tyconN, [(nameN, name)]);

val constN = "const";
fun const name = (constN, [(nameN, name)]);

val axiomN = "axiom";
fun axiom name = (axiomN, [(nameN, name)]);


(* inner syntax *)

val sortN = "sort";
val sort = (sortN, []);

val typN = "typ";
val typ = (typN, []);

val termN = "term";
val term = (termN, []);

val propN = "prop";
val prop = (propN, []);

val thmN = "thm";
val thm = (thmN, []);


(* outer syntax *)

val keywordN = "keyword";
fun keyword name = (keywordN, [(nameN, name)]);

val commandN = "command";
fun command name = (commandN, [(nameN, name)]);

end;
