(*  Title:      Pure/Thy/document_source.ML
    Author:     Makarius

Document source for presentation.
*)

signature DOCUMENT_SOURCE =
sig
  val is_white: Token.T -> bool
  val is_black: Token.T -> bool
  val is_white_comment: Token.T -> bool
  val is_black_comment: Token.T -> bool
  val is_improper: Token.T -> bool
  val improper: Token.T list parser
  val improper_end: Token.T list parser
  val blank_end: Token.T list parser
  datatype scope = Command | Proof
  type tag = string * scope
  val eq_tag: tag * tag -> bool
  val update_tags: tag -> Proof.context -> Proof.context
  val get_tags: Proof.context -> tag list
  type tagging = tag list
  val update_tagging: Proof.context -> tagging -> tag option * tagging
  val tag_scope: scope parser
  val tag_name: string parser
  val old_tags: string list parser
  val annotation: unit parser
end;

structure Document_Source: DOCUMENT_SOURCE =
struct

(* white space and comments *)

(*NB: arranging white space around command spans is a black art*)

val is_white = Token.is_space orf Token.is_informal_comment;
val is_black = not o is_white;

val is_white_comment = Token.is_informal_comment;
val is_black_comment = Token.is_formal_comment;


val space_proper =
  Scan.one Token.is_blank -- Scan.many is_white_comment -- Scan.one is_black;

val is_improper = not o (is_black orf Token.is_begin_ignore orf Token.is_end_ignore);
val improper = Scan.many is_improper;
val improper_end = Scan.repeat (Scan.unless space_proper (Scan.one is_improper));
val blank_end = Scan.repeat (Scan.unless space_proper (Scan.one Token.is_blank));


(** syntactic tags **)

(* scope *)

datatype scope = Command | Proof;

type tag = string * scope;
val eq_tag: tag * tag -> bool = eq_fst op =;


(* context data *)

structure Tags = Proof_Data
(
  type T = tag list;
  fun init _ = [];
);

val update_tags = Tags.map o update eq_tag;

val get_tags = Tags.get;


(* command tagging *)

type tagging = tag list;

fun update_tagging ctxt tagging =
  let
    val tagging' = fold (update eq_tag) (get_tags ctxt) tagging;
    val nested_tagging' = filter (fn (_, scope) => scope = Proof) tagging';
  in (try hd tagging', nested_tagging') end;


(* parse scope and name *)

val scope = Parse.reserved "command" >> K Command || Parse.reserved "proof" >> K Proof;

val tag_scope =
  Parse.group (fn () => "document tag scope") (Parse.$$$ "(" |-- Parse.!!! (scope --| Parse.$$$ ")"));

val tag_name =
  Parse.group (fn () => "document tag name") (Parse.short_ident || Parse.string);


(* syntactic tags (old-style) *)

val old_tag = (improper -- Parse.$$$ "%" -- improper) |-- Parse.!!! (tag_name --| blank_end);

val old_tags = Scan.repeat old_tag;


(* semantic markers (operation on presentation context) *)

val marker = improper |-- Parse.document_marker --| blank_end;

val annotation = Scan.repeat (old_tag >> K () || marker >> K ()) >> K ();

end;
