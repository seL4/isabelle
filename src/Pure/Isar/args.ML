(*  Title:      Pure/Isar/args.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Concrete argument syntax (for attributes, methods etc.).

TODO:
  - sectioned: generalize sname to attributed thms;
*)

signature ARGS =
sig
  type T
  val val_of: T -> string
  val ident: string -> T
  val string: string -> T
  val keyword: string -> T
  val stopper: T * (T -> bool)
  val not_eof: T -> bool
  val $$$ : string -> T list -> string * T list
  val name: T list -> string * T list
  val sectioned: string list -> T list -> (string list * (string * string list) list) * T list
  type src
  val syntax: string -> (T list -> 'a * T list) -> ('a -> 'b) -> src -> 'b
end;

structure Args: ARGS =
struct


(** datatype T **)

datatype kind = Ident | String | Keyword | EOF;
datatype T = Arg of kind * string;

fun val_of (Arg (_, x)) = x;

fun str_of (Arg (Ident, x)) = enclose "'" "'" x
  | str_of (Arg (String, x)) = quote x
  | str_of (Arg (Keyword, x)) = x;

fun arg kind x = Arg (kind, x);
val ident = arg Ident;
val string = arg String;
val keyword = arg Keyword;


(* eof *)

val eof = arg EOF "";

fun is_eof (Arg (EOF, _)) = true
  | is_eof _ = false;

val stopper = (eof, is_eof);
val not_eof = not o is_eof;



(** scanners **)

(* basic *)

fun $$$ x = Scan.one (fn Arg (k, y) => (k = Ident orelse k = Keyword) andalso x = y) >> val_of;
val name = Scan.one (fn (Arg (k, x)) => k = Ident orelse k = String) >> val_of;


(* sections *)

val no_colon = Scan.one (fn Arg (k, x) => k = String orelse x <> ":");
val sname = name --| Scan.ahead no_colon;

fun sect s = ($$$ s --| $$$ ":") -- Scan.repeat sname;

fun any_sect [] = Scan.fail
  | any_sect (s :: ss) = sect s || any_sect ss;

fun sectioned ss =
  Scan.repeat sname -- Scan.repeat (any_sect ss);



(** type src **)

type src = (string * T list) * Position.T;

fun err_in_src kind msg ((s, args), pos) =
  error (space_implode " " (kind :: s :: map str_of args) ^ Position.str_of pos ^ ": " ^ msg);


(* argument syntax *)

fun syntax kind scan f (src as ((s, args), pos)) =
  (case handle_error (Scan.error (Scan.finite stopper scan)) args of
    OK (x, []) => f x
  | OK (_, args') => err_in_src kind "bad arguments" ((s, args'), pos)
  | Error msg => err_in_src kind ("\n" ^ msg) src);


end;
