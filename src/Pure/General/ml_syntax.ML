(*  Title:      Pure/General/ml_syntax.ML
    ID:         $Id$
    Author:     Makarius

Basic ML syntax operations.
*)

signature ML_SYNTAX =
sig
  val reserved: string list
  val is_reserved: string -> bool
  val is_identifier: string -> bool
  val str_of_pair: ('a -> string) -> ('b -> string) -> 'a * 'b -> string
  val str_of_list: ('a -> string) -> 'a list -> string
  val str_of_option: ('a -> string) -> 'a option -> string
  val str_of_char: string -> string
end;

structure ML_Syntax: ML_SYNTAX =
struct

(* reserved words *)

val reserved =
 ["abstype", "and", "andalso", "as", "case", "do", "datatype", "else",
  "end", "exception", "fn", "fun", "handle", "if", "in", "infix",
  "infixr", "let", "local", "nonfix", "of", "op", "open", "orelse",
  "raise", "rec", "then", "type", "val", "with", "withtype", "while",
  "eqtype", "functor", "include", "sharing", "sig", "signature",
  "struct", "structure", "where"];

val is_reserved = member (op =) reserved;


(* identifiers *)

fun is_identifier name =
  not (is_reserved name) andalso Syntax.is_ascii_identifier name;


(* unformatted output *)

fun str_of_pair f1 f2 (x, y) = "(" ^ f1 x ^ ", " ^ f2 y ^ ")";

fun str_of_list f = enclose "[" "]" o commas o map f;

fun str_of_option f NONE = "NONE"
  | str_of_option f (SOME x) = "SOME (" ^ f x ^ ")";

fun str_of_char c =
  if not (Symbol.is_char c) then raise Fail ("Bad character: " ^ quote c)
  else if c = "\"" then "\\\""
  else if c = "\\" then "\\\\"
  else if Symbol.is_printable c then c
  else "\\" ^ string_of_int (ord c);

val str_of_string = quote o translate_string str_of_char;

end;
