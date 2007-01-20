(*  Title:      Pure/General/ml_syntax.ML
    ID:         $Id$
    Author:     Makarius

Basic ML syntax operations.
*)

signature ML_SYNTAX =
sig
  val reserved_names: string list
  val reserved: Name.context
  val is_reserved: string -> bool
  val is_identifier: string -> bool
  val print_pair: ('a -> string) -> ('b -> string) -> 'a * 'b -> string
  val print_list: ('a -> string) -> 'a list -> string
  val print_option: ('a -> string) -> 'a option -> string
  val print_char: string -> string
  val print_string: string -> string
  val print_class: class -> string
  val print_sort: sort -> string
  val print_typ: typ -> string
  val print_term: term -> string
end;

structure ML_Syntax: ML_SYNTAX =
struct

(* reserved words *)

val reserved_names =
 ["abstype", "and", "andalso", "as", "case", "do", "datatype", "else",
  "end", "exception", "fn", "fun", "handle", "if", "in", "infix",
  "infixr", "let", "local", "nonfix", "of", "op", "open", "orelse",
  "raise", "rec", "then", "type", "val", "with", "withtype", "while",
  "eqtype", "functor", "include", "sharing", "sig", "signature",
  "struct", "structure", "where"];

val reserved = Name.make_context reserved_names;
val is_reserved = Name.is_declared reserved;


(* identifiers *)

fun is_identifier name =
  not (is_reserved name) andalso Syntax.is_ascii_identifier name;


(* literal output -- unformatted *)

fun print_pair f1 f2 (x, y) = "(" ^ f1 x ^ ", " ^ f2 y ^ ")";

fun print_list f = enclose "[" "]" o commas o map f;

fun print_option f NONE = "NONE"
  | print_option f (SOME x) = "SOME (" ^ f x ^ ")";

fun print_char s =
  if not (Symbol.is_char s) then raise Fail ("Bad character: " ^ quote s)
  else if s = "\"" then "\\\""
  else if s = "\\" then "\\\\"
  else
    let val c = ord s in
      if c < 32 then "\\^" ^ chr (c + ord "@")
      else if c < 127 then s
      else "\\" ^ string_of_int c
    end;

val print_string = quote o translate_string print_char;

val print_class = print_string;

val print_sort = print_list print_class;

fun print_typ (Type arg) =
      "Type " ^ print_pair print_string (print_list print_typ) arg
  | print_typ (TFree arg) =
      "TFree " ^ print_pair print_string print_sort arg
  | print_typ (TVar arg) =
      "TVar " ^ print_pair (print_pair print_string Int.toString) print_sort arg;

fun print_term (Const arg) =
      "Const " ^ print_pair print_string print_typ arg
  | print_term (Free arg) =
      "Free " ^ print_pair print_string print_typ arg
  | print_term (Var arg) =
      "Var " ^ print_pair (print_pair print_string Int.toString) print_typ arg
  | print_term (Bound i) =
      "Bound " ^ Int.toString i
  | print_term (Abs (s, T, t)) =
      "Abs (" ^ print_string s ^ ", " ^ print_typ T ^ ", " ^ print_term t ^ ")"
  | print_term (t1 $ t2) =
      "(" ^ print_term t1 ^ ") $ (" ^ print_term t2 ^ ")";

end;
