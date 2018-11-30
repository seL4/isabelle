(*  Title:      Pure/Tools/ghc.ML
    Author:     Makarius

Support for GHC: Glasgow Haskell Compiler.
*)

signature GHC =
sig
  val print_codepoint: UTF8.codepoint -> string
  val print_symbol: Symbol.symbol -> string
  val print_string: string -> string
end;

structure GHC: GHC =
struct

(** string literals **)

fun print_codepoint c =
  (case c of
    34 => "\\\""
  | 39 => "\\'"
  | 92 => "\\\\"
  | 7 => "\\a"
  | 8 => "\\b"
  | 9 => "\\t"
  | 10 => "\\n"
  | 11 => "\\v"
  | 12 => "\\f"
  | 13 => "\\r"
  | c =>
      if c >= 32 andalso c < 127 then chr c
      else "\\" ^ string_of_int c ^ "\\&");

fun print_symbol sym =
  (case Symbol.decode sym of
    Symbol.Char s => print_codepoint (ord s)
  | Symbol.UTF8 s => UTF8.decode_permissive s |> map print_codepoint |> implode
  | Symbol.Sym s => "\\092<" ^ s ^ ">"
  | Symbol.Control s => "\\092<^" ^ s ^ ">"
  | _ => translate_string (print_codepoint o ord) sym);

val print_string = quote o implode o map print_symbol o Symbol.explode;

end;
