(*  Title:      Pure/Thy/latex.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Simple LaTeX presentation primitives (based on outer lexical syntax).
*)

signature LATEX =
sig
  val token_source: OuterLex.token list -> string
  val theory_entry: string -> string
end;

structure Latex: LATEX =
struct


(* symbol output *)

local

val output_chr = fn
  " " => "~" |
  "\n" => "\\isanewline\n" |
  "$" => "\\$" |
  "&" => "\\&" |
  "%" => "\\%" |
  "#" => "\\#" |
  "_" => "\\_" |
  "{" => "{\\textbraceleft}" |
  "}" => "{\\textbraceright}" |
  "~" => "{\\textasciitilde}" |
  "^" => "{\\textasciicircum}" |
(*  "\"" => "{\\textquotedblleft}" |    (* FIXME !? *)*)
  "\\" => "{\\textbackslash}" |
(*  "|" => "{\\textbar}" |
  "<" => "{\\textless}" |
  ">" => "{\\textgreater}" |  *)
  c => c;

in

(* FIXME replace \<forall> etc. *)
val output_symbol = implode o map output_chr o explode;
val output_symbols = map output_symbol;

end;


(* token output *)

local

structure T = OuterLex;

fun output_tok tok =
  let
    val out = output_symbol;
    val s = T.val_of tok;
  in
    if T.is_kind T.Command tok then "\\isacommand{" ^ out s ^ "}"
    else if T.is_kind T.Keyword tok then "\\isakeyword{" ^ out s ^ "}"
    else if T.is_kind T.String tok then out (quote s)
    else if T.is_kind T.Verbatim tok then "\\isatext{" ^ s ^ "}"
    else out s
  end;

(*adhoc tuning of tokens*)
fun invisible_token tok =
  T.is_kind T.Command tok andalso T.val_of tok mem_string ["text", "txt"] orelse
  T.keyword_with (equal ";") tok orelse T.is_kind T.Comment tok;

in

val output_tokens = map output_tok o filter_out invisible_token;

end;


(* theory presentation *)

fun token_source toks =
  "\\begin{isabellesimple}\n" ^ implode (output_tokens toks) ^ "\\end{isabellesimple}\n";

fun theory_entry name = "\\input{" ^ name ^ ".tex}\n";


end;
