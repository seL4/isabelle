(*  Title:      Pure/Thy/latex.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Simple LaTeX presentation primitives (based on outer lexical syntax).
*)

signature LATEX =
sig
  datatype token = Basic of OuterLex.token | Markup of string * string | Verbatim of string
  val token_source: token list -> string
  val theory_entry: string -> string
end;

structure Latex: LATEX =
struct


(* symbol output *)

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
  "\"" => "{\"}" |
  "\\" => "\\verb,\\," |
  c => c;

val output_chr' = fn
  "\\" => "{\\textbackslash}" |
  "|" => "{\\textbar}" |
  "<" => "{\\textless}" |
  ">" => "{\\textgreater}" |
  c => output_chr c;


(* FIXME replace \<forall> etc. *)
val output_sym = implode o map output_chr o explode;
val output_sym' = implode o map output_chr' o explode;


(* token output *)

structure T = OuterLex;

datatype token = Basic of T.token | Markup of string * string | Verbatim of string;


val invisible_token = T.keyword_with (equal ";") orf T.is_kind T.Comment;

fun strip_blanks s =
  implode (#1 (Library.take_suffix Symbol.is_blank
    (#2 (Library.take_prefix Symbol.is_blank (explode s)))));

fun output_tok (Basic tok) =
      let val s = T.val_of tok in
        if invisible_token tok then ""
        else if T.is_kind T.Command tok then "\\isacommand{" ^ output_sym' s ^ "}"
        else if T.is_kind T.Keyword tok then "\\isakeyword{" ^ output_sym' s ^ "}"
        else if T.is_kind T.String tok then output_sym (quote s)
        else if T.is_kind T.Verbatim tok then output_sym (enclose "{*" "*}" s)
        else output_sym s
      end
  | output_tok (Markup (cmd, arg)) = "\n\\isamarkup" ^ cmd ^ "{" ^ strip_blanks arg ^ "}\n"
  | output_tok (Verbatim txt) = "\n" ^ txt ^ "\n";


val output_tokens = implode o map output_tok;


(* theory presentation *)

fun token_source toks =
  "\\begin{isabellesimple}\n" ^ output_tokens toks ^ "\\end{isabellesimple}\n";

fun theory_entry name = "\\input{" ^ name ^ ".tex}\n";


end;
