(*  Title:      Pure/Thy/latex.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Simple LaTeX presentation primitives (based on outer lexical syntax).
*)

signature LATEX =
sig
  val token_source: (OuterLex.token * string option) list -> string
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
(*  "\\" => "{\\textbackslash}" |  FIXME *)
  "\\" => "\\verb,\\," |
  "|" => "{|}" |
  "<" => "{<}" |
  ">" => "{>}" |
  c => c;


(* FIXME replace \<forall> etc. *)
val output_sym = implode o map output_chr o explode;
val output_symbols = map output_sym;


(* token output *)

structure T = OuterLex;

fun output_tok (tok, Some s) = "\\isamarkup" ^ T.val_of tok ^ "{" ^ s ^ "}"
  | output_tok (tok, None) =
      let val s = T.val_of tok in
        if T.is_kind T.Command tok then "\\isacommand{" ^ output_sym s ^ "}"
        else if T.is_kind T.Keyword tok then "\\isakeyword{" ^ output_sym s ^ "}"
        else if T.is_kind T.String tok then output_sym (quote s)
        else if T.is_kind T.Verbatim tok then output_sym (enclose "{*" "*}" s)
        else output_sym s
      end;

val output_tokens = map output_tok;


(* theory presentation *)

fun token_source toks =
  "\\begin{isabellesimple}\n" ^ implode (output_tokens toks) ^ "\\end{isabellesimple}\n";

fun theory_entry name = "\\input{" ^ name ^ ".tex}\n";


end;
