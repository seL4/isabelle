(*  Title:      Pure/Thy/latex.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

LaTeX presentation primitives (based on outer lexical syntax).
*)

signature LATEX =
sig
  datatype token = Basic of OuterLex.token | Markup of string | MarkupEnv of string | Verbatim
  val output_tokens: (token * string) list -> string
  val isabelle_file: string -> string
  val old_symbol_source: string -> Symbol.symbol list -> string
  val theory_entry: string -> string
  val modes: string list
  val setup: (theory -> theory) list
end;

structure Latex: LATEX =
struct


(* symbol output *)

local

val output_chr = fn
  " " => "\\ " |
  "\n" => "\\isanewline\n" |
  "$" => "\\$" |
  "&" => "\\&" |
  "%" => "\\%" |
  "#" => "\\#" |
  "_" => "\\_" |
  "{" => "{\\isabraceleft}" |
  "}" => "{\\isabraceright}" |
  "~" => "{\\isatilde}" |
  "^" => "{\\isacircum}" |
  "\"" => "{\"}" |
  "\\" => "{\\isabackslash}" |
  c => c;

fun output_sym s =
  if size s = 1 then output_chr s
  else
    (case explode s of
      cs as "\\" :: "<" :: "^" :: _ => implode (map output_chr cs)
    | "\\" :: "<" :: cs => "{\\isasym" ^ implode (#1 (Library.split_last cs)) ^ "}"
    | _ => sys_error "output_sym");

in

val output_symbols = implode o map output_sym;
val output_syms = output_symbols o Symbol.explode;

end;


(* token output *)

structure T = OuterLex;

datatype token =
  Basic of T.token |
  Markup of string |
  MarkupEnv of string |
  Verbatim;


val invisible_token = T.keyword_with (equal ";") orf T.is_kind T.Comment;

fun strip_blanks s =
  implode (#1 (Library.take_suffix Symbol.is_blank
    (#2 (Library.take_prefix Symbol.is_blank (explode s)))));

fun output_tok (Basic tok, _) =
      let val s = T.val_of tok in
        if invisible_token tok then ""
        else if T.is_kind T.Command tok then
          if s = "{" then "{\\isabeginblock}"
          else if s = "}" then "{\\isaendblock}"
          else "\\isacommand{" ^ output_syms s ^ "}"
        else if T.is_kind T.Keyword tok andalso Syntax.is_identifier s then
          "\\isakeyword{" ^ output_syms s ^ "}"
        else if T.is_kind T.String tok then output_syms (quote s)
        else if T.is_kind T.Verbatim tok then output_syms (enclose "{*" "*}" s)
        else output_syms s
      end
  | output_tok (Markup cmd, txt) = "%\n\\isamarkup" ^ cmd ^ "{" ^ strip_blanks txt ^ "}\n"
  | output_tok (MarkupEnv cmd, txt) = "%\n\\begin{isamarkup" ^ cmd ^ "}%\n" ^
      strip_blanks txt ^ "%\n\\end{isamarkup" ^ cmd ^ "}%\n"
  | output_tok (Verbatim, txt) = "%\n" ^ strip_blanks txt ^ "\n";


val output_tokens = implode o map output_tok;


(* theory presentation *)

val isabelle_file = enclose
  "\\begin{isabelle}%\n"
  "\\end{isabelle}%\n\
  \%%% Local Variables:\n\
  \%%% mode: latex\n\
  \%%% TeX-master: \"root\"\n\
  \%%% End:\n";

fun old_symbol_source name syms =
  isabelle_file ("\\isamarkupheader{" ^ output_syms name ^ "}%\n" ^ output_symbols syms);

fun theory_entry name = "\\input{" ^ name ^ ".tex}\n\n";


(* print mode *)

val latexN = "latex";
val modes = [latexN, Symbol.xsymbolsN, Symbol.symbolsN];

fun latex_output str =
  let val syms = Symbol.explode str
  in (output_symbols syms, real (Symbol.length syms)) end;

val token_translation =
  map (fn s => (latexN, s, apfst (enclose "\\mbox{" "}") o latex_output))
    Syntax.standard_token_classes;

val _ = Symbol.add_mode latexN latex_output;
val setup = [Theory.add_tokentrfuns token_translation];


end;
