(*  Title:      Pure/Thy/latex.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

LaTeX presentation primitives (based on outer lexical syntax).
*)

signature LATEX =
sig
  val output_known_symbols: (string -> bool) * (string -> bool) ->
    Symbol.symbol list -> string
  val output_symbols: Symbol.symbol list -> string
  datatype token = Basic of OuterLex.token | Markup of string | MarkupEnv of string | Verbatim
  val output_tokens: (token * string) list -> string
  val flag_markup: bool -> string
  val tex_trailer: string
  val isabelle_file: string -> string -> string
  val symbol_source: (string -> bool) * (string -> bool) ->
    string -> Symbol.symbol list -> string
  val theory_entry: string -> string
  val modes: string list
end;

structure Latex: LATEX =
struct


(* symbol output *)

local

val output_chr = fn
  " " => "\\ " |
  "\n" => "\\isanewline\n" |
  "!" => "{\\isacharbang}" |
  "\"" => "{\\isachardoublequote}" |
  "#" => "{\\isacharhash}" |
  "$" => "{\\isachardollar}" |
  "%" => "{\\isacharpercent}" |
  "&" => "{\\isacharampersand}" |
  "'" => "{\\isacharprime}" |
  "(" => "{\\isacharparenleft}" |
  ")" => "{\\isacharparenright}" |
  "*" => "{\\isacharasterisk}" |
  "+" => "{\\isacharplus}" |
  "," => "{\\isacharcomma}" |
  "-" => "{\\isacharminus}" |
  "." => "{\\isachardot}" |
  "/" => "{\\isacharslash}" |
  ":" => "{\\isacharcolon}" |
  ";" => "{\\isacharsemicolon}" |
  "<" => "{\\isacharless}" |
  "=" => "{\\isacharequal}" |
  ">" => "{\\isachargreater}" |
  "?" => "{\\isacharquery}" |
  "@" => "{\\isacharat}" |
  "[" => "{\\isacharbrackleft}" |
  "\\" => "{\\isacharbackslash}" |
  "]" => "{\\isacharbrackright}" |
  "^" => "{\\isacharcircum}" |
  "_" => "{\\isacharunderscore}" |
  "`" => "{\\isacharbackquote}" |
  "{" => "{\\isacharbraceleft}" |
  "|" => "{\\isacharbar}" |
  "}" => "{\\isacharbraceright}" |
  "~" => "{\\isachartilde}" |
  c => if Symbol.is_digit c then enclose "{\\isadigit{" "}}" c else c;

val output_chrs = translate_string output_chr;

fun output_known_sym (known_sym, known_ctrl) sym =
  (case Symbol.decode sym of
    Symbol.Char s => output_chr s
  | Symbol.Sym s => if known_sym s then enclose "{\\isasym" "}" s else output_chrs sym
  | Symbol.Ctrl s => if known_ctrl s then enclose "\\isactrl" " " s else output_chrs sym
  | Symbol.Raw s => s);

in

val output_known_symbols = implode oo (map o output_known_sym);
val output_symbols = output_known_symbols (K true, K true);
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

fun output_tok (Basic tok, _) =
      let val s = T.val_of tok in
        if invisible_token tok then ""
        else if T.is_kind T.Command tok then
          "\\isacommand{" ^ output_syms s ^ "}"
        else if T.is_kind T.Keyword tok andalso Syntax.is_ascii_identifier s then
          "\\isakeyword{" ^ output_syms s ^ "}"
        else if T.is_kind T.String tok then output_syms (Library.quote s)
        else if T.is_kind T.Verbatim tok then output_syms (enclose "{*" "*}" s)
        else output_syms s
      end
  | output_tok (Markup cmd, txt) =
      "%\n\\isamarkup" ^ cmd ^ "{" ^ Symbol.strip_blanks txt ^ "%\n}\n"
  | output_tok (MarkupEnv cmd, txt) = "%\n\\begin{isamarkup" ^ cmd ^ "}%\n" ^
      Symbol.strip_blanks txt ^ "%\n\\end{isamarkup" ^ cmd ^ "}%\n"
  | output_tok (Verbatim, txt) = "%\n" ^ Symbol.strip_blanks txt ^ "\n";


val output_tokens = implode o map output_tok;


fun flag_markup true = "\\isamarkuptrue%\n"
  | flag_markup false = "\\isamarkupfalse%\n";


(* theory presentation *)

val tex_trailer =
  "%%% Local Variables:\n\
  \%%% mode: latex\n\
  \%%% TeX-master: \"root\"\n\
  \%%% End:\n";

fun isabelle_file name txt =
  "%\n\\begin{isabellebody}%\n\
  \\\def\\isabellecontext{" ^ output_syms name ^ "}%\n" ^ txt ^
  "\\end{isabellebody}%\n" ^ tex_trailer;

fun symbol_source known name syms = isabelle_file name
  ("\\isamarkupheader{" ^ output_known_symbols known (Symbol.explode name) ^ "}%\n" ^
    output_known_symbols known syms);

fun theory_entry name = "\\input{" ^ name ^ ".tex}\n\n";


(* print mode *)

val latexN = "latex";
val modes = [latexN, Symbol.xsymbolsN, Symbol.symbolsN];

fun latex_output str =
  let val syms = Symbol.explode str
  in (output_symbols syms, real (Symbol.length syms)) end;

fun latex_indent "" = ""
  | latex_indent s = enclose "\\isaindent{" "}" s;

val _ = Output.add_mode latexN (latex_output, latex_indent o #1, Symbol.default_raw);


end;
