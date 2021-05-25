(*  Title:      Pure/Thy/latex.ML
    Author:     Makarius

LaTeX output of theory sources.
*)

signature LATEX =
sig
  type text
  val string: string -> text
  val text: string * Position.T -> text
  val block: text list -> text
  val enclose_body: string -> string -> text list -> text list
  val enclose_block: string -> string -> text list -> text
  val output_text: text list -> string
  val output_positions: Position.T -> text list -> string
  val output_name: string -> string
  val output_ascii: string -> string
  val output_ascii_breakable: string -> string -> string
  val output_symbols: Symbol.symbol list -> string
  val output_syms: string -> string
  val symbols: Symbol_Pos.T list -> text
  val symbols_output: Symbol_Pos.T list -> text
  val begin_delim: string -> string
  val end_delim: string -> string
  val begin_tag: string -> string
  val end_tag: string -> string
  val environment_block: string -> text list -> text
  val environment: string -> string -> string
  val isabelle_body: string -> text list -> text list
  val theory_entry: string -> string
  val index_escape: string -> string
  type index_item = {text: text, like: string}
  type index_entry = {items: index_item list, def: bool}
  val index_entry: index_entry -> text
  val index_variants: (binding -> bool option -> 'a -> 'a) -> binding -> 'a -> 'a
  val latexN: string
  val latex_output: string -> string * int
  val latex_markup: string * Properties.T -> Markup.output
  val latex_indent: string -> int -> string
end;

structure Latex: LATEX =
struct

(* text with positions *)

abstype text = Text of string * Position.T | Block of text list
with

fun string s = Text (s, Position.none);
val text = Text;
val block = Block;

fun map_text f (Text (s, pos)) = Text (f s, pos)
  | map_text f (Block texts) = Block ((map o map_text) f texts);

fun output_text texts =
  let
    fun output (Text (s, _)) = Buffer.add s
      | output (Block body) = fold output body;
  in Buffer.empty |> fold output texts |> Buffer.content end;

fun output_positions file_pos texts =
  let
    fun position (a, b) = enclose "%:%" "%:%" (a ^ "=" ^ b);
    fun add_position p positions =
      let val s = position (apply2 Value.print_int p)
      in positions |> s <> hd positions ? cons s end;

    fun output (Text (s, pos)) (positions, line) =
          let
            val positions' =
              (case Position.line_of pos of
                NONE => positions
              | SOME l => add_position (line, l) positions);
            val line' = fold_string (fn c => fn n => if c = "\n" then n + 1 else n) s line;
          in (positions', line') end
      | output (Block body) res = fold output body res;
  in
    (case Position.file_of file_pos of
      NONE => ""
    | SOME file =>
        ([position (Markup.fileN, file), "\\endinput"], 1)
        |> fold output texts |> #1 |> rev |> cat_lines)
  end;

end;

fun enclose_body bg en body =
  (if bg = "" then [] else [string bg]) @ body @
  (if en = "" then [] else [string en]);

fun enclose_block bg en = block o enclose_body bg en;


(* output name for LaTeX macros *)

val output_name =
  translate_string
    (fn "_" => "UNDERSCORE"
      | "'" => "PRIME"
      | "0" => "ZERO"
      | "1" => "ONE"
      | "2" => "TWO"
      | "3" => "THREE"
      | "4" => "FOUR"
      | "5" => "FIVE"
      | "6" => "SIX"
      | "7" => "SEVEN"
      | "8" => "EIGHT"
      | "9" => "NINE"
      | s => s);

fun enclose_name bg en = enclose bg en o output_name;


(* output verbatim ASCII *)

val output_ascii =
  translate_string
    (fn " " => "\\ "
      | "\t" => "\\ "
      | "\n" => "\\isanewline\n"
      | s =>
          s
          |> exists_string (fn s' => s = s') "\"#$%&',-<>\\^_`{}~" ? enclose "{\\char`\\" "}"
          |> suffix "{\\kern0pt}");

fun output_ascii_breakable sep =
  space_explode sep
  #> map output_ascii
  #> space_implode (output_ascii sep ^ "\\discretionary{}{}{}");


(* output symbols *)

local

val char_table =
  Symtab.make
   [("\007", "{\\isacharbell}"),
    ("!", "{\\isacharbang}"),
    ("\"", "{\\isachardoublequote}"),
    ("#", "{\\isacharhash}"),
    ("$", "{\\isachardollar}"),
    ("%", "{\\isacharpercent}"),
    ("&", "{\\isacharampersand}"),
    ("'", "{\\isacharprime}"),
    ("(", "{\\isacharparenleft}"),
    (")", "{\\isacharparenright}"),
    ("*", "{\\isacharasterisk}"),
    ("+", "{\\isacharplus}"),
    (",", "{\\isacharcomma}"),
    ("-", "{\\isacharminus}"),
    (".", "{\\isachardot}"),
    ("/", "{\\isacharslash}"),
    (":", "{\\isacharcolon}"),
    (";", "{\\isacharsemicolon}"),
    ("<", "{\\isacharless}"),
    ("=", "{\\isacharequal}"),
    (">", "{\\isachargreater}"),
    ("?", "{\\isacharquery}"),
    ("@", "{\\isacharat}"),
    ("[", "{\\isacharbrackleft}"),
    ("\\", "{\\isacharbackslash}"),
    ("]", "{\\isacharbrackright}"),
    ("^", "{\\isacharcircum}"),
    ("_", "{\\isacharunderscore}"),
    ("`", "{\\isacharbackquote}"),
    ("{", "{\\isacharbraceleft}"),
    ("|", "{\\isacharbar}"),
    ("}", "{\\isacharbraceright}"),
    ("~", "{\\isachartilde}")];

fun output_chr " " = "\\ "
  | output_chr "\t" = "\\ "
  | output_chr "\n" = "\\isanewline\n"
  | output_chr c =
      (case Symtab.lookup char_table c of
        SOME s => s ^ "{\\kern0pt}"
      | NONE => if Symbol.is_ascii_digit c then enclose "{\\isadigit{" "}}" c else c);

fun output_sym sym =
  (case Symbol.decode sym of
    Symbol.Char s => output_chr s
  | Symbol.UTF8 s => s
  | Symbol.Sym s => enclose_name "{\\isasym" "}" s
  | Symbol.Control s => enclose_name "\\isactrl" " " s
  | Symbol.Malformed s => error (Symbol.malformed_msg s)
  | Symbol.EOF => error "Bad EOF symbol");

open Basic_Symbol_Pos;

val scan_latex_length =
  Scan.many1 (fn (s, _) => s <> Symbol.latex andalso Symbol.not_eof s)
    >> (Symbol.length o map Symbol_Pos.symbol) ||
  $$ Symbol.latex -- Scan.option (Scan.permissive Symbol_Pos.scan_cartouche "") >> K 0;

val scan_latex =
  $$ Symbol.latex |-- Symbol_Pos.scan_cartouche_content "Embedded LaTeX: "
    >> (implode o map Symbol_Pos.symbol) ||
  Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> (output_sym o Symbol_Pos.symbol);

fun read scan syms =
  Scan.read Symbol_Pos.stopper (Scan.repeat scan) (map (rpair Position.none) syms);

in

fun length_symbols syms =
  fold Integer.add (these (read scan_latex_length syms)) 0;

fun output_symbols syms =
  if member (op =) syms Symbol.latex then
    (case read scan_latex syms of
      SOME ss => implode ss
    | NONE => error ("Malformed embedded LaTeX: " ^ quote (Symbol.beginning 10 syms)))
  else implode (map output_sym syms);

val output_syms = output_symbols o Symbol.explode;

end;

fun symbols syms = text (Symbol_Pos.content syms, #1 (Symbol_Pos.range syms));
fun symbols_output syms =
  text (output_symbols (map Symbol_Pos.symbol syms), #1 (Symbol_Pos.range syms));


(* tags *)

val begin_delim = enclose_name "%\n\\isadelim" "\n";
val end_delim = enclose_name "%\n\\endisadelim" "\n";
val begin_tag = enclose_name "%\n\\isatag" "\n";
fun end_tag tg = enclose_name "%\n\\endisatag" "\n" tg ^ enclose "{\\isafold" "}%\n" tg;


(* theory presentation *)

fun environment_delim name =
 ("%\n\\begin{" ^ output_name name ^ "}%\n",
  "%\n\\end{" ^ output_name name ^ "}");

fun environment_block name = environment_delim name |-> enclose_body #> block;
fun environment name = environment_delim name |-> enclose;

fun isabelle_body name =
  enclose_body
   ("%\n\\begin{isabellebody}%\n\\setisabellecontext{" ^ output_syms name ^ "}%\n")
   "%\n\\end{isabellebody}%\n";

fun theory_entry name = "\\input{" ^ name ^ ".tex}\n\n";


(* index entries *)

type index_item = {text: text, like: string};
type index_entry = {items: index_item list, def: bool};

val index_escape =
  translate_string (fn s =>
    if member_string "!\"@|" s then "\\char" ^ string_of_int (ord s)
    else if member_string "\\{}#" s then "\"" ^ s else s);

fun index_item (item: index_item) =
  let
    val like_text =
      if #like item = "" then ""
      else index_escape (#like item) ^ "@";
    val item_text = index_escape (output_text [#text item]);
  in like_text ^ item_text end;

fun index_entry (entry: index_entry) =
  (space_implode "!" (map index_item (#items entry)) ^
    "|" ^ index_escape (if #def entry then "isaindexdef" else "isaindexref"))
  |> enclose "\\index{" "}"
  |> string;

fun index_binding NONE = I
  | index_binding (SOME def) = Binding.map_name (suffix (if def then "_def" else "_ref"));

fun index_variants setup binding =
  fold (fn index => setup (index_binding index binding) index) [NONE, SOME true, SOME false];


(* print mode *)

val latexN = "latex";

fun latex_output str =
  let val syms = Symbol.explode str
  in (output_symbols syms, length_symbols syms) end;

fun latex_markup (s, _: Properties.T) =
  if s = Markup.commandN orelse s = Markup.keyword1N orelse s = Markup.keyword3N
  then ("\\isacommand{", "}")
  else if s = Markup.keyword2N
  then ("\\isakeyword{", "}")
  else Markup.no_output;

fun latex_indent "" _ = ""
  | latex_indent s _ = enclose "\\isaindent{" "}" s;

val _ = Output.add_mode latexN latex_output (prefix Symbol.latex o cartouche);
val _ = Markup.add_mode latexN latex_markup;
val _ = Pretty.add_mode latexN latex_indent;

end;
