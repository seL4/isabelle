(*  Title:      Pure/Thy/document_antiquotation.ML
    Author:     Makarius

Document antiquotations.
*)

signature DOCUMENT_ANTIQUOTATION =
sig
  val thy_output_display: bool Config.T
  val thy_output_cartouche: bool Config.T
  val thy_output_quotes: bool Config.T
  val thy_output_margin: int Config.T
  val thy_output_indent: int Config.T
  val thy_output_source: bool Config.T
  val thy_output_source_cartouche: bool Config.T
  val thy_output_break: bool Config.T
  val thy_output_modes: string Config.T
  val trim_blanks: Proof.context -> string -> string
  val trim_lines: Proof.context -> string -> string
  val indent_lines: Proof.context -> string -> string
  val prepare_lines: Proof.context -> string -> string
  val delimit: Proof.context -> Pretty.T -> Pretty.T
  val indent: Proof.context -> Pretty.T -> Pretty.T
  val format: Proof.context -> Pretty.T -> string
  val output: Proof.context -> Pretty.T -> Output.output
  val print_antiquotations: bool -> Proof.context -> unit
  val check: Proof.context -> xstring * Position.T -> string
  val check_option: Proof.context -> xstring * Position.T -> string
  val setup: binding -> 'a context_parser ->
    ({context: Proof.context, source: Token.src, argument: 'a} -> Latex.text) -> theory -> theory
  val setup_embedded: binding -> 'a context_parser ->
    ({context: Proof.context, source: Token.src, argument: 'a} -> Latex.text) -> theory -> theory
  val setup_option: binding -> (string -> Proof.context -> Proof.context) -> theory -> theory
  val boolean: string -> bool
  val integer: string -> int
  val evaluate: (Symbol_Pos.T list -> Latex.text) -> Proof.context ->
    Antiquote.text_antiquote -> Latex.text
  val approx_content: Proof.context -> string -> string
end;

structure Document_Antiquotation: DOCUMENT_ANTIQUOTATION =
struct

(* options *)

val thy_output_display = Attrib.setup_option_bool ("thy_output_display", \<^here>);
val thy_output_break = Attrib.setup_option_bool ("thy_output_break", \<^here>);
val thy_output_cartouche = Attrib.setup_option_bool ("thy_output_cartouche", \<^here>);
val thy_output_quotes = Attrib.setup_option_bool ("thy_output_quotes", \<^here>);
val thy_output_margin = Attrib.setup_option_int ("thy_output_margin", \<^here>);
val thy_output_indent = Attrib.setup_option_int ("thy_output_indent", \<^here>);
val thy_output_source = Attrib.setup_option_bool ("thy_output_source", \<^here>);
val thy_output_source_cartouche = Attrib.setup_option_bool ("thy_output_source_cartouche", \<^here>);
val thy_output_modes = Attrib.setup_option_string ("thy_output_modes", \<^here>);


(* blanks *)

fun trim_blanks ctxt =
  not (Config.get ctxt thy_output_display) ? Symbol.trim_blanks;

fun trim_lines ctxt =
  if not (Config.get ctxt thy_output_display) then
    split_lines #> map Symbol.trim_blanks #> space_implode " "
  else I;

fun indent_lines ctxt =
  if Config.get ctxt thy_output_display then
    prefix_lines (Symbol.spaces (Config.get ctxt thy_output_indent))
  else I;

fun prepare_lines ctxt = trim_lines ctxt #> indent_lines ctxt;


(* output *)

fun delimit ctxt =
  if Config.get ctxt thy_output_cartouche then Pretty.cartouche
  else if Config.get ctxt thy_output_quotes then Pretty.quote
  else I;

fun indent ctxt =
  Config.get ctxt thy_output_display ? Pretty.indent (Config.get ctxt thy_output_indent);

fun format ctxt =
  if Config.get ctxt thy_output_display orelse Config.get ctxt thy_output_break
  then Pretty.string_of_margin (Config.get ctxt thy_output_margin)
  else Pretty.unformatted_string_of;

fun output ctxt = delimit ctxt #> indent ctxt #> format ctxt #> Output.output;


(* theory data *)

structure Data = Theory_Data
(
  type T =
    (bool * (Token.src -> Proof.context -> Latex.text)) Name_Space.table *
      (string -> Proof.context -> Proof.context) Name_Space.table;
  val empty : T =
    (Name_Space.empty_table Markup.document_antiquotationN,
      Name_Space.empty_table Markup.document_antiquotation_optionN);
  val extend = I;
  fun merge ((commands1, options1), (commands2, options2)) : T =
    (Name_Space.merge_tables (commands1, commands2),
      Name_Space.merge_tables (options1, options2));
);

val get_antiquotations = Data.get o Proof_Context.theory_of;

fun print_antiquotations verbose ctxt =
  let
    val (commands, options) = get_antiquotations ctxt;
    val command_names = map #1 (Name_Space.markup_table verbose ctxt commands);
    val option_names = map #1 (Name_Space.markup_table verbose ctxt options);
  in
    [Pretty.big_list "document antiquotations:" (map Pretty.mark_str command_names),
     Pretty.big_list "document antiquotation options:" (map Pretty.mark_str option_names)]
  end |> Pretty.writeln_chunks;

fun check ctxt = #1 o Name_Space.check (Context.Proof ctxt) (#1 (get_antiquotations ctxt));
fun check_option ctxt = #1 o Name_Space.check (Context.Proof ctxt) (#2 (get_antiquotations ctxt));

fun gen_setup name embedded scan body thy =
  let
    fun cmd src ctxt =
      let val (x, ctxt') = Token.syntax scan src ctxt
      in body {context = ctxt', source = src, argument = x} end;
    val entry = (name, (embedded, cmd));
  in thy |> Data.map (apfst (Name_Space.define (Context.Theory thy) true entry #> #2)) end;

fun setup name = gen_setup name false;
fun setup_embedded name = gen_setup name true;

fun setup_option name opt thy = thy
  |> Data.map (apsnd (Name_Space.define (Context.Theory thy) true (name, opt) #> #2));


(* syntax *)

local

val property =
  Parse.name_position -- Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.name) "";

val properties =
  Scan.optional (Parse.$$$ "[" |-- Parse.!!! (Parse.enum "," property --| Parse.$$$ "]")) [];

in

val parse_antiq =
  Parse.!!!
    (Parse.token Parse.liberal_name -- properties -- Parse.args --| Scan.ahead Parse.eof)
  >> (fn ((name, opts), args) => (opts, name :: args));

end;


(* evaluate *)

local

fun command pos (opts, src) ctxt =
  let
    val (src', (embedded, scan)) = Token.check_src ctxt (#1 o get_antiquotations) src;
    val _ =
      if null opts andalso Options.default_bool "update_control_cartouches" then
        Context_Position.reports_text ctxt
          (Antiquote.update_reports embedded pos (map Token.content_of src'))
      else ();
  in scan src' ctxt end;

fun option ((xname, pos), s) ctxt =
  let
    val (_, opt) =
      Name_Space.check (Context.Proof ctxt) (#2 (get_antiquotations ctxt)) (xname, pos);
  in opt s ctxt end;

fun eval ctxt pos (opts, src) =
  let
    val preview_ctxt = fold option opts (Config.put show_markup false ctxt);
    val _ = command pos (opts, src) preview_ctxt;

    val print_ctxt = Context_Position.set_visible false preview_ctxt;
    val print_modes =
      space_explode "," (Config.get print_ctxt thy_output_modes) @ [Latex.latexN, Pretty.regularN];
  in Print_Mode.with_modes print_modes (fn () => command pos (opts, src) print_ctxt) () end;

in

fun read_antiq ctxt ({range = (pos, _), body, ...}: Antiquote.antiq) =
  let val keywords = Thy_Header.get_keywords' ctxt;
  in Token.read_antiq keywords parse_antiq (body, pos) end;

fun evaluate eval_text ctxt antiq =
  (case antiq of
    Antiquote.Text ss => eval_text ss
  | Antiquote.Control {name, body, ...} =>
      eval ctxt Position.none
        ([], Token.make_src name (if null body then [] else [Token.read_cartouche body]))
  | Antiquote.Antiq antiq => eval ctxt (#1 (#range antiq)) (read_antiq ctxt antiq));

end;


(* approximative content, e.g. for index entries *)

local

val strip_symbols = [Symbol.open_, Symbol.close, "'", "\"", "`"];

fun strip_symbol sym =
  if member (op =) strip_symbols sym then ""
  else
    (case Symbol.decode sym of
      Symbol.Char s => s
    | Symbol.UTF8 s => s
    | Symbol.Sym s => s
    | Symbol.Control s => s
    | _ => "");

fun strip_antiq _ (Antiquote.Text body) = map Symbol_Pos.symbol body
  | strip_antiq _ (Antiquote.Control {body, ...}) = map Symbol_Pos.symbol body
  | strip_antiq ctxt (Antiquote.Antiq antiq) =
      read_antiq ctxt antiq |> #2 |> tl
      |> maps (Symbol.explode o Token.content_of);

in

fun approx_content ctxt =
  Symbol_Pos.explode0
  #> trim (Symbol.is_blank o Symbol_Pos.symbol)
  #> Antiquote.parse_comments Position.none
  #> maps (strip_antiq ctxt)
  #> map strip_symbol
  #> implode;

end;


(* option syntax *)

fun boolean "" = true
  | boolean "true" = true
  | boolean "false" = false
  | boolean s = error ("Bad boolean value: " ^ Library.quote s);

fun integer s =
  let
    fun int ss =
      (case Library.read_int ss of (i, []) => i
      | _ => error ("Bad integer value: " ^ Library.quote s));
  in (case Symbol.explode s of "-" :: ss => ~ (int ss) | ss => int ss) end;

val _ = Theory.setup
 (setup_option \<^binding>\<open>show_types\<close> (Config.put show_types o boolean) #>
  setup_option \<^binding>\<open>show_sorts\<close> (Config.put show_sorts o boolean) #>
  setup_option \<^binding>\<open>show_structs\<close> (Config.put show_structs o boolean) #>
  setup_option \<^binding>\<open>show_question_marks\<close> (Config.put show_question_marks o boolean) #>
  setup_option \<^binding>\<open>show_abbrevs\<close> (Config.put show_abbrevs o boolean) #>
  setup_option \<^binding>\<open>names_long\<close> (Config.put Name_Space.names_long o boolean) #>
  setup_option \<^binding>\<open>names_short\<close> (Config.put Name_Space.names_short o boolean) #>
  setup_option \<^binding>\<open>names_unique\<close> (Config.put Name_Space.names_unique o boolean) #>
  setup_option \<^binding>\<open>eta_contract\<close> (Config.put Syntax_Trans.eta_contract o boolean) #>
  setup_option \<^binding>\<open>display\<close> (Config.put thy_output_display o boolean) #>
  setup_option \<^binding>\<open>break\<close> (Config.put thy_output_break o boolean) #>
  setup_option \<^binding>\<open>cartouche\<close> (Config.put thy_output_cartouche o boolean) #>
  setup_option \<^binding>\<open>quotes\<close> (Config.put thy_output_quotes o boolean) #>
  setup_option \<^binding>\<open>mode\<close> (Config.put thy_output_modes) #>
  setup_option \<^binding>\<open>margin\<close> (Config.put thy_output_margin o integer) #>
  setup_option \<^binding>\<open>indent\<close> (Config.put thy_output_indent o integer) #>
  setup_option \<^binding>\<open>source\<close> (Config.put thy_output_source o boolean) #>
  setup_option \<^binding>\<open>source_cartouche\<close> (Config.put thy_output_source_cartouche o boolean) #>
  setup_option \<^binding>\<open>goals_limit\<close> (Config.put Goal_Display.goals_limit o integer));

end;
