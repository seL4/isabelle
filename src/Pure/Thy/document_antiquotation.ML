(*  Title:      Pure/Thy/document_antiquotation.ML
    Author:     Makarius

Document antiquotations.
*)

signature DOCUMENT_ANTIQUOTATION =
sig
  val thy_output_display: bool Config.T
  val thy_output_quotes: bool Config.T
  val thy_output_margin: int Config.T
  val thy_output_indent: int Config.T
  val thy_output_source: bool Config.T
  val thy_output_break: bool Config.T
  val thy_output_modes: string Config.T
  val print_antiquotations: bool -> Proof.context -> unit
  val check: Proof.context -> xstring * Position.T -> string
  val check_option: Proof.context -> xstring * Position.T -> string
  val setup: binding -> 'a context_parser ->
    ({source: Token.src, context: Proof.context} -> 'a -> string) -> theory -> theory
  val setup_option: binding -> (string -> Proof.context -> Proof.context) -> theory -> theory
  val boolean: string -> bool
  val integer: string -> int
  val evaluate: Proof.context -> Antiquote.text_antiquote -> string
end;

structure Document_Antiquotation: DOCUMENT_ANTIQUOTATION =
struct

(* options *)

val thy_output_display = Attrib.setup_option_bool ("thy_output_display", \<^here>);
val thy_output_break = Attrib.setup_option_bool ("thy_output_break", \<^here>);
val thy_output_quotes = Attrib.setup_option_bool ("thy_output_quotes", \<^here>);
val thy_output_margin = Attrib.setup_option_int ("thy_output_margin", \<^here>);
val thy_output_indent = Attrib.setup_option_int ("thy_output_indent", \<^here>);
val thy_output_source = Attrib.setup_option_bool ("thy_output_source", \<^here>);
val thy_output_modes = Attrib.setup_option_string ("thy_output_modes", \<^here>);


(* theory data *)

structure Data = Theory_Data
(
  type T =
    (Token.src -> Proof.context -> string) Name_Space.table *
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

fun setup name scan body thy =
  let
    fun cmd src ctxt =
      let val (x, ctxt') = Token.syntax scan src ctxt
      in body {source = src, context = ctxt'} x end;
  in thy |> Data.map (apfst (Name_Space.define (Context.Theory thy) true (name, cmd) #> #2)) end;

fun setup_option name opt thy = thy
  |> Data.map (apsnd (Name_Space.define (Context.Theory thy) true (name, opt) #> #2));


(* syntax *)

local

val property =
  Parse.position Parse.name -- Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.name) "";

val properties =
  Scan.optional (Parse.$$$ "[" |-- Parse.!!! (Parse.enum "," property --| Parse.$$$ "]")) [];

in

val antiq =
  Parse.!!!
    (Parse.token Parse.liberal_name -- properties -- Parse.args --| Scan.ahead Parse.eof)
  >> (fn ((name, props), args) => (props, name :: args));

end;


(* evaluate *)

local

fun command src ctxt =
  let val (src', f) = Token.check_src ctxt (#1 o get_antiquotations) src
  in f src' ctxt end;

fun option ((xname, pos), s) ctxt =
  let
    val (_, opt) =
      Name_Space.check (Context.Proof ctxt) (#2 (get_antiquotations ctxt)) (xname, pos);
  in opt s ctxt end;

fun eval ctxt (opts, src) =
  let
    val preview_ctxt = fold option opts ctxt;
    val print_ctxt = Context_Position.set_visible false preview_ctxt;
    val print_modes = space_explode "," (Config.get print_ctxt thy_output_modes) @ [Latex.latexN];
  in Print_Mode.with_modes print_modes (fn () => command src print_ctxt) () end;

in

fun evaluate _ (Antiquote.Text ss) = Symbol_Pos.content ss
  | evaluate ctxt (Antiquote.Control {name, body, ...}) =
      eval ctxt ([], Token.make_src name (if null body then [] else [Token.read_cartouche body]))
  | evaluate ctxt (Antiquote.Antiq {range = (pos, _), body, ...}) =
      let val keywords = Thy_Header.get_keywords' ctxt;
      in eval ctxt (Token.read_antiq keywords antiq (body, pos)) end;

end;


(* option syntax *)

fun boolean "" = true
  | boolean "true" = true
  | boolean "false" = false
  | boolean s = error ("Bad boolean value: " ^ quote s);

fun integer s =
  let
    fun int ss =
      (case Library.read_int ss of (i, []) => i
      | _ => error ("Bad integer value: " ^ quote s));
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
  setup_option \<^binding>\<open>quotes\<close> (Config.put thy_output_quotes o boolean) #>
  setup_option \<^binding>\<open>mode\<close> (Config.put thy_output_modes) #>
  setup_option \<^binding>\<open>margin\<close> (Config.put thy_output_margin o integer) #>
  setup_option \<^binding>\<open>indent\<close> (Config.put thy_output_indent o integer) #>
  setup_option \<^binding>\<open>source\<close> (Config.put thy_output_source o boolean) #>
  setup_option \<^binding>\<open>goals_limit\<close> (Config.put Goal_Display.goals_limit o integer));

end;
