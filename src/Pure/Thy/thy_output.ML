(*  Title:      Pure/Thy/thy_output.ML
    Author:     Markus Wenzel, TU Muenchen

Theory document output with antiquotations.
*)

signature THY_OUTPUT =
sig
  val display_default: bool Unsynchronized.ref
  val quotes_default: bool Unsynchronized.ref
  val indent_default: int Unsynchronized.ref
  val source_default: bool Unsynchronized.ref
  val break_default: bool Unsynchronized.ref
  val display: bool Config.T
  val quotes: bool Config.T
  val indent: int Config.T
  val source: bool Config.T
  val break: bool Config.T
  val add_wrapper: ((unit -> string) -> unit -> string) -> Proof.context -> Proof.context
  val add_option: binding -> (string -> Proof.context -> Proof.context) -> theory -> theory
  val intern_command: theory -> xstring -> string
  val defined_command: theory -> string -> bool
  val intern_option: theory -> xstring -> string
  val defined_option: theory -> string -> bool
  val print_antiquotations: Proof.context -> unit
  val antiquotation: binding -> 'a context_parser ->
    ({source: Args.src, state: Toplevel.state, context: Proof.context} -> 'a -> string) ->
      theory -> theory
  val boolean: string -> bool
  val integer: string -> int
  datatype markup = Markup | MarkupEnv | Verbatim
  val modes: string list Unsynchronized.ref
  val eval_antiq: Scan.lexicon -> Toplevel.state -> Symbol_Pos.T list * Position.range -> string
  val eval_antiquote: Scan.lexicon -> Toplevel.state -> Symbol_Pos.text * Position.T -> string
  val present_thy: Scan.lexicon -> (string -> string list) -> (markup -> string -> bool) ->
    (Toplevel.transition * Toplevel.state) list -> Token.T list -> Buffer.T
  val pretty_text: Proof.context -> string -> Pretty.T
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val str_of_source: Args.src -> string
  val maybe_pretty_source: (Proof.context -> 'a -> Pretty.T) -> Proof.context ->
    Args.src -> 'a list -> Pretty.T list
  val output: Proof.context -> Pretty.T list -> string
end;

structure Thy_Output: THY_OUTPUT =
struct

(** global options **)

val display_default = Unsynchronized.ref false;
val quotes_default = Unsynchronized.ref false;
val indent_default = Unsynchronized.ref 0;
val source_default = Unsynchronized.ref false;
val break_default = Unsynchronized.ref false;

val display = Attrib.setup_config_bool (Binding.name "thy_output_display") (fn _ => ! display_default);
val quotes = Attrib.setup_config_bool (Binding.name "thy_output_quotes") (fn _ => ! quotes_default);
val indent = Attrib.setup_config_int (Binding.name "thy_output_indent") (fn _ => ! indent_default);
val source = Attrib.setup_config_bool (Binding.name "thy_output_source") (fn _ => ! source_default);
val break = Attrib.setup_config_bool (Binding.name "thy_output_break") (fn _ => ! break_default);


structure Wrappers = Proof_Data
(
  type T = ((unit -> string) -> unit -> string) list;
  fun init _ = [];
);

fun add_wrapper wrapper = Wrappers.map (cons wrapper);

val wrap = Wrappers.get #> fold (fn wrapper => fn f => wrapper f);



(** maintain global antiquotations **)

structure Antiquotations = Theory_Data
(
  type T =
    (Args.src -> Toplevel.state -> Proof.context -> string) Name_Space.table *
      (string -> Proof.context -> Proof.context) Name_Space.table;
  val empty : T =
    (Name_Space.empty_table Isabelle_Markup.doc_antiquotationN,
      Name_Space.empty_table Isabelle_Markup.doc_antiquotation_optionN);
  val extend = I;
  fun merge ((commands1, options1), (commands2, options2)) : T =
    (Name_Space.merge_tables (commands1, commands2),
      Name_Space.merge_tables (options1, options2));
);

fun add_command name cmd thy = thy
  |> Antiquotations.map (apfst (Name_Space.define (Context.Theory thy) true (name, cmd) #> snd));

fun add_option name opt thy = thy
  |> Antiquotations.map (apsnd (Name_Space.define (Context.Theory thy) true (name, opt) #> snd));

val intern_command = Name_Space.intern o #1 o #1 o Antiquotations.get;
val defined_command = Symtab.defined o #2 o #1 o Antiquotations.get;

val intern_option = Name_Space.intern o #1 o #2 o Antiquotations.get;
val defined_option = Symtab.defined o #2 o #2 o Antiquotations.get;

fun command src state ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ((xname, _), pos) = Args.dest_src src;
    val (name, f) = Name_Space.check (Context.Proof ctxt) (#1 (Antiquotations.get thy)) (xname, pos);
  in
    f src state ctxt handle ERROR msg =>
      cat_error msg ("The error(s) above occurred in document antiquotation: " ^
        quote name ^ Position.str_of pos)
  end;

fun option ((xname, pos), s) ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (_, opt) = Name_Space.check (Context.Proof ctxt) (#2 (Antiquotations.get thy)) (xname, pos);
  in opt s ctxt end;

fun print_antiquotations ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (commands, options) = Antiquotations.get thy;
    val command_names = map #1 (Name_Space.extern_table ctxt commands);
    val option_names = map #1 (Name_Space.extern_table ctxt options);
  in
    [Pretty.big_list "document antiquotations:" (map Pretty.str command_names),
      Pretty.big_list "document antiquotation options:" (map Pretty.str option_names)]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun antiquotation name scan out =
  add_command name
    (fn src => fn state => fn ctxt =>
      let val (x, ctxt') = Args.context_syntax "document antiquotation" scan src ctxt
      in out {source = src, state = state, context = ctxt'} x end);



(** syntax of antiquotations **)

(* option values *)

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


(* outer syntax *)

local

val property =
  Parse.position Parse.xname -- Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.xname) "";

val properties =
  Scan.optional (Parse.$$$ "[" |-- Parse.!!! (Parse.enum "," property --| Parse.$$$ "]")) [];

in

val antiq =
  Parse.!!!
    (Parse.position Parse.liberal_name -- properties -- Args.parse --| Scan.ahead Parse.eof)
  >> (fn (((x, pos), y), z) => (y, Args.src ((x, z), pos)));

end;


(* eval_antiquote *)

val modes = Unsynchronized.ref ([]: string list);

fun eval_antiq lex state (ss, (pos, _)) =
  let
    val (opts, src) = Token.read_antiq lex antiq (ss, pos);
    fun cmd ctxt = wrap ctxt (fn () => command src state ctxt) ();
    val preview_ctxt = fold option opts (Toplevel.presentation_context_of state);
    val print_ctxt = Context_Position.set_visible false preview_ctxt;
    val _ = cmd preview_ctxt;
  in Print_Mode.with_modes (! modes @ Latex.modes) (fn () => cmd print_ctxt) () end;

fun eval_antiquote lex state (txt, pos) =
  let
    fun expand (Antiquote.Text ss) = Symbol_Pos.content ss
      | expand (Antiquote.Antiq antiq) = eval_antiq lex state antiq
      | expand (Antiquote.Open _) = ""
      | expand (Antiquote.Close _) = "";
    val ants = Antiquote.read (Symbol_Pos.explode (txt, pos), pos);
  in
    if Toplevel.is_toplevel state andalso not (forall Antiquote.is_text ants) then
      error ("Unknown context -- cannot expand document antiquotations" ^ Position.str_of pos)
    else implode (map expand ants)
  end;



(** present theory source **)

(*NB: arranging white space around command spans is a black art.*)

(* presentation tokens *)

datatype token =
    NoToken
  | BasicToken of Token.T
  | MarkupToken of string * (string * Position.T)
  | MarkupEnvToken of string * (string * Position.T)
  | VerbatimToken of string * Position.T;

fun output_token lex state =
  let val eval = eval_antiquote lex state in
    fn NoToken => ""
     | BasicToken tok => Latex.output_basic tok
     | MarkupToken (cmd, txt) => Latex.output_markup cmd (eval txt)
     | MarkupEnvToken (cmd, txt) => Latex.output_markup_env cmd (eval txt)
     | VerbatimToken txt => Latex.output_verbatim (eval txt)
  end;

fun basic_token pred (BasicToken tok) = pred tok
  | basic_token _ _ = false;

val improper_token = basic_token (not o Token.is_proper);
val comment_token = basic_token Token.is_comment;
val blank_token = basic_token Token.is_blank;
val newline_token = basic_token Token.is_newline;


(* command spans *)

type command = string * Position.T * string list;   (*name, position, tags*)
type source = (token * (string * int)) list;        (*token, markup flag, meta-comment depth*)

datatype span = Span of command * (source * source * source * source) * bool;

fun make_span cmd src =
  let
    fun take_newline (tok :: toks) =
          if newline_token (fst tok) then ([tok], toks, true)
          else ([], tok :: toks, false)
      | take_newline [] = ([], [], false);
    val (((src_prefix, src_main), src_suffix1), (src_suffix2, src_appendix, newline)) =
      src
      |> take_prefix (improper_token o fst)
      ||>> take_suffix (improper_token o fst)
      ||>> take_prefix (comment_token o fst)
      ||> take_newline;
  in Span (cmd, (src_prefix, src_main, src_suffix1 @ src_suffix2, src_appendix), newline) end;


(* present spans *)

local

fun err_bad_nesting pos =
  error ("Bad nesting of commands in presentation" ^ pos);

fun edge which f (x: string option, y) =
  if x = y then I
  else (case which (x, y) of NONE => I | SOME txt => Buffer.add (f txt));

val begin_tag = edge #2 Latex.begin_tag;
val end_tag = edge #1 Latex.end_tag;
fun open_delim delim e = edge #2 Latex.begin_delim e #> delim #> edge #2 Latex.end_delim e;
fun close_delim delim e = edge #1 Latex.begin_delim e #> delim #> edge #1 Latex.end_delim e;

in

fun present_span lex default_tags span state state'
    (tag_stack, active_tag, newline, buffer, present_cont) =
  let
    val present = fold (fn (tok, (flag, 0)) =>
        Buffer.add (output_token lex state' tok)
        #> Buffer.add flag
      | _ => I);

    val Span ((cmd_name, cmd_pos, cmd_tags), srcs, span_newline) = span;

    val (tag, tags) = tag_stack;
    val tag' = try hd (fold (update (op =)) cmd_tags (the_list tag));

    val active_tag' =
      if is_some tag' then tag'
      else if cmd_name = "end" andalso not (Toplevel.is_toplevel state') then NONE
      else try hd (default_tags cmd_name);
    val edge = (active_tag, active_tag');

    val newline' =
      if is_none active_tag' then span_newline else newline;

    val nesting = Toplevel.level state' - Toplevel.level state;
    val tag_stack' =
      if nesting = 0 andalso not (Toplevel.is_proof state) then tag_stack
      else if nesting >= 0 then (tag', replicate nesting tag @ tags)
      else
        (case drop (~ nesting - 1) tags of
          tgs :: tgss => (tgs, tgss)
        | [] => err_bad_nesting (Position.str_of cmd_pos));

    val buffer' =
      buffer
      |> end_tag edge
      |> close_delim (fst present_cont) edge
      |> snd present_cont
      |> open_delim (present (#1 srcs)) edge
      |> begin_tag edge
      |> present (#2 srcs);
    val present_cont' =
      if newline then (present (#3 srcs), present (#4 srcs))
      else (I, present (#3 srcs) #> present (#4 srcs));
  in (tag_stack', active_tag', newline', buffer', present_cont') end;

fun present_trailer ((_, tags), active_tag, _, buffer, present_cont) =
  if not (null tags) then err_bad_nesting " at end of theory"
  else
    buffer
    |> end_tag (active_tag, NONE)
    |> close_delim (fst present_cont) (active_tag, NONE)
    |> snd present_cont;

end;


(* present_thy *)

datatype markup = Markup | MarkupEnv | Verbatim;

local

val space_proper =
  Scan.one Token.is_blank -- Scan.many Token.is_comment -- Scan.one Token.is_proper;

val is_improper = not o (Token.is_proper orf Token.is_begin_ignore orf Token.is_end_ignore);
val improper = Scan.many is_improper;
val improper_end = Scan.repeat (Scan.unless space_proper (Scan.one is_improper));
val blank_end = Scan.repeat (Scan.unless space_proper (Scan.one Token.is_blank));

val opt_newline = Scan.option (Scan.one Token.is_newline);

val ignore =
  Scan.depend (fn d => opt_newline |-- Scan.one Token.is_begin_ignore
    >> pair (d + 1)) ||
  Scan.depend (fn d => Scan.one Token.is_end_ignore --|
    (if d = 0 then Scan.fail_with (K (fn () => "Bad nesting of meta-comments")) else opt_newline)
    >> pair (d - 1));

val tag = (improper -- Parse.$$$ "%" -- improper) |-- Parse.!!! (Parse.tag_name --| blank_end);

val locale =
  Scan.option ((Parse.$$$ "(" -- improper -- Parse.$$$ "in") |--
    Parse.!!! (improper |-- Parse.xname --| (improper -- Parse.$$$ ")")));

in

fun present_thy lex default_tags is_markup command_results toks =
  let
    (* tokens *)

    val ignored = Scan.state --| ignore
      >> (fn d => (NONE, (NoToken, ("", d))));

    fun markup mark mk flag = Scan.peek (fn d =>
      improper |--
        Parse.position (Scan.one (Token.is_command andf is_markup mark o Token.content_of)) --
      Scan.repeat tag --
      Parse.!!!! ((improper -- locale -- improper) |-- Parse.doc_source --| improper_end)
      >> (fn (((tok, pos), tags), txt) =>
        let val name = Token.content_of tok
        in (SOME (name, pos, tags), (mk (name, txt), (flag, d))) end));

    val command = Scan.peek (fn d =>
      Parse.position (Scan.one (Token.is_command)) --
      Scan.repeat tag
      >> (fn ((tok, pos), tags) =>
        let val name = Token.content_of tok
        in (SOME (name, pos, tags), (BasicToken tok, (Latex.markup_false, d))) end));

    val cmt = Scan.peek (fn d =>
      Parse.$$$ "--" |-- Parse.!!!! (improper |-- Parse.doc_source)
      >> (fn txt => (NONE, (MarkupToken ("cmt", txt), ("", d)))));

    val other = Scan.peek (fn d =>
       Parse.not_eof >> (fn tok => (NONE, (BasicToken tok, ("", d)))));

    val token =
      ignored ||
      markup Markup MarkupToken Latex.markup_true ||
      markup MarkupEnv MarkupEnvToken Latex.markup_true ||
      markup Verbatim (VerbatimToken o #2) "" ||
      command || cmt || other;


    (* spans *)

    val is_eof = fn (_, (BasicToken x, _)) => Token.is_eof x | _ => false;
    val stopper = Scan.stopper (K (NONE, (BasicToken Token.eof, ("", 0)))) is_eof;

    val cmd = Scan.one (is_some o fst);
    val non_cmd = Scan.one (is_none o fst andf not o is_eof) >> #2;

    val comments = Scan.many (comment_token o fst o snd);
    val blank = Scan.one (blank_token o fst o snd);
    val newline = Scan.one (newline_token o fst o snd);
    val before_cmd =
      Scan.option (newline -- comments) --
      Scan.option (newline -- comments) --
      Scan.option (blank -- comments) -- cmd;

    val span =
      Scan.repeat non_cmd -- cmd --
        Scan.repeat (Scan.unless before_cmd non_cmd) --
        Scan.option (newline >> (single o snd))
      >> (fn (((toks1, (cmd, tok2)), toks3), tok4) =>
          make_span (the cmd) (toks1 @ (tok2 :: (toks3 @ the_default [] tok4))));

    val spans =
      Source.of_list (filter_out Token.is_semicolon toks)
      |> Source.source' 0 Token.stopper (Scan.error (Scan.bulk token)) NONE
      |> Source.source stopper (Scan.error (Scan.bulk span)) NONE
      |> Source.exhaust;


    (* present commands *)

    fun present_command tr span st st' =
      Toplevel.setmp_thread_position tr (present_span lex default_tags span st st');

    fun present _ [] = I
      | present st (((tr, st'), span) :: rest) = present_command tr span st st' #> present st' rest;
  in
    if length command_results = length spans then
      ((NONE, []), NONE, true, Buffer.empty, (I, I))
      |> present Toplevel.toplevel (command_results ~~ spans)
      |> present_trailer
    else error "Messed-up outer syntax for presentation"
  end;

end;



(** setup default output **)

(* options *)

val _ =
  Context.>> (Context.map_theory
   (add_option (Binding.name "show_types") (Config.put show_types o boolean) #>
    add_option (Binding.name "show_sorts") (Config.put show_sorts o boolean) #>
    add_option (Binding.name "show_structs") (Config.put show_structs o boolean) #>
    add_option (Binding.name "show_question_marks") (Config.put show_question_marks o boolean) #>
    add_option (Binding.name "show_abbrevs") (Config.put show_abbrevs o boolean) #>
    add_option (Binding.name "names_long") (Config.put Name_Space.names_long o boolean) #>
    add_option (Binding.name "names_short") (Config.put Name_Space.names_short o boolean) #>
    add_option (Binding.name "names_unique") (Config.put Name_Space.names_unique o boolean) #>
    add_option (Binding.name "eta_contract") (Config.put Syntax_Trans.eta_contract o boolean) #>
    add_option (Binding.name "display") (Config.put display o boolean) #>
    add_option (Binding.name "break") (Config.put break o boolean) #>
    add_option (Binding.name "quotes") (Config.put quotes o boolean) #>
    add_option (Binding.name "mode") (add_wrapper o Print_Mode.with_modes o single) #>
    add_option (Binding.name "margin") (add_wrapper o setmp_CRITICAL Pretty.margin_default o integer) #>
    add_option (Binding.name "indent") (Config.put indent o integer) #>
    add_option (Binding.name "source") (Config.put source o boolean) #>
    add_option (Binding.name "goals_limit") (Config.put Goal_Display.goals_limit o integer)));


(* basic pretty printing *)

fun tweak_line ctxt s =
  if Config.get ctxt display then s else Symbol.strip_blanks s;

fun pretty_text ctxt =
  Pretty.chunks o map Pretty.str o map (tweak_line ctxt) o split_lines;

fun pretty_term ctxt t = Syntax.pretty_term (Variable.auto_fixes t ctxt) t;

fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;

fun pretty_term_style ctxt (style, t) =
  pretty_term ctxt (style t);

fun pretty_thm_style ctxt (style, th) =
  pretty_term ctxt (style (Thm.full_prop_of th));

fun pretty_term_typ ctxt (style, t) =
  let val t' = style t
  in pretty_term ctxt (Type.constraint (Term.fastype_of t') t') end;

fun pretty_term_typeof ctxt (style, t) =
  Syntax.pretty_typ ctxt (Term.fastype_of (style t));

fun pretty_const ctxt c =
  let
    val t = Const (c, Consts.type_scheme (Proof_Context.consts_of ctxt) c)
      handle TYPE (msg, _, _) => error msg;
    val ([t'], _) = Variable.import_terms true [t] ctxt;
  in pretty_term ctxt t' end;

fun pretty_abbrev ctxt s =
  let
    val t = Syntax.read_term (Proof_Context.set_mode Proof_Context.mode_abbrev ctxt) s;
    fun err () = error ("Abbreviated constant expected: " ^ Syntax.string_of_term ctxt t);
    val (head, args) = Term.strip_comb t;
    val (c, T) = Term.dest_Const head handle TERM _ => err ();
    val (U, u) = Consts.the_abbreviation (Proof_Context.consts_of ctxt) c
      handle TYPE _ => err ();
    val t' = Term.betapplys (Envir.expand_atom T (U, u), args);
    val eq = Logic.mk_equals (t, t');
    val ctxt' = Variable.auto_fixes eq ctxt;
  in Proof_Context.pretty_term_abbrev ctxt' eq end;

fun pretty_class ctxt =
  Pretty.str o Proof_Context.extern_class ctxt o Proof_Context.read_class ctxt;

fun pretty_type ctxt s =
  let val Type (name, _) = Proof_Context.read_type_name_proper ctxt false s
  in Pretty.str (Proof_Context.extern_type ctxt name) end;

fun pretty_prf full ctxt = Proof_Syntax.pretty_proof_of ctxt full;

fun pretty_theory ctxt name =
  (Theory.requires (Proof_Context.theory_of ctxt) name "presentation"; Pretty.str name);


(* default output *)

val str_of_source = space_implode " " o map Token.unparse o #2 o #1 o Args.dest_src;

fun maybe_pretty_source pretty ctxt src xs =
  map (pretty ctxt) xs  (*always pretty in order to exhibit errors!*)
  |> (if Config.get ctxt source then K [pretty_text ctxt (str_of_source src)] else I);

fun output ctxt prts =
  prts
  |> (if Config.get ctxt quotes then map Pretty.quote else I)
  |> (if Config.get ctxt display then
    map (Output.output o Pretty.string_of o Pretty.indent (Config.get ctxt indent))
    #> space_implode "\\isasep\\isanewline%\n"
    #> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
  else
    map (Output.output o (if Config.get ctxt break then Pretty.string_of else Pretty.str_of))
    #> space_implode "\\isasep\\isanewline%\n"
    #> enclose "\\isa{" "}");



(** concrete antiquotations **)

(* basic entities *)

local

fun basic_entities name scan pretty = antiquotation name scan
  (fn {source, context, ...} => output context o maybe_pretty_source pretty context source);

fun basic_entities_style name scan pretty = antiquotation name scan
  (fn {source, context, ...} => fn (style, xs) =>
    output context
      (maybe_pretty_source (fn ctxt => fn x => pretty ctxt (style, x)) context source xs));

fun basic_entity name scan = basic_entities name (scan >> single);

in

val _ =
  Context.>> (Context.map_theory
   (basic_entities_style (Binding.name "thm") (Term_Style.parse -- Attrib.thms) pretty_thm_style #>
    basic_entity (Binding.name "prop") (Term_Style.parse -- Args.prop) pretty_term_style #>
    basic_entity (Binding.name "term") (Term_Style.parse -- Args.term) pretty_term_style #>
    basic_entity (Binding.name "term_type") (Term_Style.parse -- Args.term) pretty_term_typ #>
    basic_entity (Binding.name "typeof") (Term_Style.parse -- Args.term) pretty_term_typeof #>
    basic_entity (Binding.name "const") (Args.const_proper false) pretty_const #>
    basic_entity (Binding.name "abbrev") (Scan.lift Args.name_source) pretty_abbrev #>
    basic_entity (Binding.name "typ") Args.typ_abbrev Syntax.pretty_typ #>
    basic_entity (Binding.name "class") (Scan.lift Args.name_source) pretty_class #>
    basic_entity (Binding.name "type") (Scan.lift Args.name) pretty_type #>
    basic_entity (Binding.name "text") (Scan.lift Args.name) pretty_text #>
    basic_entities (Binding.name "prf") Attrib.thms (pretty_prf false) #>
    basic_entities (Binding.name "full_prf") Attrib.thms (pretty_prf true) #>
    basic_entity (Binding.name "theory") (Scan.lift Args.name) pretty_theory #>
    basic_entities_style (Binding.name "thm_style")
      (Term_Style.parse_bare -- Attrib.thms) pretty_thm_style #>
    basic_entity (Binding.name "term_style")
      (Term_Style.parse_bare -- Args.term) pretty_term_style));

end;


(* goal state *)

local

fun proof_state state =
  (case try Toplevel.proof_of state of
    SOME prf => prf
  | _ => error "No proof state");

fun goal_state name main_goal = antiquotation name (Scan.succeed ())
  (fn {state, context = ctxt, ...} => fn () => output ctxt
    [Pretty.chunks
      (Proof.pretty_goals main_goal (Proof.map_context (K ctxt) (proof_state state)))]);

in

val _ =
  Context.>> (Context.map_theory
   (goal_state (Binding.name "goals") true #>
    goal_state (Binding.name "subgoals") false));

end;


(* embedded lemma *)

val _ = Keyword.define ("by", NONE);  (*overlap with command category*)

val _ =
  Context.>> (Context.map_theory
   (antiquotation (Binding.name "lemma")
    (Args.prop -- Scan.lift (Args.$$$ "by" |-- Method.parse -- Scan.option Method.parse))
    (fn {source, context, ...} => fn (prop, methods) =>
      let
        val prop_src =
          (case Args.dest_src source of ((a, arg :: _), pos) => Args.src ((a, [arg]), pos));
        (* FIXME check proof!? *)
        val _ = context
          |> Proof.theorem NONE (K I) [[(prop, [])]]
          |> Proof.global_terminal_proof methods;
      in output context (maybe_pretty_source pretty_term context prop_src [prop]) end)));


(* ML text *)

val verb_text =
  split_lines
  #> map (space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|")
  #> space_implode "\\isasep\\isanewline%\n";

local

fun ml_text name ml = antiquotation name (Scan.lift Args.name_source_position)
  (fn {context, ...} => fn (txt, pos) =>
   (ML_Context.eval_in (SOME context) false pos (ml pos txt);
    Symbol_Pos.content (Symbol_Pos.explode (txt, pos))
    |> (if Config.get context quotes then quote else I)
    |> (if Config.get context display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
        else verb_text)));

fun ml_enclose bg en pos txt =
  ML_Lex.read Position.none bg @ ML_Lex.read pos txt @ ML_Lex.read Position.none en;

in

val _ =
  Context.>> (Context.map_theory
   (ml_text (Binding.name "ML") (ml_enclose "fn _ => (" ");") #>
    ml_text (Binding.name "ML_op") (ml_enclose "fn _ => (op " ");") #>
    ml_text (Binding.name "ML_type") (ml_enclose "val _ = NONE : (" ") option;") #>
    ml_text (Binding.name "ML_struct")
      (ml_enclose "functor XXX() = struct structure XX = " " end;") #>

    ml_text (Binding.name "ML_functor")   (* FIXME formal treatment of functor name (!?) *)
      (fn pos => fn txt =>
        ML_Lex.read Position.none ("ML_Env.check_functor " ^
          ML_Syntax.print_string (Symbol_Pos.content (Symbol_Pos.explode (txt, pos))))) #>

    ml_text (Binding.name "ML_text") (K (K []))));

end;


(* files *)

val _ =
  Context.>> (Context.map_theory
   (antiquotation (Binding.name "file") (Scan.lift Args.name)
    (fn _ => fn path =>
      if File.exists (Path.explode path) then verb_text path
      else error ("Bad file: " ^ quote path))));

end;
