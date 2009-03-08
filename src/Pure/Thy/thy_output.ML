(*  Title:      Pure/Thy/thy_output.ML
    Author:     Markus Wenzel, TU Muenchen

Theory document output.
*)

signature THY_OUTPUT =
sig
  val display: bool ref
  val quotes: bool ref
  val indent: int ref
  val source: bool ref
  val break: bool ref
  val add_commands: (string * (Args.src -> Toplevel.state -> string)) list -> unit
  val add_options: (string * (string -> (unit -> string) -> unit -> string)) list -> unit
  val defined_command: string -> bool
  val defined_option: string -> bool
  val print_antiquotations: unit -> unit
  val boolean: string -> bool
  val integer: string -> int
  val raw_antiquotation: string -> (Args.src -> Toplevel.state ->
    Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val antiquotation: string -> (Args.src -> Proof.context ->
    Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val args: (Context.generic * Args.T list -> 'a * (Context.generic * Args.T list)) ->
    (Args.src -> Proof.context -> 'a -> string) -> Args.src -> Toplevel.state -> string
  datatype markup = Markup | MarkupEnv | Verbatim
  val modes: string list ref
  val eval_antiquote: Scan.lexicon -> Toplevel.state -> SymbolPos.text * Position.T -> string
  val present_thy: Scan.lexicon -> (string -> string list) -> (markup -> string -> bool) ->
    (Toplevel.transition * Toplevel.state) list -> (OuterLex.token, 'a) Source.source -> Buffer.T
  val str_of_source: Args.src -> string
  val pretty_text: string -> Pretty.T
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val output_list: (Proof.context -> 'a -> Pretty.T) -> Args.src ->
    Proof.context -> 'a list -> string
  val output: (Proof.context -> 'a -> Pretty.T) -> Args.src -> Proof.context -> 'a -> string
end;

structure ThyOutput: THY_OUTPUT =
struct

structure T = OuterLex;
structure P = OuterParse;


(** global options **)

val locale = ref "";
val display = ref false;
val quotes = ref false;
val indent = ref 0;
val source = ref false;
val break = ref false;



(** maintain global commands **)

local

val global_commands =
  ref (Symtab.empty: (Args.src -> Toplevel.state -> string) Symtab.table);

val global_options =
  ref (Symtab.empty: (string -> (unit -> string) -> unit -> string) Symtab.table);

fun add_item kind (name, x) tab =
 (if not (Symtab.defined tab name) then ()
  else warning ("Redefined document antiquotation " ^ kind ^ ": " ^ quote name);
  Symtab.update (name, x) tab);

in

fun add_commands xs = CRITICAL (fn () => change global_commands (fold (add_item "command") xs));
fun add_options xs = CRITICAL (fn () => change global_options (fold (add_item "option") xs));

fun defined_command name = Symtab.defined (! global_commands) name;
fun defined_option name = Symtab.defined (! global_options) name;

fun command src =
  let val ((name, _), pos) = Args.dest_src src in
    (case Symtab.lookup (! global_commands) name of
      NONE => error ("Unknown document antiquotation: " ^ quote name ^ Position.str_of pos)
    | SOME f =>
       (Position.report (Markup.doc_antiq name) pos;
        (fn state => f src state handle ERROR msg =>
          cat_error msg ("The error(s) above occurred in document antiquotation: " ^
            quote name ^ Position.str_of pos))))
  end;

fun option (name, s) f () =
  (case Symtab.lookup (! global_options) name of
    NONE => error ("Unknown document antiquotation option: " ^ quote name)
  | SOME opt => opt s f ());

fun options [] f = f
  | options (opt :: opts) f = option opt (options opts f);


fun print_antiquotations () =
 [Pretty.big_list "document antiquotation commands:"
    (map Pretty.str (sort_strings (Symtab.keys (! global_commands)))),
  Pretty.big_list "document antiquotation options:"
    (map Pretty.str (sort_strings (Symtab.keys (! global_options))))]
 |> Pretty.chunks |> Pretty.writeln;

end;



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


(* args syntax *)

fun syntax scan = Args.context_syntax "document antiquotation" scan;

fun raw_antiquotation name scan =
  add_commands [(name, fn src => fn state =>
    #1 (syntax (scan src state) src (Toplevel.presentation_context_of state NONE)))];

fun antiquotation name scan =
  raw_antiquotation name (fn src => fn state =>
    scan src (Toplevel.presentation_context_of state NONE));

fun args scan f src state : string =
  let
    val loc = if ! locale = "" then NONE else SOME (! locale);
    val (x, ctxt) = syntax scan src (Toplevel.presentation_context_of state loc);
  in f src ctxt x end;


(* outer syntax *)

local

val property = P.xname -- Scan.optional (P.$$$ "=" |-- P.!!! P.xname) "";
val properties = Scan.optional (P.$$$ "[" |-- P.!!! (P.enum "," property --| P.$$$ "]")) [];

in

val antiq = P.!!! (P.position P.xname -- properties -- Args.parse --| Scan.ahead P.eof)
  >> (fn (((x, pos), y), z) => (y, Args.src ((x, z), pos)));

end;


(* eval_antiquote *)

val modes = ref ([]: string list);

fun eval_antiquote lex state (txt, pos) =
  let
    fun expand (Antiquote.Text s) = s
      | expand (Antiquote.Antiq x) =
          let val (opts, src) = Antiquote.read_antiq lex antiq x in
            options opts (fn () => command src state) ();  (*preview errors!*)
            PrintMode.with_modes (! modes @ Latex.modes)
              (Output.no_warnings (options opts (fn () => command src state))) ()
          end
      | expand (Antiquote.Open _) = ""
      | expand (Antiquote.Close _) = "";
    val ants = Antiquote.read (SymbolPos.explode (txt, pos), pos);
  in
    if Toplevel.is_toplevel state andalso exists Antiquote.is_antiq ants then
      error ("Unknown context -- cannot expand document antiquotations" ^ Position.str_of pos)
    else implode (map expand ants)
  end;



(** present theory source **)

(*NB: arranging white space around command spans is a black art.*)

(* presentation tokens *)

datatype token =
    NoToken
  | BasicToken of T.token
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

val improper_token = basic_token (not o T.is_proper);
val comment_token = basic_token T.is_comment;
val blank_token = basic_token T.is_blank;
val newline_token = basic_token T.is_newline;


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
    val tag' = try hd (fold OuterKeyword.update_tags cmd_tags (the_list tag));

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
        (case Library.drop (~ nesting - 1, tags) of
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
  Scan.one T.is_blank -- Scan.many T.is_comment -- Scan.one T.is_proper;

val is_improper = not o (T.is_proper orf T.is_begin_ignore orf T.is_end_ignore);
val improper = Scan.many is_improper;
val improper_end = Scan.repeat (Scan.unless space_proper (Scan.one is_improper));
val blank_end = Scan.repeat (Scan.unless space_proper (Scan.one T.is_blank));

val opt_newline = Scan.option (Scan.one T.is_newline);

val ignore =
  Scan.depend (fn d => opt_newline |-- Scan.one T.is_begin_ignore
    >> pair (d + 1)) ||
  Scan.depend (fn d => Scan.one T.is_end_ignore --|
    (if d = 0 then Scan.fail_with (K "Bad nesting of meta-comments") else opt_newline)
    >> pair (d - 1));

val tag = (improper -- P.$$$ "%" -- improper) |-- P.!!! (P.tag_name --| blank_end);

val locale =
  Scan.option ((P.$$$ "(" -- improper -- P.$$$ "in") |--
    P.!!! (improper |-- P.xname --| (improper -- P.$$$ ")")));

in

fun present_thy lex default_tags is_markup command_results src =
  let
    (* tokens *)

    val ignored = Scan.state --| ignore
      >> (fn d => (NONE, (NoToken, ("", d))));

    fun markup mark mk flag = Scan.peek (fn d =>
      improper |-- P.position (Scan.one (T.is_kind T.Command andf is_markup mark o T.content_of)) --
      Scan.repeat tag --
      P.!!!! ((improper -- locale -- improper) |-- P.doc_source --| improper_end)
      >> (fn (((tok, pos), tags), txt) =>
        let val name = T.content_of tok
        in (SOME (name, pos, tags), (mk (name, txt), (flag, d))) end));

    val command = Scan.peek (fn d =>
      P.position (Scan.one (T.is_kind T.Command)) --
      Scan.repeat tag
      >> (fn ((tok, pos), tags) =>
        let val name = T.content_of tok
        in (SOME (name, pos, tags), (BasicToken tok, (Latex.markup_false, d))) end));

    val cmt = Scan.peek (fn d =>
      P.$$$ "--" |-- P.!!!! (improper |-- P.doc_source)
      >> (fn txt => (NONE, (MarkupToken ("cmt", txt), ("", d)))));

    val other = Scan.peek (fn d =>
       P.not_eof >> (fn tok => (NONE, (BasicToken tok, ("", d)))));

    val token =
      ignored ||
      markup Markup MarkupToken Latex.markup_true ||
      markup MarkupEnv MarkupEnvToken Latex.markup_true ||
      markup Verbatim (VerbatimToken o #2) "" ||
      command || cmt || other;


    (* spans *)

    val is_eof = fn (_, (BasicToken x, _)) => T.is_eof x | _ => false;
    val stopper = Scan.stopper (K (NONE, (BasicToken T.eof, ("", 0)))) is_eof;

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
      src
      |> Source.filter (not o T.is_semicolon)
      |> Source.source' 0 T.stopper (Scan.error (Scan.bulk token)) NONE
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

val _ = add_options
 [("show_types", Library.setmp Syntax.show_types o boolean),
  ("show_sorts", Library.setmp Syntax.show_sorts o boolean),
  ("show_structs", Library.setmp show_structs o boolean),
  ("show_question_marks", Library.setmp show_question_marks o boolean),
  ("long_names", Library.setmp NameSpace.long_names o boolean),
  ("short_names", Library.setmp NameSpace.short_names o boolean),
  ("unique_names", Library.setmp NameSpace.unique_names o boolean),
  ("eta_contract", Library.setmp Syntax.eta_contract o boolean),
  ("locale", Library.setmp locale),
  ("display", Library.setmp display o boolean),
  ("break", Library.setmp break o boolean),
  ("quotes", Library.setmp quotes o boolean),
  ("mode", fn s => fn f => PrintMode.with_modes [s] f),
  ("margin", Pretty.setmp_margin o integer),
  ("indent", Library.setmp indent o integer),
  ("source", Library.setmp source o boolean),
  ("goals_limit", Library.setmp goals_limit o integer)];


(* basic pretty printing *)

val str_of_source = space_implode " " o map T.unparse o #2 o #1 o Args.dest_src;

fun tweak_line s =
  if ! display then s else Symbol.strip_blanks s;

val pretty_text = Pretty.chunks o map Pretty.str o map tweak_line o Library.split_lines;

fun pretty_term ctxt t = Syntax.pretty_term (Variable.auto_fixes t ctxt) t;

fun pretty_term_abbrev ctxt t = ProofContext.pretty_term_abbrev (Variable.auto_fixes t ctxt) t;

fun pretty_term_typ ctxt t =
  Syntax.pretty_term ctxt (TypeInfer.constrain (Term.fastype_of t) t);

fun pretty_term_typeof ctxt = Syntax.pretty_typ ctxt o Term.fastype_of;

fun pretty_const ctxt c =
  let
    val t = Const (c, Consts.type_scheme (ProofContext.consts_of ctxt) c)
      handle TYPE (msg, _, _) => error msg;
    val ([t'], _) = Variable.import_terms true [t] ctxt;
  in pretty_term ctxt t' end;

fun pretty_abbrev ctxt s =
  let
    val t = Syntax.parse_term ctxt s |> singleton (ProofContext.standard_infer_types ctxt);
    fun err () = error ("Abbreviated constant expected: " ^ Syntax.string_of_term ctxt t);
    val (head, args) = Term.strip_comb t;
    val (c, T) = Term.dest_Const head handle TERM _ => err ();
    val (U, u) = Consts.the_abbreviation (ProofContext.consts_of ctxt) c
      handle TYPE _ => err ();
    val t' = Term.betapplys (Envir.expand_atom T (U, u), args);
  in pretty_term_abbrev ctxt (Logic.mk_equals (t, t')) end;

fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;

fun pretty_term_style ctxt (name, t) =
  pretty_term ctxt (TermStyle.the_style (ProofContext.theory_of ctxt) name ctxt t);

fun pretty_thm_style ctxt (name, th) =
  pretty_term_style ctxt (name, Thm.full_prop_of th);

fun pretty_prf full ctxt thms =
  Pretty.chunks (map (ProofSyntax.pretty_proof_of ctxt full) thms);

fun pretty_theory ctxt name =
  (Theory.requires (ProofContext.theory_of ctxt) name "presentation"; Pretty.str name);


(* Isar output *)

fun output_list pretty src ctxt xs =
  map (pretty ctxt) xs        (*always pretty in order to exhibit errors!*)
  |> (if ! source then K [pretty_text (str_of_source src)] else I)
  |> (if ! quotes then map Pretty.quote else I)
  |> (if ! display then
    map (Output.output o Pretty.string_of o Pretty.indent (! indent))
    #> space_implode "\\isasep\\isanewline%\n"
    #> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
  else
    map (Output.output o (if ! break then Pretty.string_of else Pretty.str_of))
    #> space_implode "\\isasep\\isanewline%\n"
    #> enclose "\\isa{" "}");

fun output pretty src ctxt = output_list pretty src ctxt o single;

fun proof_state state =
  (case try Toplevel.proof_of state of
    SOME prf => prf
  | _ => error "No proof state");

fun output_goals main_goal src state = args (Scan.succeed ()) (output (fn _ => fn _ =>
  Pretty.chunks (Proof.pretty_goals main_goal (proof_state state)))) src state;

fun ml_val txt = "fn _ => (" ^ txt ^ ");";
fun ml_type txt = "val _ = NONE : (" ^ txt ^ ") option;";
fun ml_struct txt = "functor DUMMY_FUNCTOR() = struct structure DUMMY = " ^ txt ^ " end;"

fun output_ml ml _ ctxt (txt, pos) =
 (ML_Context.eval_in (SOME ctxt) false pos (ml txt);
  SymbolPos.content (SymbolPos.explode (txt, pos))
  |> (if ! quotes then quote else I)
  |> (if ! display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
  else
    split_lines
    #> map (space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|")
    #> space_implode "\\isasep\\isanewline%\n"));


(* embedded lemmas *)

fun pretty_lemma ctxt (prop, methods) =
  let
    val _ = ctxt
      |> Proof.theorem_i NONE (K I) [[(prop, [])]]
      |> Proof.global_terminal_proof methods;
  in pretty_term ctxt prop end;

val embedded_lemma =
  args (Args.prop -- Scan.lift (Args.$$$ "by" |-- Method.parse -- Scan.option Method.parse))
    (output pretty_lemma o (fn ((a, arg :: _), p) => (Args.src ((a, [arg]), p))) o Args.dest_src);


(* commands *)

val _ = OuterKeyword.keyword "by";

val _ = add_commands
 [("thm", args Attrib.thms (output_list pretty_thm)),
  ("thm_style", args (Scan.lift Args.liberal_name -- Attrib.thm) (output pretty_thm_style)),
  ("prop", args Args.prop (output pretty_term)),
  ("lemma", embedded_lemma),
  ("term", args Args.term (output pretty_term)),
  ("term_style", args (Scan.lift Args.liberal_name -- Args.term) (output pretty_term_style)),
  ("term_type", args Args.term (output pretty_term_typ)),
  ("typeof", args Args.term (output pretty_term_typeof)),
  ("const", args Args.const_proper (output pretty_const)),
  ("abbrev", args (Scan.lift Args.name_source) (output pretty_abbrev)),
  ("typ", args Args.typ_abbrev (output Syntax.pretty_typ)),
  ("text", args (Scan.lift Args.name) (output (K pretty_text))),
  ("goals", output_goals true),
  ("subgoals", output_goals false),
  ("prf", args Attrib.thms (output (pretty_prf false))),
  ("full_prf", args Attrib.thms (output (pretty_prf true))),
  ("theory", args (Scan.lift Args.name) (output pretty_theory)),
  ("ML", args (Scan.lift Args.name_source_position) (output_ml ml_val)),
  ("ML_type", args (Scan.lift Args.name_source_position) (output_ml ml_type)),
  ("ML_struct", args (Scan.lift Args.name_source_position) (output_ml ml_struct))];

end;
