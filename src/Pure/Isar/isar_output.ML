(*  Title:      Pure/Isar/isar_output.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar theory output.
*)

signature ISAR_OUTPUT =
sig
  val display: bool ref
  val quotes: bool ref
  val indent: int ref
  val source: bool ref
  val add_commands: (string * (Args.src -> Toplevel.state -> string)) list -> unit
  val add_options: (string * (string -> (unit -> string) -> unit -> string)) list -> unit
  val print_antiquotations: unit -> unit
  val boolean: string -> bool
  val integer: string -> int
  val args: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    (Args.src -> Proof.context -> 'a -> string) -> Args.src -> Toplevel.state -> string
  datatype markup = Markup | MarkupEnv | Verbatim
  val modes: string list ref
  val eval_antiquote: Scan.lexicon -> Toplevel.state -> string * Position.T -> string
  val present_thy: Scan.lexicon -> (string -> string list) -> (markup -> string -> bool) ->
    Toplevel.transition list -> (OuterLex.token, 'a) Source.source -> Buffer.T
  val output_list: (Proof.context -> 'a -> Pretty.T) -> Args.src ->
    Proof.context -> 'a list -> string
  val output: (Proof.context -> 'a -> Pretty.T) -> Args.src -> Proof.context -> 'a -> string
end;

structure IsarOutput: ISAR_OUTPUT =
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
  else warning ("Redefined antiquotation " ^ kind ^ ": " ^ quote name);
  Symtab.update ((name, x), tab));

in

val add_commands = Library.change global_commands o fold (add_item "command");
val add_options = Library.change global_options o fold (add_item "option");

fun command src =
  let val ((name, _), pos) = Args.dest_src src in
    (case Symtab.lookup (! global_commands, name) of
      NONE => error ("Unknown antiquotation command: " ^ quote name ^ Position.str_of pos)
    | SOME f => transform_failure (curry Antiquote.ANTIQUOTE_FAIL (name, pos)) (f src))
  end;

fun option (name, s) f () =
  (case Symtab.lookup (! global_options, name) of
    NONE => error ("Unknown antiquotation option: " ^ quote name)
  | SOME opt => opt s f ());

fun options [] f = f
  | options (opt :: opts) f = option opt (options opts f);


fun print_antiquotations () =
 [Pretty.big_list "antiquotation commands:" (map Pretty.str (Symtab.keys (! global_commands))),
  Pretty.big_list "antiquotation options:" (map Pretty.str (Symtab.keys (! global_options)))]
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

fun syntax (scan: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list))) =
  Args.syntax "antiquotation" scan;

fun args scan f src state : string =
  let
    val ctxt0 =
      if ! locale = "" then Toplevel.body_context_of state
      else #3 (Locale.read_context_statement (SOME (! locale)) [] []
        (ProofContext.init (Toplevel.theory_of state)));
    val (ctxt, x) = syntax scan src ctxt0;
  in f src ctxt x end;


(* outer syntax *)

local

val property = P.xname -- Scan.optional (P.$$$ "=" |-- P.!!! P.xname) "";
val properties = Scan.optional (P.$$$ "[" |-- P.!!! (P.enum "," property --| P.$$$ "]")) [];

val antiq = P.position P.xname -- properties -- P.arguments --| Scan.ahead P.eof
  >> (fn (((x, pos), y), z) => (y, Args.src ((x, z), pos)));

fun antiq_args_aux keyword_lexicon (str, pos) =
  Source.of_string str
  |> Symbol.source false
  |> T.source false (K (keyword_lexicon, Scan.empty_lexicon)) pos
  |> T.source_proper
  |> Source.source T.stopper (Scan.error (Scan.bulk (P.!!! antiq))) NONE
  |> Source.exhaust;

in

fun antiq_args lex (s, pos) =
  (case antiq_args_aux lex (s, pos) of [x] => x | _ => raise ERROR) handle ERROR =>
    error ("Malformed antiquotation: " ^ quote ("@{" ^ s ^ "}") ^ Position.str_of pos);

end;


(* eval_antiquote *)

val modes = ref ([]: string list);

fun eval_antiquote lex state (str, pos) =
  let
    fun expand (Antiquote.Text s) = s
      | expand (Antiquote.Antiq x) =
          let val (opts, src) = antiq_args lex x in
            options opts (fn () => command src state) ();  (*preview errors!*)
            Library.setmp print_mode (! modes @ Latex.modes @ ! print_mode)
              (Output.no_warnings (options opts (fn () => command src state))) ()
          end;
    val ants = Antiquote.antiquotes_of (str, pos);
  in
    if Toplevel.is_toplevel state andalso exists Antiquote.is_antiq ants then
      error ("Cannot expand antiquotations at top-level" ^ Position.str_of pos)
    else implode (map expand ants)
  end;



(** present theory source **)

(* presentation tokens *)

datatype token =
    NoToken
  | BasicToken of T.token
  | MarkupToken of string * (string * Position.T)
  | MarkupEnvToken of string * (string * Position.T)
  | VerbatimToken of string * Position.T;

fun output_token lex state =
  let
    val eval = eval_antiquote lex state
  in
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
type tok = string * token * int;                    (*raw text, token, meta-comment depth*)
type source = tok list;          

datatype span = Span of command * (source * source * source * source) * bool;

fun make_span cmd src =
  let
    fun take_newline ((tok: tok) :: toks) =
          if newline_token (#2 tok) then ([tok], toks, true)
          else ([], tok :: toks, false)
      | take_newline [] = ([], [], false);
    val (((src_prefix, src_main), src_suffix1), (src_suffix2, src_appendix, newline)) =
      src
      |> take_prefix (improper_token o #2)
      ||>> take_suffix (improper_token o #2)
      ||>> take_prefix (comment_token o #2)
      ||> take_newline;      
  in Span (cmd, (src_prefix, src_main, src_suffix1 @ src_suffix2, src_appendix), newline) end;


(* present spans *)

local

fun err_bad_nesting pos =
  error ("Bad nesting of commands in presentation" ^ pos);

fun edge1 f (x, y) = if_none (Option.map (Buffer.add o f) (if x = y then NONE else x)) I;
fun edge2 f (x, y) = if_none (Option.map (Buffer.add o f) (if x = y then NONE else y)) I;

val begin_tag = edge2 Latex.begin_tag;
val end_tag = edge1 Latex.end_tag;
fun open_delim delim e = edge2 Latex.begin_delim e #> delim #> edge2 Latex.end_delim e;
fun close_delim delim e = edge1 Latex.begin_delim e #> delim #> edge1 Latex.end_delim e;

in

fun present_span lex default_tags span state state'
    (tag_stack, active_tag, newline, buffer, present_cont) =
  let
    val present = fold (fn (raw, tok, d) =>
      if d > 0 then I
      else Buffer.add raw #> Buffer.add (output_token lex state' tok));

    val Span ((cmd_name, cmd_pos, cmd_tags), srcs, span_newline) = span;

    val (tag, tags) = tag_stack;
    val tag' =
      (case tag of NONE => [] | SOME tg => [tg])
      |> fold OuterKeyword.update_tags cmd_tags
      |> try hd;

    val active_tag' =
      if is_some tag' then tag'
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
  Scan.one T.is_blank -- Scan.any T.is_comment -- Scan.one T.is_proper;

val is_improper = not o (T.is_proper orf T.is_begin_ignore orf T.is_end_ignore);
val improper = Scan.any is_improper;
val improper_end = Scan.repeat (Scan.unless space_proper (Scan.one is_improper));

val opt_newline = Scan.option (Scan.one T.is_newline);

val ignore =
  Scan.depend (fn d => opt_newline |-- Scan.one T.is_begin_ignore
    >> pair (d + 1)) ||
  Scan.depend (fn d => Scan.one T.is_end_ignore --|
    (if d = 0 then Scan.fail_with (K "Bad nesting of meta-comments") else opt_newline)
    >> pair (d - 1));

val tag = (improper -- P.$$$ "%" -- improper) |-- P.!!! (P.tag_name --| improper_end);

in

fun present_thy lex default_tags is_markup trs src =
  let
    (* tokens *)

    val ignored = Scan.state --| ignore
      >> (fn d => (NONE, ("", NoToken, d)));

    fun markup flag mark mk = Scan.peek (fn d =>
      improper |--
      P.position (Scan.one (T.is_kind T.Command andf is_markup mark o T.val_of)) --
      Scan.repeat tag --
      P.!!!! (improper |-- P.position P.text --| improper_end)
      >> (fn (((tok, pos), tags), txt) =>
        let val name = T.val_of tok
        in (SOME (name, pos, tags), (flag, mk (name, txt), d)) end));

    val command = Scan.peek (fn d =>
      P.position (Scan.one (T.is_kind T.Command)) --
      Scan.repeat tag
      >> (fn ((tok, pos), tags) =>
        let val name = T.val_of tok
        in (SOME (name, pos, tags), (Latex.markup_false, BasicToken tok, d)) end));

    val cmt = Scan.peek (fn d =>
      P.$$$ "--" |-- P.!!!! (improper |-- P.position P.text)
      >> (fn txt => (NONE, ("", MarkupToken ("cmt", txt), d))));

    val other = Scan.peek (fn d =>
       Scan.one T.not_eof >> (fn tok => (NONE, ("", BasicToken tok, d))));

    val token =
      ignored ||
      markup Latex.markup_true Markup MarkupToken ||
      markup Latex.markup_true MarkupEnv MarkupEnvToken ||
      markup "" Verbatim (VerbatimToken o #2) ||
      command || cmt || other;


    (* spans *)

    val stopper =
      ((NONE, ("", BasicToken (#1 T.stopper), 0)),
        fn (_, (_, BasicToken x, _)) => #2 T.stopper x | _ => false);

    val cmd = Scan.one (is_some o #1);
    val non_cmd = Scan.one (is_none o #1 andf not o #2 stopper) >> #2;

    val comments = Scan.any (comment_token o #2 o #2);
    val blank = Scan.one (blank_token o #2 o #2);
    val newline = Scan.one (newline_token o #2 o #2); 
    val before_cmd =
      Scan.option (newline -- comments) --
      Scan.option (newline -- comments) --
      Scan.option (blank -- comments) -- cmd;

    val span =
      Scan.repeat non_cmd -- cmd --
        Scan.repeat (Scan.unless before_cmd non_cmd) --
        Scan.option (newline >> (single o #2))
      >> (fn (((toks1, (cmd, tok2)), toks3), tok4) =>
          make_span (the cmd) (toks1 @ tok2 :: toks3 @ if_none tok4 []));

    val spans =
      src
      |> Source.filter (not o T.is_semicolon)
      |> Source.source' 0 T.stopper (Scan.error (Scan.bulk token)) NONE
      |> Source.source stopper (Scan.error (Scan.bulk span)) NONE
      |> Source.exhaust;
  in
    if length trs = length spans then
      ((NONE, []), NONE, true, Buffer.empty, (I, I))
      |> Toplevel.present_excursion (trs ~~ map (present_span lex default_tags) spans)
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
  ("mode", fn s => fn f => fn () => Library.setmp print_mode (s :: ! print_mode) f ()),
  ("margin", Pretty.setmp_margin o integer),
  ("indent", Library.setmp indent o integer),
  ("source", Library.setmp source o boolean),
  ("goals_limit", Library.setmp goals_limit o integer)];


(* basic pretty printing *)

val str_of_source = space_implode " " o map Args.string_of o #2 o #1 o Args.dest_src;

fun tweak_line s =
  if ! display then s else Symbol.strip_blanks s;

val pretty_text = Pretty.chunks o map Pretty.str o map tweak_line o Library.split_lines;

fun pretty_term ctxt = ProofContext.pretty_term ctxt o ProofContext.extern_skolem ctxt;

fun pretty_term_typ ctxt t =
  (Syntax.const Syntax.constrainC $
    ProofContext.extern_skolem ctxt t $
    Syntax.term_of_typ (! show_sorts) (Term.fastype_of t))
  |> ProofContext.pretty_term ctxt;

fun pretty_term_typeof ctxt = ProofContext.pretty_typ ctxt o Term.fastype_of;

fun pretty_term_const ctxt t =
  if Term.is_Const t then pretty_term ctxt t
  else error ("Logical constant expected: " ^ ProofContext.string_of_term ctxt t);

fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;

fun pretty_term_style ctxt (name, t) =
  pretty_term ctxt (TermStyle.the_style (ProofContext.theory_of ctxt) name ctxt t);

fun pretty_thm_style ctxt (name, th) =
  pretty_term_style ctxt (name, Thm.full_prop_of th);

fun pretty_prf full ctxt thms =
  Pretty.chunks (map (ProofContext.pretty_proof_of ctxt full) thms);


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

fun output_goals main_goal src state = args (Scan.succeed ()) (output (fn _ => fn _ =>
  Pretty.chunks (Proof.pretty_goals main_goal (Toplevel.proof_of state
      handle Toplevel.UNDEF => error "No proof state")))) src state;

fun output_ml src ctxt txt =
 (Context.use_mltext ("fn _ => (" ^ txt ^ ")") false (SOME (ProofContext.theory_of ctxt));
  (if ! source then str_of_source src else txt)
  |> (if ! quotes then quote else I)
  |> (if ! display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
  else
    split_lines
    #> map (space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|")
    #> space_implode "\\isasep\\isanewline%\n"));


(* commands *)

val _ = add_commands
 [("thm", args Attrib.local_thmss (output_list pretty_thm)),
  ("thm_style", args (Scan.lift Args.liberal_name -- Attrib.local_thm) (output pretty_thm_style)),
  ("prop", args Args.local_prop (output pretty_term)),
  ("term", args Args.local_term (output pretty_term)),
  ("term_style", args (Scan.lift Args.liberal_name -- Args.local_term) (output pretty_term_style)),
  ("term_type", args Args.local_term (output pretty_term_typ)),
  ("typeof", args Args.local_term (output pretty_term_typeof)),
  ("const", args Args.local_term (output pretty_term_const)),
  ("typ", args Args.local_typ_abbrev (output ProofContext.pretty_typ)),
  ("text", args (Scan.lift Args.name) (output (K pretty_text))),
  ("goals", output_goals true),
  ("subgoals", output_goals false),
  ("prf", args Attrib.local_thmss (output (pretty_prf false))),
  ("full_prf", args Attrib.local_thmss (output (pretty_prf true))),
  ("ML", args (Scan.lift Args.name) output_ml)];

end;
