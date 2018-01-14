(*  Title:      Pure/Thy/thy_output.ML
    Author:     Makarius

Theory document output.
*)

signature THY_OUTPUT =
sig
  val output_text: Proof.context -> {markdown: bool} -> Input.source -> Latex.text list
  val check_comments: Proof.context -> Symbol_Pos.T list -> unit
  val check_token_comments: Proof.context -> Token.T -> unit
  val output_token: Proof.context -> Token.T -> Latex.text list
  val present_thy: theory -> (Toplevel.transition * Toplevel.state) list ->
    Token.T list -> Latex.text list
  val pretty_text: Proof.context -> string -> Pretty.T
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val str_of_source: Token.src -> string
  val maybe_pretty_source: (Proof.context -> 'a -> Pretty.T) -> Proof.context ->
    Token.src -> 'a list -> Pretty.T list
  val string_of_margin: Proof.context -> Pretty.T -> string
  val output: Proof.context -> Pretty.T list -> string
  val verbatim_text: Proof.context -> string -> string
end;

structure Thy_Output: THY_OUTPUT =
struct

(* output text *)

fun output_text ctxt {markdown} source =
  let
    val pos = Input.pos_of source;
    val syms = Input.source_explode source;

    val _ = Context_Position.report ctxt pos (Markup.language_document (Input.is_delimited source));

    val output_antiquotes =
      map (fn ant =>
        Latex.text (Document_Antiquotation.evaluate ctxt ant, #1 (Antiquote.range [ant])));

    fun output_line line =
      (if Markdown.line_is_item line then [Latex.string "\\item "] else []) @
        output_antiquotes (Markdown.line_content line);

    fun output_block (Markdown.Par lines) =
          Latex.block (separate (Latex.string "\n") (map (Latex.block o output_line) lines))
      | output_block (Markdown.List {kind, body, ...}) =
          Latex.environment_block (Markdown.print_kind kind) (output_blocks body)
    and output_blocks blocks = separate (Latex.string "\n\n") (map output_block blocks);
  in
    if Toplevel.is_skipped_proof (Toplevel.presentation_state ctxt) then []
    else if markdown andalso exists (Markdown.is_control o Symbol_Pos.symbol) syms
    then
      let
        val ants = Antiquote.parse pos syms;
        val reports = Antiquote.antiq_reports ants;
        val blocks = Markdown.read_antiquotes ants;
        val _ = Context_Position.reports ctxt (reports @ Markdown.reports blocks);
      in output_blocks blocks end
    else
      let
        val ants = Antiquote.parse pos (Symbol_Pos.trim_blanks syms);
        val reports = Antiquote.antiq_reports ants;
        val _ = Context_Position.reports ctxt (reports @ Markdown.text_reports ants);
      in output_antiquotes ants end
  end;


(* output tokens with formal comments *)

local

fun output_latex syms =
  [Latex.text (Symbol_Pos.content syms, #1 (Symbol_Pos.range syms))];

fun output_symbols syms =
  [Latex.text (Latex.output_symbols (map Symbol_Pos.symbol syms), #1 (Symbol_Pos.range syms))];

val output_symbols_antiq =
  (fn Antiquote.Text syms => output_symbols syms
    | Antiquote.Control {name = (name, _), body, ...} =>
        Latex.string (Latex.output_symbols [Symbol.encode (Symbol.Control name)]) ::
          output_symbols body
    | Antiquote.Antiq {body, ...} =>
        Latex.enclose_body "%\n\\isaantiq\n" "{}%\n\\endisaantiq\n" (output_symbols body));

fun output_symbols_comment ctxt {antiq} (comment, syms) =
  (case (comment, antiq) of
    (NONE, false) => output_symbols syms
  | (NONE, true) =>
      Antiquote.parse (#1 (Symbol_Pos.range syms)) syms
      |> maps output_symbols_antiq
  | (SOME Comment.Comment, _) =>
      let
        val body = Symbol_Pos.cartouche_content syms;
        val source = Input.source true (Symbol_Pos.implode body) (Symbol_Pos.range body);
      in
        output_text ctxt {markdown = false} source
        |> Latex.enclose_body "%\n\\isamarkupcmt{" "%\n}"
      end
  | (SOME Comment.Cancel, _) =>
      output_symbols (Symbol_Pos.cartouche_content syms)
      |> Latex.enclose_body "%\n\\isamarkupcancel{" "}"
  | (SOME Comment.Latex, _) =>
      output_latex (Symbol_Pos.cartouche_content syms));

in

fun output_body ctxt antiq bg en syms =
  (case Comment.read_body syms of
    SOME res => maps (output_symbols_comment ctxt {antiq = antiq}) res
  | NONE => output_symbols syms) |> Latex.enclose_body bg en
and output_token ctxt tok =
  let
    fun output antiq bg en =
      output_body ctxt antiq bg en (Input.source_explode (Token.input_of tok));
  in
    (case Token.kind_of tok of
      Token.Comment => []
    | Token.Command => output false "\\isacommand{" "}"
    | Token.Keyword =>
        if Symbol.is_ascii_identifier (Token.content_of tok)
        then output false "\\isakeyword{" "}"
        else output false "" ""
    | Token.String => output false "{\\isachardoublequoteopen}" "{\\isachardoublequoteclose}"
    | Token.Alt_String => output false "{\\isacharbackquoteopen}" "{\\isacharbackquoteclose}"
    | Token.Verbatim => output true "{\\isacharverbatimopen}" "{\\isacharverbatimclose}"
    | Token.Cartouche => output false "{\\isacartoucheopen}" "{\\isacartoucheclose}"
    | _ => output false "" "")
  end handle ERROR msg => error (msg ^ Position.here (Token.pos_of tok));

fun check_comments ctxt =
  Comment.read_body #> (Option.app o List.app) (fn (comment, syms) =>
    let
      val pos = #1 (Symbol_Pos.range syms);
      val _ =
        comment |> Option.app (fn kind =>
          Context_Position.reports ctxt [(pos, Comment.markup kind), (pos, Markup.cartouche)]);
      val _ = output_symbols_comment ctxt {antiq = false} (comment, syms);
    in if comment = SOME Comment.Comment then check_comments ctxt syms else () end);

fun check_token_comments ctxt tok =
  check_comments ctxt (Input.source_explode (Token.input_of tok));

end;



(** present theory source **)

(*NB: arranging white space around command spans is a black art*)


(* presentation tokens *)

datatype token =
    Ignore_Token
  | Basic_Token of Token.T
  | Markup_Token of string * Input.source
  | Markup_Env_Token of string * Input.source
  | Raw_Token of Input.source;

fun basic_token pred (Basic_Token tok) = pred tok
  | basic_token _ _ = false;

val improper_token = basic_token Token.is_improper;
val comment_token = basic_token Token.is_comment;
val blank_token = basic_token Token.is_blank;
val newline_token = basic_token Token.is_newline;

fun present_token ctxt tok =
  (case tok of
    Ignore_Token => []
  | Basic_Token tok => output_token ctxt tok
  | Markup_Token (cmd, source) =>
      Latex.enclose_body ("%\n\\isamarkup" ^ cmd ^ "{") "%\n}\n"
        (output_text ctxt {markdown = false} source)
  | Markup_Env_Token (cmd, source) =>
      [Latex.environment_block ("isamarkup" ^ cmd) (output_text ctxt {markdown = true} source)]
  | Raw_Token source =>
      Latex.string "%\n" :: output_text ctxt {markdown = true} source @ [Latex.string "\n"]);


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
  else (case which (x, y) of NONE => I | SOME txt => cons (Latex.string (f txt)));

val begin_tag = edge #2 Latex.begin_tag;
val end_tag = edge #1 Latex.end_tag;
fun open_delim delim e = edge #2 Latex.begin_delim e #> delim #> edge #2 Latex.end_delim e;
fun close_delim delim e = edge #1 Latex.begin_delim e #> delim #> edge #1 Latex.end_delim e;

in

fun present_span thy keywords document_tags span state state'
    (tag_stack, active_tag, newline, latex, present_cont) =
  let
    val ctxt' =
      Toplevel.presentation_context state'
        handle Toplevel.UNDEF => Proof_Context.init_global (Context.get_theory thy Context.PureN);
    val present = fold (fn (tok, (flag, 0)) =>
        fold cons (present_token ctxt' tok)
        #> cons (Latex.string flag)
      | _ => I);

    val Span ((cmd_name, cmd_pos, cmd_tags), srcs, span_newline) = span;

    val (tag, tags) = tag_stack;
    val tag' = try hd (fold (update (op =)) cmd_tags (the_list tag));

    val nesting = Toplevel.level state' - Toplevel.level state;

    val active_tag' =
      if is_some tag' then tag'
      else if cmd_name = "end" andalso not (Toplevel.is_toplevel state') then NONE
      else
        (case Keyword.command_tags keywords cmd_name @ document_tags of
          default_tag :: _ => SOME default_tag
        | [] =>
            if Keyword.is_vacuous keywords cmd_name andalso Toplevel.is_proof state
            then active_tag
            else NONE);

    val edge = (active_tag, active_tag');

    val newline' =
      if is_none active_tag' then span_newline else newline;

    val tag_stack' =
      if nesting = 0 andalso not (Toplevel.is_proof state) then tag_stack
      else if nesting >= 0 then (tag', replicate nesting tag @ tags)
      else
        (case drop (~ nesting - 1) tags of
          tg :: tgs => (tg, tgs)
        | [] => err_bad_nesting (Position.here cmd_pos));

    val latex' =
      latex
      |> end_tag edge
      |> close_delim (fst present_cont) edge
      |> snd present_cont
      |> open_delim (present (#1 srcs)) edge
      |> begin_tag edge
      |> present (#2 srcs);
    val present_cont' =
      if newline then (present (#3 srcs), present (#4 srcs))
      else (I, present (#3 srcs) #> present (#4 srcs));
  in (tag_stack', active_tag', newline', latex', present_cont') end;

fun present_trailer ((_, tags), active_tag, _, latex, present_cont) =
  if not (null tags) then err_bad_nesting " at end of theory"
  else
    latex
    |> end_tag (active_tag, NONE)
    |> close_delim (fst present_cont) (active_tag, NONE)
    |> snd present_cont;

end;


(* present_thy *)

local

val markup_true = "\\isamarkuptrue%\n";
val markup_false = "\\isamarkupfalse%\n";

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
    Parse.!!! (improper |-- Parse.name --| (improper -- Parse.$$$ ")")));

in

fun present_thy thy command_results toks =
  let
    val keywords = Thy_Header.get_keywords thy;


    (* tokens *)

    val ignored = Scan.state --| ignore
      >> (fn d => (NONE, (Ignore_Token, ("", d))));

    fun markup pred mk flag = Scan.peek (fn d =>
      improper |--
        Parse.position (Scan.one (fn tok =>
          Token.is_command tok andalso pred keywords (Token.content_of tok))) --
      Scan.repeat tag --
      Parse.!!!! ((improper -- locale -- improper) |-- Parse.document_source --| improper_end)
      >> (fn (((tok, pos'), tags), source) =>
        let val name = Token.content_of tok
        in (SOME (name, pos', tags), (mk (name, source), (flag, d))) end));

    val command = Scan.peek (fn d =>
      Scan.optional (Scan.one Token.is_command_modifier ::: improper) [] --
      Scan.one Token.is_command -- Scan.repeat tag
      >> (fn ((cmd_mod, cmd), tags) =>
        map (fn tok => (NONE, (Basic_Token tok, ("", d)))) cmd_mod @
          [(SOME (Token.content_of cmd, Token.pos_of cmd, tags),
            (Basic_Token cmd, (markup_false, d)))]));

    val cmt = Scan.peek (fn d =>
      (Parse.$$$ "--" || Parse.$$$ Symbol.comment) |--
        Parse.!!!! (improper |-- Parse.document_source) >>
        (fn source => (NONE, (Markup_Token ("cmt", source), ("", d)))));

    val other = Scan.peek (fn d =>
       Parse.not_eof >> (fn tok => (NONE, (Basic_Token tok, ("", d)))));

    val tokens =
      (ignored ||
        markup Keyword.is_document_heading Markup_Token markup_true ||
        markup Keyword.is_document_body Markup_Env_Token markup_true ||
        markup Keyword.is_document_raw (Raw_Token o #2) "") >> single ||
      command ||
      (cmt || other) >> single;


    (* spans *)

    val is_eof = fn (_, (Basic_Token x, _)) => Token.is_eof x | _ => false;
    val stopper = Scan.stopper (K (NONE, (Basic_Token Token.eof, ("", 0)))) is_eof;

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

    val spans = toks
      |> take_suffix Token.is_space |> #1
      |> Source.of_list
      |> Source.source' 0 Token.stopper (Scan.error (Scan.bulk tokens >> flat))
      |> Source.source stopper (Scan.error (Scan.bulk span))
      |> Source.exhaust;


    (* present commands *)

    val document_tags = space_explode "," (Options.default_string \<^system_option>\<open>document_tags\<close>);

    fun present_command tr span st st' =
      Toplevel.setmp_thread_position tr
        (present_span thy keywords document_tags span st st');

    fun present _ [] = I
      | present st (((tr, st'), span) :: rest) = present_command tr span st st' #> present st' rest;
  in
    if length command_results = length spans then
      ((NONE, []), NONE, true, [], (I, I))
      |> present Toplevel.toplevel (command_results ~~ spans)
      |> present_trailer
      |> rev
    else error "Messed-up outer syntax for presentation"
  end;

end;



(** standard output operations **)

(* basic pretty printing *)

fun perhaps_trim ctxt =
  not (Config.get ctxt Document_Antiquotation.thy_output_display) ? Symbol.trim_blanks;

fun pretty_text ctxt =
  Pretty.chunks o map Pretty.str o map (perhaps_trim ctxt) o split_lines;

fun pretty_term ctxt t = Syntax.pretty_term (Variable.auto_fixes t ctxt) t;

fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;


(* default output *)

val str_of_source = space_implode " " o map Token.unparse o Token.args_of_src;

fun maybe_pretty_source pretty ctxt src xs =
  map (pretty ctxt) xs  (*always pretty in order to exhibit errors!*)
  |> (if Config.get ctxt Document_Antiquotation.thy_output_source
      then K [pretty_text ctxt (str_of_source src)] else I);

fun string_of_margin ctxt =
  Pretty.string_of_margin (Config.get ctxt Document_Antiquotation.thy_output_margin);

fun output ctxt prts =
  prts
  |> Config.get ctxt Document_Antiquotation.thy_output_quotes ? map Pretty.quote
  |> (if Config.get ctxt Document_Antiquotation.thy_output_display then
        map (Pretty.indent (Config.get ctxt Document_Antiquotation.thy_output_indent)
          #> string_of_margin ctxt #> Output.output)
        #> space_implode "\\isasep\\isanewline%\n"
        #> Latex.environment "isabelle"
      else
        map
          ((if Config.get ctxt Document_Antiquotation.thy_output_break
            then string_of_margin ctxt else Pretty.unformatted_string_of) #> Output.output)
        #> space_implode "\\isasep\\isanewline%\n"
        #> enclose "\\isa{" "}");


(* verbatim text *)

fun verbatim_text ctxt =
  if Config.get ctxt Document_Antiquotation.thy_output_display then
    split_lines #>
    map (prefix (Symbol.spaces (Config.get ctxt Document_Antiquotation.thy_output_indent))) #>
    cat_lines #>
    Latex.output_ascii #> Latex.environment "isabellett"
  else
    split_lines #>
    map (Latex.output_ascii #> enclose "\\isatt{" "}") #>
    space_implode "\\isasep\\isanewline%\n";

end;
