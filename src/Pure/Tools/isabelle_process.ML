(*  Title:      Pure/Tools/isabelle_process.ML
    ID:         $Id$
    Author:     Makarius

Isabelle process wrapper -- interaction via external program.

General format of process output:

  (a) unmarked stdout/stderr, no line structure (output should be
  processed immediately as it arrives);

  (b) properly marked-up messages, e.g. for writeln channel

  "\002A" ^ props ^ "\002,\n" ^ text ^ "\002.\n"

  where the props consist of name=value lines terminated by "\002,\n"
  each, and the remaining text is any number of lines (output is
  supposed to be processed in one piece);

  (c) special init message holds "pid" and "session" property.
*)

signature ISABELLE_PROCESS =
sig
  val output_markup: Markup.T -> output * output
  val full_markupN: string
  val test_markupN: string
  val isabelle_processN: string
  val init: unit -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

(* explicit markup *)

fun output_markup (name, props) =
 (enclose "<" ">" (space_implode " " (name :: map XML.attribute props)),
  enclose "</" ">" name);

val full_markupN = "full_markup";
val test_markupN = "test_markup";

val _ = Markup.add_mode test_markupN output_markup;


(* symbol output *)

val isabelle_processN = "isabelle_process";

local

fun output str =
  let
    fun out s = if Symbol.is_raw s then Symbol.decode_raw s else XML.text s;
    val syms = Symbol.explode str;
  in (implode (map out syms), Symbol.length syms) end;

in

val _ = Output.add_mode isabelle_processN output Symbol.encode_raw;

end;


(* message markup *)

val STX = chr 2;
val DEL = chr 127;

fun special ch = STX ^ ch;
val special_sep = special ",";
val special_end = special ".";

local

fun print_props props =
  let
    val clean = translate_string (fn c =>
      if c = STX orelse c = "\n" orelse c = "\r" then DEL else c);
  in implode (map (fn (x, y) => clean x ^ "=" ^ clean y ^ special_sep ^ "\n") props) end;

fun get_pos (elem as XML.Elem (name, atts, ts)) =
      if name = Markup.positionN then SOME (Position.of_properties atts)
      else get_first get_pos ts
  | get_pos _ = NONE;

in

val _ = Markup.add_mode isabelle_processN (fn (name, props) =>
  if print_mode_active full_markupN orelse name = Markup.positionN
  then output_markup (name, props) else ("", ""));

fun message ch txt0 =
  let
    val txt1 = XML.element "message" [] [txt0];
    val (txt, pos) =
      (case try XML.tree_of_string txt1 of
        NONE => (txt1, Position.none)
      | SOME xml =>
          (if print_mode_active full_markupN then XML.header ^ txt1 else XML.plain_content xml,
            the_default Position.none (get_pos xml)))
      |>> translate_string (fn c => if c = STX then DEL else c);
    val props =
      Position.properties_of (Position.thread_data ())
      |> Position.default_properties pos;
  in Output.writeln_default (special ch ^ print_props props ^ txt ^ special_end) end;

fun init_message () =
  let
    val pid = ("pid", string_of_pid (Posix.ProcEnv.getpid ()));
    val session = ("session", List.last (Session.id ()) handle List.Empty => "unknown");
    val welcome = Session.welcome ();
  in Output.writeln_default (special "H" ^ print_props [pid, session] ^ welcome ^ special_end) end;

end;


(* channels *)

fun setup_channels () =
 (Output.writeln_fn  := message "A";
  Output.priority_fn := message "B";
  Output.tracing_fn  := message "C";
  Output.warning_fn  := message "D";
  Output.error_fn    := message "E";
  Output.debug_fn    := message "F";
  Output.prompt_fn   := message "G");


(* token translations *)

local

fun markup kind x =
  ((output_markup (kind, []) |-> enclose) (Output.output x), Symbol.length (Symbol.explode x));

fun free_or_skolem x =
  (case try Name.dest_skolem x of
    NONE => markup Markup.freeN x
  | SOME x' => markup Markup.skolemN x');

fun var_or_skolem s =
  (case Lexicon.read_variable s of
    SOME (x, i) =>
      (case try Name.dest_skolem x of
        NONE => markup Markup.varN s
      | SOME x' => markup Markup.skolemN
          (setmp show_question_marks true Term.string_of_vname (x', i)))
  | NONE => markup Markup.varN s);

val token_trans =
 Syntax.tokentrans_mode full_markupN
  [("class", markup Markup.classN),
   ("tfree", markup Markup.tfreeN),
   ("tvar", markup Markup.tvarN),
   ("free", free_or_skolem),
   ("bound", markup Markup.boundN),
   ("var", var_or_skolem)];

in

val _ = Context.>> (Context.map_theory (Sign.add_tokentrfuns token_trans));

end;


(* init *)

fun init () =
 (change print_mode (update (op =) isabelle_processN);
  setup_channels ();
  init_message ();
  Isar.secure_main ());

end;

