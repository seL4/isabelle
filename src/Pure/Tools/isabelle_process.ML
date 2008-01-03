(*  Title:      Pure/Tools/isabelle_process.ML
    ID:         $Id$
    Author:     Makarius

Isabelle process wrapper -- interaction via external program.

General format of process output:

  (a) unmarked stdout/stderr, no line structure (output should be
  processed immediately as it arrives)

  (b) echo of my pid on stdout, appears *relatively* early after
  startup on a separate line, e.g. "\nPID=4711\n"

  (c) properly marked-up messages, e.g. for writeln channel

  "\002A" ^ props ^ "\002,\n" ^ text ^ "\002.\n"

  where the props consist of name=value lines terminated by "\002,"
  each, and the remaining text is any number of lines (output is
  supposed to be processed in one piece).
*)

signature ISABELLE_PROCESS =
sig
  val test_markupN: string
  val test_markup: Markup.T -> output * output
  val isabelle_processN: string
  val init: unit -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

(* test_markup *)

val test_markupN = "test_markup";

fun test_markup (name, props) =
 (enclose "<" ">" (space_implode " " (name :: map XML.attribute props)),
  enclose "</" ">" name);

val _ = Markup.add_mode test_markupN test_markup;


(* channels *)

val isabelle_processN = "isabelle_process";

local

fun special c = chr 2 ^ c;
val special_sep = special ",";
val special_end = special ".";

fun message_props () =
  let
    val thread_props = Toplevel.thread_properties ();
    val props =
      (case AList.lookup (op =) thread_props Markup.idN of
        SOME id => [(Markup.idN, id)]
      | NONE => Position.properties_of (#1 (Position.of_properties thread_props)));
  in implode (map (fn (x, y) => x ^ "=" ^ y ^ special_sep ^ "\n") props) end;

fun output ch markup txt =
  Output.writeln_default (special ch ^ message_props () ^ Markup.enclose markup txt ^ special_end);

in

fun setup_channels () =
 (Output.writeln_fn  := output "A" Markup.writeln;
  Output.priority_fn := output "B" Markup.priority;
  Output.tracing_fn  := output "C" Markup.tracing;
  Output.warning_fn  := output "D" Markup.warning;
  Output.error_fn    := output "E" Markup.error;
  Output.debug_fn    := output "F" Markup.debug);

val _ = Markup.add_mode isabelle_processN (fn (name, _) =>
  if name = Markup.promptN then (special "G", special_end ^ "\n")
  else ("", ""));

end;


(* init *)

fun init () =
 (Output.writeln_default ("\nPID=" ^ string_of_pid (Posix.ProcEnv.getpid ()));
  setup_channels ();
  change print_mode (update (op =) isabelle_processN);
  Isar.secure_main ());

end;

