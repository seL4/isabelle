(*  Title:      Pure/Tools/isabelle_process.ML
    ID:         $Id$
    Author:     Makarius

Isabelle process wrapper -- interaction via external program.
*)

signature ISABELLE_PROCESS =
sig
  val test_markupN: string
  val test_markup: Markup.T -> output * output
  val init: unit -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

(* test markup *)

val test_markupN = "test_markup";

fun test_markup (name, props) =
 (enclose "<" ">" (space_implode " " (name :: map XML.attribute props)),
  enclose "</" ">" name);

val _ = Markup.add_mode test_markupN test_markup;


(* channels *)

local

fun special c = chr 2 ^ c;
val special_end = special "Z";

fun output c m s =
  Output.writeln_default (special c ^ Markup.enclose m s ^ special_end);

in

fun setup_channels () =
 (Output.writeln_fn  := output "A" Markup.writeln;
  Output.priority_fn := output "B" Markup.priority;
  Output.tracing_fn  := output "C" Markup.tracing;
  Output.warning_fn  := output "D" Markup.warning;
  Output.error_fn    := output "E" Markup.error;
  Output.debug_fn    := output "F" Markup.debug);

end;


(* init *)

fun init () =
 (Output.writeln_default ("PID=" ^ string_of_pid (Posix.ProcEnv.getpid ()));
  setup_channels ();
  Isar.secure_main ());

end;

