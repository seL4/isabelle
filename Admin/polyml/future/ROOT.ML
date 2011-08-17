
fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;

fun reraise exn =
  (case PolyML.exceptionLocation exn of
    NONE => raise exn
  | SOME location => PolyML.raiseWithLocation (exn, location));

fun set_exn_serial i exn =
  let
    val (file, startLine, endLine) =
      (case PolyML.exceptionLocation exn of
        NONE => ("", 0, 0)
      | SOME {file, startLine, endLine, startPosition, ...} => (file, startLine, endLine));
    val location =
      {file = file, startLine = startLine, endLine = endLine,
        startPosition = ~ i, endPosition = 0};
  in PolyML.raiseWithLocation (exn, location) handle e => e end;

fun get_exn_serial exn =
  (case Option.map #startPosition (PolyML.exceptionLocation exn) of
    NONE => NONE
  | SOME i => if i >= 0 then NONE else SOME (~ i));

exception Interrupt = SML90.Interrupt;
val ord = SML90.ord;
val chr = SML90.chr;
val raw_explode = SML90.explode;
val implode = SML90.implode;

val pointer_eq = PolyML.pointerEq;

val exception_trace = PolyML.exception_trace;

open Thread;
val seconds = Time.fromReal;
use "General/exn.ML";
use "ML-Systems/multithreading.ML";
use "ML-Systems/multithreading_polyml.ML";
use "ML-Systems/unsynchronized.ML";

use "ML-Systems/ml_pretty.ML";

val pretty_ml =
  let
    fun convert len (PolyML.PrettyBlock (ind, _, context, prts)) =
          let
            fun property name default =
              (case List.find (fn PolyML.ContextProperty (a, _) => name = a | _ => false) context of
                SOME (PolyML.ContextProperty (_, b)) => b
              | NONE => default);
            val bg = property "begin" "";
            val en = property "end" "";
            val len' = property "length" len;
          in ML_Pretty.Block ((bg, en), map (convert len') prts, ind) end
      | convert len (PolyML.PrettyString s) =
          ML_Pretty.String (s, case Int.fromString len of SOME i => i | NONE => size s)
      | convert _ (PolyML.PrettyBreak (wd, _)) =
          ML_Pretty.Break (if wd < 99999 then (false, wd) else (true, 2));
  in convert "" end;

fun ml_pretty (ML_Pretty.Block ((bg, en), prts, ind)) =
      let val context =
        (if bg = "" then [] else [PolyML.ContextProperty ("begin", bg)]) @
        (if en = "" then [] else [PolyML.ContextProperty ("end", en)])
      in PolyML.PrettyBlock (ind, false, context, map ml_pretty prts) end
  | ml_pretty (ML_Pretty.String (s, len)) =
      if len = size s then PolyML.PrettyString s
      else PolyML.PrettyBlock
        (0, false, [PolyML.ContextProperty ("length", Int.toString len)], [PolyML.PrettyString s])
  | ml_pretty (ML_Pretty.Break (false, wd)) = PolyML.PrettyBreak (wd, 0)
  | ml_pretty (ML_Pretty.Break (true, _)) = PolyML.PrettyBreak (99999, 0);

use "General/basics.ML";
use "library.ML";
use "General/alist.ML";
use "General/table.ML";
use "General/graph.ML";
use "General/ord_list.ML";

structure Position =
struct
  fun thread_data () = ();
  fun setmp_thread_data () f x = f x;
end;

structure Output =
struct
  type output = string;
  fun escape s : output = s;
  fun raw_stdout s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
  fun writeln s = raw_stdout (suffix "\n" s);
  fun warning s = writeln (prefix_lines "### " s);
  fun status (_: string) = ();
end;
val writeln = Output.writeln;
val warning = Output.warning;
fun print_mode_value () : string list = [];

use "General/properties.ML";
use "General/timing.ML";

use "Concurrent/simple_thread.ML";
use "Concurrent/synchronized.ML";
use "General/markup.ML";
use "Concurrent/single_assignment.ML";
use "Concurrent/time_limit.ML";
use "Concurrent/par_exn.ML";
use "Concurrent/task_queue.ML";
use "Concurrent/future.ML";
use "Concurrent/lazy.ML";
use "Concurrent/par_list.ML";

use "General/queue.ML";
use "Concurrent/mailbox.ML";
use "Concurrent/cache.ML";

PolyML.addPrettyPrinter (fn depth => fn pretty => fn var =>
  pretty (Synchronized.value var, depth));

PolyML.addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Future.peek x of
    NONE => PolyML.PrettyString "<future>"
  | SOME (Exn.Exn _) => PolyML.PrettyString "<failed>"
  | SOME (Exn.Res y) => pretty (y, depth)));

PolyML.addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Lazy.peek x of
    NONE => PolyML.PrettyString "<lazy>"
  | SOME (Exn.Exn _) => PolyML.PrettyString "<failed>"
  | SOME (Exn.Res y) => pretty (y, depth)));

