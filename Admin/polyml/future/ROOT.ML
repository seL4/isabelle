
fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;

use "ML-Systems/polyml.ML";

print_depth 10;

use "General/basics.ML";
use "library.ML";
use "General/alist.ML";
use "General/table.ML";
use "General/graph.ML";

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

