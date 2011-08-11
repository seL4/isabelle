
fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;

use "ML-Systems/polyml.ML";

print_depth 10;

use "General/basics.ML";
use "library.ML";
use "General/alist.ML";
use "General/table.ML";
use "General/queue.ML";
use "General/graph.ML";

use "Concurrent/simple_thread.ML";
use "Concurrent/synchronized.ML";

use "General/properties.ML";
use "General/print_mode.ML";
use "General/output.ML";
use "General/timing.ML";
use "General/markup.ML";
use "General/scan.ML";
use "General/source.ML";
use "General/symbol.ML";
use "General/position.ML";

use "Concurrent/single_assignment.ML";
use "Concurrent/time_limit.ML";
use "Concurrent/mailbox.ML";
use "Concurrent/task_queue.ML";
use "Concurrent/future.ML";
use "Concurrent/lazy.ML";
use "Concurrent/par_list.ML";
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

