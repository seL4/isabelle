
fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;

use "ML-Systems/polyml.ML";

print_depth 10;


(* library of general tools *)

use "General/basics.ML";
use "library.ML";
use "General/print_mode.ML";
use "General/alist.ML";
use "General/table.ML";

use "Concurrent/simple_thread.ML";

use "Concurrent/synchronized.ML";
if Multithreading.available then ()
else use "Concurrent/synchronized_sequential.ML";

use "General/properties.ML";
use "General/output.ML";
use "General/timing.ML";
use "General/markup.ML";
use "General/scan.ML";
use "General/source.ML";
use "General/symbol.ML";
use "General/seq.ML";
use "General/position.ML";
use "General/symbol_pos.ML";
use "General/antiquote.ML";
use "ML/ml_lex.ML";
use "ML/ml_parse.ML";
use "General/secure.ML";
(*^^^^^ end of basic ML bootstrap ^^^^^*)
use "General/integer.ML";
use "General/stack.ML";
use "General/queue.ML";
use "General/heap.ML";
use "General/same.ML";
use "General/ord_list.ML";
use "General/balanced_tree.ML";
use "General/graph.ML";
use "General/linear_set.ML";
use "General/buffer.ML";
use "General/pretty.ML";
use "General/xml.ML";
use "General/path.ML";
use "General/url.ML";
use "General/file.ML";
use "General/yxml.ML";
use "General/long_name.ML";
use "General/binding.ML";

use "General/sha1.ML";
if ML_System.is_polyml then use "General/sha1_polyml.ML" else ();


(* concurrency within the ML runtime *)

use "Concurrent/single_assignment.ML";
if Multithreading.available then ()
else use "Concurrent/single_assignment_sequential.ML";

if ML_System.is_smlnj then () else use "Concurrent/time_limit.ML";

if Multithreading.available
then use "Concurrent/bash.ML"
else use "Concurrent/bash_sequential.ML";

use "Concurrent/mailbox.ML";
use "Concurrent/task_queue.ML";
use "Concurrent/future.ML";

use "Concurrent/lazy.ML";
if Multithreading.available then ()
else use "Concurrent/lazy_sequential.ML";

use "Concurrent/par_list.ML";
if Multithreading.available then ()
else use "Concurrent/par_list_sequential.ML";

use "Concurrent/cache.ML";

