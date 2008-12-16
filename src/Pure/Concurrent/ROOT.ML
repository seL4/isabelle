(*  Title:      Pure/Concurrent/ROOT.ML
    Author:     Makarius

Concurrency within the ML runtime.
*)

use "simple_thread.ML";
use "synchronized.ML";
use "mailbox.ML";
use "task_queue.ML";
use "future.ML";
use "par_list.ML";
if Multithreading.available then () else use "par_list_dummy.ML";

