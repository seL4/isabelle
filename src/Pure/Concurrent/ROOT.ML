(*  Title:      Pure/Concurrent/ROOT.ML
    ID:         $Id$

Concurrency within the ML runtime.
*)

val future_scheduler = ref true;

use "simple_thread.ML";
use "synchronized.ML";
use "mailbox.ML";
use "schedule.ML";
use "task_queue.ML";
use "future.ML";
use "par_list.ML";
if Multithreading.available then () else use "par_list_dummy.ML";

