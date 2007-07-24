(*  Title:      Pure/ML-Systems/multithreading_polyml.ML
    ID:         $Id$
    Author:     Makarius

Multithreading in Poly/ML (version 5.1).
*)

open Thread;

structure Multithreading: MULTITHREADING =
struct

val number_of_threads = ref 0;


(* FIXME tmp *)
fun message s =
  (TextIO.output (TextIO.stdErr, (">>> " ^ s ^ "\n")); TextIO.flushOut TextIO.stdErr);


(* critical section -- may be nested within the same thread *)

local

val critical_lock = Mutex.mutex ();
val critical_thread = ref (NONE: Thread.thread option);

in

fun self_critical () =
  (case ! critical_thread of
    NONE => false
  | SOME id => Thread.equal (id, Thread.self ()));

fun CRITICAL e =
  if self_critical () then e ()
  else
    let
      val _ =
        if Mutex.trylock critical_lock then ()
        else
          (message "Waiting for critical lock";
           Mutex.lock critical_lock;
           message "Obtained critical lock");
      val _ = critical_thread := SOME (Thread.self ());
      val result = Exn.capture e ();
      val _ = critical_thread := NONE;
      val _ = Mutex.unlock critical_lock;
    in Exn.release result end;

end;

end;

val CRITICAL = Multithreading.CRITICAL;
