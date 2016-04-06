(*  Title:      Pure/Concurrent/thread_data.ML
    Author:     Makarius

Thread-local data -- physical version without context management.
*)

signature THREAD_DATA =
sig
  type 'a var
  val var: unit -> 'a var
  val get: 'a var -> 'a option
  val put: 'a var -> 'a option -> unit
  val setmp: 'a var -> 'a option -> ('b -> 'c) -> 'b -> 'c
  val is_virtual: bool
end;

structure Thread_Data: THREAD_DATA =
struct

open Thread;


(* exceptions as values *)

structure Exn =
struct

datatype 'a result =
  Res of 'a |
  Exn of exn;

fun capture f x = Res (f x) handle e => Exn e;

fun release (Res y) = y
  | release (Exn e) = PolyML.Exception.reraise e;

end;


(* thread attributes *)

local

val no_interrupts =
  [Thread.EnableBroadcastInterrupt false, Thread.InterruptState Thread.InterruptDefer];

val safe_interrupts = map
  (fn Thread.InterruptState Thread.InterruptAsynch =>
      Thread.InterruptState Thread.InterruptAsynchOnce
    | x => x);

fun with_attributes new_atts e =
  let
    val orig_atts = safe_interrupts (Thread.getAttributes ());
    val result = Exn.capture (fn () =>
      (Thread.setAttributes (safe_interrupts new_atts); e orig_atts)) ();
    val _ = Thread.setAttributes orig_atts;
  in Exn.release result end;

in

fun uninterruptible f x =
  with_attributes no_interrupts (fn atts =>
    f (fn g => fn y => with_attributes atts (fn _ => g y)) x);

end;


(* var *)

abstype 'a var = Var of 'a option Universal.tag
with

fun var () : 'a var = Var (Universal.tag ());

fun get (Var tag) =
  (case Thread.getLocal tag of
    SOME data => data
  | NONE => NONE);

fun put (Var tag) data = Thread.setLocal (tag, data);

fun setmp v data f x =
  uninterruptible (fn restore_attributes => fn () =>
    let
      val orig_data = get v;
      val _ = put v data;
      val result = Exn.capture (restore_attributes f) x;
      val _ = put v orig_data;
    in Exn.release result end) ();

end;

val is_virtual = false;

end;
