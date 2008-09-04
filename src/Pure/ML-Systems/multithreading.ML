(*  Title:      Pure/ML-Systems/multithreading.ML
    ID:         $Id$
    Author:     Makarius

Default implementation of multithreading interface -- mostly dummies.
*)

signature BASIC_MULTITHREADING =
sig
  val NAMED_CRITICAL: string -> (unit -> 'a) -> 'a
  val CRITICAL: (unit -> 'a) -> 'a
end;

signature MULTITHREADING =
sig
  include BASIC_MULTITHREADING
  val trace: int ref
  val tracing: int -> (unit -> string) -> unit
  val available: bool
  val max_threads: int ref
  val max_threads_value: unit -> int
  val self_critical: unit -> bool
  val serial: unit -> int
end;

structure Multithreading: MULTITHREADING =
struct

(* options *)

val trace = ref (0: int);
fun tracing _ _ = ();

val available = false;
val max_threads = ref (1: int);
fun max_threads_value () = Int.max (! max_threads, 1);


(* critical section *)

fun self_critical () = false;
fun NAMED_CRITICAL _ e = e ();
fun CRITICAL e = e ();


(* serial numbers *)

local val count = ref (0: int)
in fun serial () = (count := ! count + 1; ! count) end;

end;

structure BasicMultithreading: BASIC_MULTITHREADING = Multithreading;
open BasicMultithreading;



(** dummy thread structures (cf. polyml/basis/Thread.sml) **)

exception Thread of string;

local fun fail _ = raise Thread "No multithreading support on this ML platform" in

structure Mutex =
struct
  type mutex = unit;
  fun mutex _ = fail ();
  fun lock _ = fail ();
  fun unlock _ = fail ();
  fun trylock _ = fail ();
end;

structure ConditionVar =
struct
  type conditionVar = unit;
  fun conditionVar _ = fail ();
  fun wait _ = fail ();
  fun waitUntil _ = fail ();
  fun signal _ = fail ();
  fun broadcast _ = fail ();
end;

structure Thread =
struct
  type thread = unit;

  datatype threadAttribute = EnableBroadcastInterrupt of bool | InterruptState of interruptState
    and interruptState = InterruptDefer | InterruptSynch | InterruptAsynch | InterruptAsynchOnce;

  fun fork _ = fail ();
  fun exit _ = fail ();
  fun isActive _ = fail ();

  fun equal _ = fail ();
  fun self _ = fail ();

  fun interrupt _ = fail ();
  fun broadcastInterrupt _ = fail ();
  fun testInterrupt _ = fail ();

  fun kill _ = fail ();

  fun setAttributes _ = fail ();
  fun getAttributes _ = fail ();

  fun numProcessors _ = fail ();


(* thread data *)

local

val data = ref ([]: Universal.universal ref list);

fun find_data tag =
  let
    fun find (r :: rs) = if Universal.tagIs tag (! r) then SOME r else find rs
      | find [] = NONE;
  in find (! data) end;

in

fun getLocal tag = Option.map (Universal.tagProject tag o !) (find_data tag);

fun setLocal (tag, x) =
  (case find_data tag of
    SOME r => r := Universal.tagInject tag x
  | NONE => data := ref (Universal.tagInject tag x) :: ! data);

end;
end;
end;
