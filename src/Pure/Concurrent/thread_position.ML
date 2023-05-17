(*  Title:      Pure/Concurrent/thread_position.ML
    Author:     Makarius

Thread-local position information.
*)

signature THREAD_POSITION =
sig
  type T = {line: int, offset: int, end_offset: int, props: {label: string, file: string, id: string}}
  val none: T
  val get: unit -> T
  val setmp: T -> ('a -> 'b) -> 'a -> 'b
end;

structure Thread_Position: THREAD_POSITION =
struct

type T = {line: int, offset: int, end_offset: int, props: {label: string, file: string, id: string}};

val var = Thread_Data.var () : T Thread_Data.var;

val none: T = {line = 0, offset = 0, end_offset = 0, props = {label = "", file = "", id = ""}};

fun get () = (case Thread_Data.get var of NONE => none | SOME pos => pos);
fun setmp pos f x = Thread_Data.setmp var (if pos = none then NONE else SOME pos) f x;

end;
