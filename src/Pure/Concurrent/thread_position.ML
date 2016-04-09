(*  Title:      Pure/Concurrent/thread_position.ML
    Author:     Makarius

Thread-local position information.
*)

signature THREAD_POSITION =
sig
  val get: unit -> (string * string) list
  val setmp: (string * string) list -> ('a -> 'b) -> 'a -> 'b
end;

structure Thread_Position: THREAD_POSITION =
struct

val var = Thread_Data.var () : (string * string) list Thread_Data.var;

fun get () =
  (case Thread_Data.get var of
    NONE => []
  | SOME props => props);

fun setmp props f x =
  Thread_Data.setmp var (if List.null props then NONE else SOME props) f x;

end;
