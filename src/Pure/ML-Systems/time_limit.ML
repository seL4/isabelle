(*  Title:      Pure/ML-Systems/time_limit.ML
    Author:     Makarius

Dummy implementation of NJ's TimeLimit structure.
*)

signature TIME_LIMIT =
sig
  exception TimeOut
  val timeLimit : Time.time -> ('a -> 'b) -> 'a -> 'b
end;

structure TimeLimit: TIME_LIMIT =
struct

exception TimeOut;
fun timeLimit _ f x = f x;

end;

