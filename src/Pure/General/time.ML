(*  Title:      Pure/General/time.scala
    Author:     Makarius

Time based on nanoseconds (idealized).
*)

signature TIME =
sig
  include TIME
  val min: time * time -> time
  val max: time * time -> time
  val scale: real -> time -> time
  val parse: string -> time
  val print: time -> string
  val message: time -> string
end;

structure Time: TIME =
struct

open Time;

fun min (t1, t2) = if t1 < t2 then t1 else t2;
fun max (t1, t2) = if t1 > t2 then t1 else t2;

fun scale s t = Time.fromNanoseconds (Real.ceil (s * Real.fromInt (Time.toNanoseconds t)));

fun parse s =
  (case Time.fromString s of
    SOME t => t
  | NONE => raise Fail ("Bad time " ^ quote s));

fun print t =
  if t < Time.zeroTime then "-" ^ Time.toString (Time.zeroTime - t)
  else Time.toString t;

fun message t = print t ^ "s";

end;
