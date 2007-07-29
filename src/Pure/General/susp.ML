(*  Title:      Pure/General/susp.ML
    ID:         $Id$
    Author:     Sebastian Skalberg and Florian Haftmann, TU Muenchen

Delayed evaluation.
*)

signature SUSP =
sig
  type 'a T
  val value: 'a -> 'a T
  val delay: (unit -> 'a) -> 'a T
  val force: 'a T -> 'a
  val peek: 'a T -> 'a option
  val same: 'a T * 'a T -> bool
end

structure Susp : SUSP =
struct

datatype 'a susp =
    Value of 'a
  | Delay of unit -> 'a;

type 'a T = 'a susp ref;

fun value v = ref (Value v);

fun delay f = ref (Delay f);

fun force susp = NAMED_CRITICAL "susp" (fn () =>
  (case ! susp of
    Value v => v
  | Delay f =>
      let
        val v = f ();
        val _ = susp := Value v;
      in v end));

fun peek susp =
  (case ! susp of
    Value v => SOME v
  | Delay _ => NONE);

fun same (r1 : 'a T, r2) = (r1 = r2); (*equality on references*)

end
