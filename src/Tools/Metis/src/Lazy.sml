(* ========================================================================= *)
(* SUPPORT FOR LAZY EVALUATION                                               *)
(* Copyright (c) 2007 Joe Hurd, distributed under the BSD License      *)
(* ========================================================================= *)

structure Lazy :> Lazy =
struct

datatype 'a thunk =
    Value of 'a
  | Thunk of unit -> 'a;

datatype 'a lazy = Lazy of 'a thunk ref;

fun delay f = Lazy (ref (Thunk f));

fun force (Lazy (ref (Value v))) = v
  | force (Lazy (s as ref (Thunk f))) =
    let
      val v = f ()
      val () = s := Value v
    in
      v
    end;

fun memoize f =
    let
      val t = delay f
    in
      fn () => force t
    end;

end
