(* ========================================================================= *)
(* ORDERED TYPES                                                             *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure IntOrdered =
struct type t = int val compare = Int.compare end;

structure IntPairOrdered =
struct

type t = int * int;

fun compare ((i1,j1),(i2,j2)) =
    case Int.compare (i1,i2) of
      LESS => LESS
    | EQUAL => Int.compare (j1,j2)
    | GREATER => GREATER;

end;

structure StringOrdered =
struct type t = string val compare = String.compare end;
