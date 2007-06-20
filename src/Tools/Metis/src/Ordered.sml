(* ========================================================================= *)
(* ORDERED TYPES                                                             *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure IntOrdered =
struct type t = int val compare = Int.compare end;

structure StringOrdered =
struct type t = string val compare = String.compare end;
