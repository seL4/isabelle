(* ========================================================================= *)
(* NAMES                                                                     *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Name =
sig

type name = string

val compare : name * name -> order

val pp : name Parser.pp

end
