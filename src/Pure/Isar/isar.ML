(*  Title:      Pure/Isar/isar.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Isabelle/Isar main interface.
*)

signature ISAR =
sig
  val main: unit -> unit
  val loop: unit -> unit
  val sync_main: unit -> unit
  val sync_loop: unit -> unit
end;

structure Isar: ISAR =
struct

val main = OuterSyntax.main;
val loop = OuterSyntax.loop;
val sync_main = OuterSyntax.sync_main;
val sync_loop = OuterSyntax.sync_loop;

end;
