(*  Title:      Pure/Isar/isar.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar main interface.
*)

signature ISAR =
sig
  val main: unit -> unit
  val loop: unit -> unit
  val help: unit -> unit
end;

structure Isar: ISAR =
struct

val main = OuterSyntax.main;
val loop = OuterSyntax.loop;
val help = OuterSyntax.help;

end;
