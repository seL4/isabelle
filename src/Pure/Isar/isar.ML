(*  Title:      Pure/Isar/isar.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar main interface.
*)

signature ISAR =
sig
  type parser
  val main: unit -> unit
  val loop: unit -> unit
  val help: unit -> unit
  val commands: unit -> string list
  val add_keywords: string list -> unit
  val add_parsers: parser list -> unit
end;

structure Isar: ISAR =
struct

type parser = OuterSyntax.parser;
val main = OuterSyntax.main;
val loop = OuterSyntax.loop;
val help = OuterSyntax.help;
val commands = OuterSyntax.commands;
val add_keywords = OuterSyntax.add_keywords;
val add_parsers = OuterSyntax.add_parsers;

end;
