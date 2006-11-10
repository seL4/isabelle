(*  Title:      Pure/ML-Systems/polyml-4.1.4-patch.ML
    ID:         $Id$

Basis library fixes for Poly/ML 4.2.0 or later.
*)

structure Posix =
struct
  open Posix;
  structure IO =
  struct
    open IO;
    val mkReader = mkTextReader;
    val mkWriter = mkTextWriter;
  end;
end;

structure TextIO =
struct
  open TextIO;
  fun inputLine is = Option.getOpt (TextIO.inputLine is, "");
end;

structure Substring =
struct
  open Substring;
  val all = full;
end;
