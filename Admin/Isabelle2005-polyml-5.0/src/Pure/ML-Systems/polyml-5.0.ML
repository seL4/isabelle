(*  Title:      Pure/ML-Systems/polyml-5.0.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML 5.0 -- version for Isabelle2005.
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


use "ML-Systems/polyml.ML";

val pointer_eq = PolyML.pointerEq;
