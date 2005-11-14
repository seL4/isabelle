(*  Title:      Pure/ML-Systems/polyml-4.1.4-patch.ML
    ID:         $Id$
    Author:     Makarius

Turn the official PolyML 4.2.0 into the internal version 4.1.4, in
order to make it work with Isabelle2005.  This is to be commited into
ML_dbase! *)

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
