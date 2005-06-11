(*  Title:      Pure/ML-Systems/polyml-posix.ML
    ID:         $Id$

Posix patches for Poly/ML.
*)

structure OriginalPosix = Posix;
structure OriginalIO = Posix.IO;

structure Posix =
struct
  open OriginalPosix
  structure IO =
  struct
  open OriginalIO
  val mkTextReader = mkReader
  val mkTextWriter = mkWriter
  end;
end;

(*This extension of the Poly/ML Signal structure is only necessary
  because in SML/NJ, types Posix.Signal.signal and Signals.signal differ.*)
structure IsaSignal =
struct
  open Signal
  val usr1 = Posix.Signal.usr1
  val usr2 = Posix.Signal.usr2
end;
