(*  Title:      Pure/ML-Systems/polyml-posix.ML
    ID:         $Id$

Posix patches for Poly/ML.
*)

(*This extension of the Poly/ML Signal structure is only necessary
  because in SML/NJ, types Posix.Signal.signal and Signals.signal differ.*)
structure IsaSignal =
struct
  open Signal
  val usr1 = Posix.Signal.usr1
  val usr2 = Posix.Signal.usr2
  val alrm = Posix.Signal.alrm
  val chld = Posix.Signal.chld
  val cont = Posix.Signal.cont
  val int  = Posix.Signal.int
  val quit = Posix.Signal.quit
end;
