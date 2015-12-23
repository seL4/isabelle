(*  Title:      Pure/RAW/polyml-5.6.ML
    Author:     Makarius

Compatibility wrapper for Poly/ML 5.6.
*)

structure Thread =
struct
  open Thread;

  structure Thread =
  struct
    open Thread;

    fun numProcessors () =
      (case Thread.numPhysicalProcessors () of
        SOME n => n
      | NONE => Thread.numProcessors ());
  end;
end;

use "RAW/polyml.ML";
