(*  Title:      Pure/ML-Systems/thread_physical_processors.ML
    Author:     Makarius

Emulation of structure Thread in Poly/ML 5.5.2 (SVN 1890).
*)

structure Thread =
struct
  open Thread;

  fun numPhysicalProcessors () : int option = NONE;
end;
