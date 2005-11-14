(*  Title:      Pure/Tools/codegen_serializer.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to
target languages (like ML or Haskell)
*)

signature CODEGEN_SERIALIZER =
sig
  val bot: unit;
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

val bot = ();

end; (* structure *)
