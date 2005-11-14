(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code extractor from Isabelle theories to
intermediate language ("Thin-gol").
*)

(*NOTE: for simpliying development, this package contains
some stuff which will finally be moved upwards to HOL*)

signature CODEGEN_PACKAGE =
sig
  val bot: unit;
end;

structure CodegenPackage: CODEGEN_PACKAGE =
struct

val bot = ();

end; (* structure *)
