(*  Title:      Pure/ML-Systems/smlnj-pp-new.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)

Installation of the pretty printer, using SML/NJ's new pretty printer
interface.
*)

fun make_pp path pprint =
  let
    open Compiler.PrettyPrint;

    fun pp pps obj =
      pprint obj
        (string pps, openHOVBox pps o Rel,
          fn wd => break pps {nsp=wd, offset=0}, fn () => newline pps,
          fn () => closeBox pps);
  in
    (path, pp)
  end;
