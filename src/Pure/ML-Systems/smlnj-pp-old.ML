(*  Title:      Pure/ML-Systems/smlnj-pp-old.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)

Installation of the pretty printer, using SML/NJ's old pretty printer
interface.
*)

fun make_pp path pprint =
  let
    open Compiler.PrettyPrint;

    fun pp pps obj =
      pprint obj
        (add_string pps, begin_block pps INCONSISTENT,
          fn wd => add_break pps (wd, 0), fn () => add_newline pps,
          fn () => end_block pps);
  in
    (path, pp)
  end;
