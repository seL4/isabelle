(*  Title:      Pure/ML-Systems/smlnj-basis-compat.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)

Compatibility file for Standard ML of New Jersey 110.44 or later. Here
signatures that have changed to adhere to the SML Basis Library are
changed back to their old values.
*)

structure TextIO =
struct
  open TextIO;

  fun inputLine is =
    (case TextIO.inputLine is of
      SOME str => str
    | NONE => "")
    handle IO.Io _ => raise Interrupt;
end;
