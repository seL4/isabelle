(*  Title:      Pure/ML/exn_output.ML
    Author:     Makarius

Auxiliary operations for exception output.
*)

signature EXN_OUTPUT =
sig
  val position: exn -> Position.T
  val pretty: exn -> Pretty.T
end;

structure Exn_Output: EXN_OUTPUT =
struct

fun position exn =
  (case PolyML.exceptionLocation exn of
    NONE => Position.none
  | SOME loc => Exn_Properties.position_of loc);

fun pretty (exn: exn) =
  Pretty.from_ML (pretty_ml (PolyML.prettyRepresentation (exn, ML_Options.get_print_depth ())));

end;
