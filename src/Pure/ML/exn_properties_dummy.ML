(*  Title:      Pure/ML/exn_properties_dummy.ML
    Author:     Makarius

Exception properties -- dummy version.
*)

signature EXN_PROPERTIES =
sig
  val position_of: 'location -> Position.T
  val get: exn -> Properties.T
  val update: Properties.entry list -> exn -> exn
end;

structure Exn_Properties: EXN_PROPERTIES =
struct

fun position_of _ = Position.none;

fun get _ = [];
fun update _ exn = exn;

end;

