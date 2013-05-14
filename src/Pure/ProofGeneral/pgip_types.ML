(*  Title:      Pure/ProofGeneral/pgip_types.ML
    Author:     David Aspinall

Some PGIP types and conversions.
*)

signature PGIPTYPES =
sig
  exception PGIP of string
  val attr: string -> string -> XML.attributes
  val opt_attr: string -> string option -> XML.attributes
  val get_attr: XML.attributes -> string -> string           (* raises PGIP *)
end

structure PgipTypes : PGIPTYPES =
struct

exception PGIP of string

fun get_attr attrs name =
  (case Properties.get attrs name of
    SOME value => value
  | NONE => raise PGIP ("Missing attribute: " ^ quote name));

fun attr x y = [(x,y)] : XML.attributes

fun opt_attr _ NONE = []
  | opt_attr name (SOME value) = attr name value;

end

