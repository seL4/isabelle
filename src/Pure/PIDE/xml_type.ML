(*  Title:      Pure/PIDE/xml_type.ML
    Author:     Makarius

Untyped XML trees: minimal type definitions.
*)

signature XML =
sig
  type attributes = (string * string) list
  datatype tree =
      Elem of (string * attributes) * tree list
    | Text of string
  type body = tree list
end

structure XML: XML =
struct

type attributes = (string * string) list;

datatype tree =
    Elem of (string * attributes) * tree list
  | Text of string;

type body = tree list;

end;
