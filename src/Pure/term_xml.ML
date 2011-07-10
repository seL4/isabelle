(*  Title:      Pure/term_xml.ML
    Author:     Makarius

XML data representation of lambda terms.
*)

signature TERM_XML_OPS =
sig
  type 'a T
  val indexname: indexname T
  val class: class T
  val sort: sort T
  val typ: typ T
  val term: term T
end

signature TERM_XML =
sig
  structure Make: TERM_XML_OPS where type 'a T = 'a XML_Data.Make.T
  structure Dest: TERM_XML_OPS where type 'a T = 'a XML_Data.Dest.T
end;

structure Term_XML: TERM_XML =
struct

(* make *)

structure Make =
struct

open XML_Data.Make;

val indexname = pair string int;
val class = string;
val sort = list class;

fun typ T = T |> variant
 [fn Type x => pair string (list typ) x,
  fn TFree x => pair string sort x,
  fn TVar x => pair indexname sort x];

fun term t = t |> variant
 [fn Const x => pair string typ x,
  fn Free x => pair string typ x,
  fn Var x => pair indexname typ x,
  fn Bound x => int x,
  fn Abs x => triple string typ term x,
  fn op $ x => pair term term x];

end;


(* dest *)

structure Dest =
struct

open XML_Data.Dest;

val indexname = pair string int;
val class = string;
val sort = list class;

fun typ T = T |> variant
 [Type o pair string (list typ),
  TFree o pair string sort,
  TVar o pair indexname sort];

fun term t = t |> variant
 [Const o pair string typ,
  Free o pair string typ,
  Var o pair indexname typ,
  Bound o int,
  Abs o triple string typ term,
  op $ o pair term term];

end;

end;
