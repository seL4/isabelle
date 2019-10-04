(*  Title:      Pure/term_xml.ML
    Author:     Makarius

XML data representation of lambda terms.
*)

signature TERM_XML_OPS =
sig
  type 'a T
  val sort: sort T
  val typ: typ T
  val term: Consts.T -> term T
  val term_raw: term T
end

signature TERM_XML =
sig
  structure Encode: TERM_XML_OPS
  structure Decode: TERM_XML_OPS
end;

structure Term_XML: TERM_XML =
struct

structure Encode =
struct

open XML.Encode;

val sort = list string;

fun typ T = T |> variant
 [fn Type (a, b) => ([a], list typ b),
  fn TFree (a, b) => ([a], sort b),
  fn TVar ((a, b), c) => ([a, int_atom b], sort c)];

fun term consts t = t |> variant
 [fn Const (a, b) => ([a], list typ (Consts.typargs consts (a, b))),
  fn Free (a, b) => ([a], typ b),
  fn Var ((a, b), c) => ([a, int_atom b], typ c),
  fn Bound a => ([int_atom a], []),
  fn Abs (a, b, c) => ([a], pair typ (term consts) (b, c)),
  fn op $ a => ([], pair (term consts) (term consts) a)];

fun term_raw t = t |> variant
 [fn Const (a, b) => ([a], typ b),
  fn Free (a, b) => ([a], typ b),
  fn Var ((a, b), c) => ([a, int_atom b], typ c),
  fn Bound a => ([int_atom a], []),
  fn Abs (a, b, c) => ([a], pair typ term_raw (b, c)),
  fn op $ a => ([], pair term_raw term_raw a)];

end;

structure Decode =
struct

open XML.Decode;

val sort = list string;

fun typ T = T |> variant
 [fn ([a], b) => Type (a, list typ b),
  fn ([a], b) => TFree (a, sort b),
  fn ([a, b], c) => TVar ((a, int_atom b), sort c)];

fun term consts t = t |> variant
 [fn ([a], b) => Const (a, Consts.instance consts (a, list typ b)),
  fn ([a], b) => Free (a, typ b),
  fn ([a, b], c) => Var ((a, int_atom b), typ c),
  fn ([a], []) => Bound (int_atom a),
  fn ([a], b) => let val (c, d) = pair typ (term consts) b in Abs (a, c, d) end,
  fn ([], a) => op $ (pair (term consts) (term consts) a)];

fun term_raw t = t |> variant
 [fn ([a], b) => Const (a, typ b),
  fn ([a], b) => Free (a, typ b),
  fn ([a, b], c) => Var ((a, int_atom b), typ c),
  fn ([a], []) => Bound (int_atom a),
  fn ([a], b) => let val (c, d) = pair typ term_raw b in Abs (a, c, d) end,
  fn ([], a) => op $ (pair term_raw term_raw a)];

end;

end;
