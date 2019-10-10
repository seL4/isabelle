(*  Title:      Pure/term_xml.ML
    Author:     Makarius

XML data representation of lambda terms.
*)

signature TERM_XML_OPS =
sig
  type 'a T
  type 'a P
  val indexname: indexname P
  val sort: sort T
  val typ_raw: typ T
  val term_raw: term T
  val typ: typ T
  val term: Consts.T -> term T
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

fun indexname (a, b) = if b = 0 then [a] else [a, int_atom b];

val sort = list string;

fun typ_raw T = T |> variant
 [fn Type (a, b) => ([a], list typ_raw b),
  fn TFree (a, b) => ([a], sort b),
  fn TVar (a, b) => (indexname a, sort b)];

fun term_raw t = t |> variant
 [fn Const (a, b) => ([a], typ_raw b),
  fn Free (a, b) => ([a], typ_raw b),
  fn Var (a, b) => (indexname a, typ_raw b),
  fn Bound a => ([int_atom a], []),
  fn Abs (a, b, c) => ([a], pair typ_raw term_raw (b, c)),
  fn op $ a => ([], pair term_raw term_raw a)];

fun typ T = option typ_raw (if T = dummyT then NONE else SOME T);

fun term consts t = t |> variant
 [fn Const (a, b) => ([a], list typ (Consts.typargs consts (a, b))),
  fn Free (a, b) => ([a], typ b),
  fn Var (a, b) => (indexname a, typ b),
  fn Bound a => ([int_atom a], []),
  fn Abs (a, b, c) => ([a], pair typ (term consts) (b, c)),
  fn op $ a => ([], pair (term consts) (term consts) a)];

end;

structure Decode =
struct

open XML.Decode;

fun indexname [a] = (a, 0)
  | indexname [a, b] = (a, int_atom b);

val sort = list string;

fun typ_raw body = body |> variant
 [fn ([a], b) => Type (a, list typ_raw b),
  fn ([a], b) => TFree (a, sort b),
  fn (a, b) => TVar (indexname a, sort b)];

fun term_raw body = body |> variant
 [fn ([a], b) => Const (a, typ_raw b),
  fn ([a], b) => Free (a, typ_raw b),
  fn (a, b) => Var (indexname a, typ_raw b),
  fn ([a], []) => Bound (int_atom a),
  fn ([a], b) => let val (c, d) = pair typ_raw term_raw b in Abs (a, c, d) end,
  fn ([], a) => op $ (pair term_raw term_raw a)];

val typ = option typ_raw #> the_default dummyT;

fun term consts body = body |> variant
 [fn ([a], b) => Const (a, Consts.instance consts (a, list typ b)),
  fn ([a], b) => Free (a, typ b),
  fn (a, b) => Var (indexname a, typ b),
  fn ([a], []) => Bound (int_atom a),
  fn ([a], b) => let val (c, d) = pair typ (term consts) b in Abs (a, c, d) end,
  fn ([], a) => op $ (pair (term consts) (term consts) a)];

end;

end;
