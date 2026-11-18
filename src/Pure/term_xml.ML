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
  val typ: typ T
  val term_raw: term T
  val term: Consts.T -> term T
end

signature TERM_XML =
sig
  structure Encode:
  sig
    include TERM_XML_OPS
    val ztyp: ztyp T
    val zterm: {typed_vars: bool} -> zterm T
    val zproof: {typed_vars: bool} -> zproof T
  end
  structure Decode: TERM_XML_OPS
end;

structure Term_XML: TERM_XML =
struct

structure Encode =
struct

open XML.Encode;

fun indexname (a, b) = if b = 0 then [a] else [a, int_atom b];

val sort = list string;

fun typ T = T |> variant
 [fn Type (a, b) => ([a], list typ b),
  fn TFree (a, b) => ([a], sort b),
  fn TVar (a, b) => (indexname a, sort b)];

fun term_raw t = t |> variant
 [fn Const (a, b) => ([a], typ b),
  fn Free (a, b) => ([a], typ b),
  fn Var (a, b) => (indexname a, typ b),
  fn Bound a => ([], int a),
  fn Abs (a, b, c) => ([a], pair typ term_raw (b, c)),
  fn op $ a => ([], pair term_raw term_raw a)];

fun var_type T = if T = dummyT then [] else typ T;

fun term consts t = t |> variant
 [fn Const (a, b) => ([a], list typ (Consts.typargs consts (a, b))),
  fn Free (a, b) => ([a], var_type b),
  fn Var (a, b) => (indexname a, var_type b),
  fn Bound a => ([], int a),
  fn Abs (a, b, c) => ([a], pair typ (term consts) (b, c)),
  fn t as op $ a =>
    if can Logic.match_of_class t then raise Match
    else ([], pair (term consts) (term consts) a),
  fn t =>
    let val (T, c) = Logic.match_of_class t
    in ([c], typ T) end];

fun ztyp T = T |> variant
 [fn ZFun args => (["fun"], pair ztyp ztyp args)
   | ZProp => (["prop"], [])
   | ZType0 a => ([a], [])
   | ZType1 (a, b) => ([a], list ztyp [b])
   | ZType (a, b) => ([a], list ztyp b),
  fn ZTVar ((a, ~1), b) => ([a], sort b),
  fn ZTVar (a, b) => (indexname a, sort b)];

fun zvar_type {typed_vars} T =
  if typed_vars andalso T <> ZTerm.ztyp_dummy then ztyp T else [];

fun zterm flag t = t |> variant
 [fn ZConst0 a => ([a], [])
   | ZConst1 (a, b) => ([a], list ztyp [b])
   | ZConst (a, b) => ([a], list ztyp b),
  fn ZVar ((a, ~1), b) => ([a], zvar_type flag b),
  fn ZVar (a, b) => (indexname a, zvar_type flag b),
  fn ZBound a => ([], int a),
  fn ZAbs (a, b, c) => ([a], pair ztyp (zterm flag) (b, c)),
  fn ZApp a => ([], pair (zterm flag) (zterm flag) a),
  fn OFCLASS (a, b) => ([b], ztyp a)];

fun zproof flag prf = prf |> variant
 [fn ZNop => ([], []),
  fn ZBoundp a => ([], int a),
  fn ZAbst (a, b, c) => ([a], pair ztyp (zproof flag) (b, c)),
  fn ZAbsp (a, b, c) => ([a], pair (zterm flag) (zproof flag) (b, c)),
  fn ZAppt a => ([], pair (zproof flag) (zterm flag) a),
  fn ZAppp a => ([], pair (zproof flag) (zproof flag) a),
  fn ZHyp a => ([], zterm flag a),
  fn ZConstp (c as ((ZAxiom a, b), _)) => ([a], list (ztyp o #2) (ZTerm.zproof_const_typargs c)),
  fn OFCLASSp (a, b) => ([b], ztyp a),
  fn ZConstp (c as ((ZOracle a, b), _)) => ([a], list (ztyp o #2) (ZTerm.zproof_const_typargs c)),
  fn ZConstp (c as ((ZThm {theory_name, thm_name = (name, _), serial}, b), _)) =>
    ([int_atom serial, theory_name, #1 name, int_atom (#2 name)],
      list (ztyp o #2) (ZTerm.zproof_const_typargs c))];

end;

structure Decode =
struct

open XML.Decode;

fun indexname [a] = (a, 0)
  | indexname [a, b] = (a, int_atom b);

val sort = list string;

fun typ body = body |> variant
 [fn ([a], b) => Type (a, list typ b),
  fn ([a], b) => TFree (a, sort b),
  fn (a, b) => TVar (indexname a, sort b)];

fun term_raw body = body |> variant
 [fn ([a], b) => Const (a, typ b),
  fn ([a], b) => Free (a, typ b),
  fn (a, b) => Var (indexname a, typ b),
  fn ([], a) => Bound (int a),
  fn ([a], b) => let val (c, d) = pair typ term_raw b in Abs (a, c, d) end,
  fn ([], a) => op $ (pair term_raw term_raw a)];

fun var_type [] = dummyT
  | var_type body = typ body;

fun term consts body = body |> variant
 [fn ([a], b) => Const (a, Consts.instance consts (a, list typ b)),
  fn ([a], b) => Free (a, var_type b),
  fn (a, b) => Var (indexname a, var_type b),
  fn ([], a) => Bound (int a),
  fn ([a], b) => let val (c, d) = pair typ (term consts) b in Abs (a, c, d) end,
  fn ([], a) => op $ (pair (term consts) (term consts) a),
  fn ([a], b) => Logic.mk_of_class (typ b, a)];

end;

end;
