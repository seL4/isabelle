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
    val pure_type: Pure_Term.T T
    val pure_term: {typed_vars: bool} -> Pure_Term.t T
    val pure_proof: {typed_vars: bool} -> Pure_Logic.proof T
  end
  structure Decode: TERM_XML_OPS
end;

structure Term_XML: TERM_XML =
struct

structure Encode =
struct

open Basic_Pure_Term Basic_Pure_Logic XML.Encode;

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

fun pure_type T = T |> variant
 [fn FUN args => (["fun"], pair pure_type pure_type args)
   | PROP => (["prop"], [])
   | CON0 a => ([a], [])
   | CON1 (a, b) => ([a], list pure_type [b])
   | CONN (a, b) => ([a], list pure_type b),
  fn TV ((a, ~1), b) => ([a], sort b),
  fn TV (a, b) => (indexname a, sort b)];

fun pure_var_type {typed_vars} T =
  if typed_vars andalso T <> Pure_Term.dummyT then pure_type T else [];

fun pure_term flag t = t |> variant
 [fn CONST0 a => ([a], [])
   | CONST1 (a, b) => ([a], list pure_type [b])
   | CONSTN (a, b) => ([a], list pure_type b),
  fn FV ((a, ~1), b) => ([a], pure_var_type flag b),
  fn FV (a, b) => (indexname a, pure_var_type flag b),
  fn BV a => ([], int a),
  fn ABS ((a, _), b, c) => ([a], pair pure_type (pure_term flag) (b, c)),
  fn APP a => ([], pair (pure_term flag) (pure_term flag) a),
  fn OFCLASS (a, b) => ([b], pure_type a)];

fun pure_proof flag prf = prf |> variant
 [fn Nop => ([], []),
  fn BVp a => ([], int a),
  fn Abst ((a, _), b, c) => ([a], pair pure_type (pure_proof flag) (b, c)),
  fn Absp ((a, _), b, c) => ([a], pair (pure_term flag) (pure_proof flag) (b, c)),
  fn Appt a => ([], pair (pure_proof flag) (pure_term flag) a),
  fn Appp a => ([], pair (pure_proof flag) (pure_proof flag) a),
  fn Hypp a => ([], pure_term flag a),
  fn Constp (c as ((Axiom a, b), _)) =>
    ([a], list (pure_type o #2) (Pure_Logic.proof_const_typargs c)),
  fn OFCLASSp (a, b) => ([b], pure_type a),
  fn Constp (c as ((Oracle a, b), _)) =>
    ([a], list (pure_type o #2) (Pure_Logic.proof_const_typargs c)),
  fn Constp (c as ((Thm {theory_name, thm_name = (name, _), serial}, b), _)) =>
    ([int_atom serial, theory_name, #1 name, int_atom (#2 name)],
      list (pure_type o #2) (Pure_Logic.proof_const_typargs c))];

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
