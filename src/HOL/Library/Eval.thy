(*  Title:      HOL/Library/Eval.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term evaluation mechanism *}

theory Eval
imports Pure_term
begin

subsection {* @{text typ_of} class *}

class typ_of = type +
  fixes typ_of :: "'a itself \<Rightarrow> typ"

ML {*
structure TypOf =
struct

val class_typ_of = Sign.intern_class @{theory} "typ_of";

fun term_typ_of_type ty =
  Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
    $ Logic.mk_type ty;

fun mk_typ_of_def ty =
  let
    val lhs = Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
      $ Free ("x", Term.itselfT ty)
    val rhs = Pure_term.mk_typ (fn v => term_typ_of_type (TFree v)) ty
  in Logic.mk_equals (lhs, rhs) end;

end;
*}

setup {*
let
  fun mk arities _ thy =
    (maps (fn (tyco, asorts, _) => [(("", []), TypOf.mk_typ_of_def
      (Type (tyco,
        map TFree (Name.names Name.context "'a" asorts))))]) arities, thy);
  fun hook specs =
    DatatypeCodegen.prove_codetypes_arities (ClassPackage.intro_classes_tac [])
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [TypOf.class_typ_of] mk ((K o K) I)
in DatatypeCodegen.add_codetypes_hook_bootstrap hook end
*}


subsection {* @{text term_of} class *}

class term_of = typ_of +
  constrains typ_of :: "'a itself \<Rightarrow> typ"
  fixes term_of :: "'a \<Rightarrow> term"

ML {*
structure TermOf =
struct

local
  fun term_term_of ty =
    Const (@{const_name term_of}, ty --> @{typ term});
in
  val class_term_of = Sign.intern_class @{theory} "term_of";
  fun mk_terms_of_defs vs (tyco, cs) =
    let
      val dty = Type (tyco, map TFree vs);
      fun mk_eq c =
        let
          val lhs : term = term_term_of dty $ c;
          val rhs : term = Pure_term.mk_term
            (fn (v, ty) => term_term_of ty $ Free (v, ty))
            (Pure_term.mk_typ (fn (v, sort) => TypOf.term_typ_of_type (TFree (v, sort)))) c
        in
          HOLogic.mk_eq (lhs, rhs)
        end;
    in map mk_eq cs end;
  fun mk_term_of t =
    term_term_of (Term.fastype_of t) $ t;
end;

end;
*}

setup {*
let
  fun thy_note ((name, atts), thms) =
    PureThy.add_thmss [((name, thms), atts)] #-> (fn [thms] => pair (name, thms));
  fun thy_def ((name, atts), t) =
    PureThy.add_defs_i false [((name, t), atts)] #-> (fn [thm] => pair (name, thm));
  fun mk arities css thy =
    let
      val (_, asorts, _) :: _ = arities;
      val vs = Name.names Name.context "'a" asorts;
      val defs = map (TermOf.mk_terms_of_defs vs) css;
      val defs' = (map (pair ("", []) o ObjectLogic.ensure_propT thy) o flat) defs;
    in
      thy
      |> PrimrecPackage.gen_primrec thy_note thy_def "" defs'
      |> snd
    end;
  fun hook specs =
    if (fst o hd) specs = (fst o dest_Type) @{typ typ} then I
    else
      DatatypeCodegen.prove_codetypes_arities (ClassPackage.intro_classes_tac [])
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [TermOf.class_term_of] ((K o K o pair) []) mk
in DatatypeCodegen.add_codetypes_hook_bootstrap hook end
*}

text {* Adaption for @{typ ml_string}s *}

lemmas [code func, code nofunc] = term_of_ml_string_def


subsection {* Evaluation infrastructure *}

ML {*
signature EVAL =
sig
  val eval_ref: term option ref
  val eval_term: theory -> term -> term
  val print: (theory -> term -> term) -> string
    -> Toplevel.transition -> Toplevel.transition
end;

structure Eval : EVAL =
struct

val eval_ref = ref (NONE : term option);

fun eval_term thy t =
  CodegenPackage.eval_term
    thy (("Eval.eval_ref", eval_ref), TermOf.mk_term_of t);

fun print eval s = Toplevel.keep (fn state =>
  let
    val ctxt = Toplevel.context_of state;
    val thy = ProofContext.theory_of ctxt;
    val t = eval thy (ProofContext.read_term ctxt s);
    val T = Term.type_of t;
  in
    writeln (Pretty.string_of
      (Pretty.block [Pretty.quote (ProofContext.pretty_term ctxt t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (ProofContext.pretty_typ ctxt T)]))
  end);

end;
*}

ML {*
val valueP =
  OuterSyntax.improper_command "value" "read, evaluate and print term" OuterKeyword.diag
    ((OuterParse.opt_keyword "overloaded" -- OuterParse.term)
      >> (fn (b, t) => (Toplevel.no_timing o Eval.print
            (if b then Eval.eval_term else Codegen.eval_term) t)));

val _ = OuterSyntax.add_parsers [valueP];
*}

end
