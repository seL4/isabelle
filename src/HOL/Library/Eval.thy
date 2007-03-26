(*  Title:      HOL/Library/Eval.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term evaluation mechanism *}

theory Eval
imports Pure_term
begin

subsection {* The typ_of class *}

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


subsection {* term_of class *}

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

text {* Disable for characters and ml_strings *}

code_const "typ_of \<Colon> char itself \<Rightarrow> typ" and "term_of \<Colon> char \<Rightarrow> term"
  (SML "!((_); raise Fail \"typ'_of'_char\")"
    and "!((_); raise Fail \"term'_of'_char\")")
  (OCaml "!((_); failwith \"typ'_of'_char\")"
    and "!((_); failwith \"term'_of'_char\")")
  (Haskell "error/ \"typ'_of'_char\""
    and "error/ \"term'_of'_char\"")

code_const "term_of \<Colon> ml_string \<Rightarrow> term"
  (SML "!((_); raise Fail \"term'_of'_ml'_string\")")
  (OCaml "!((_); failwith \"term'_of'_ml'_string\")")

subsection {* Evaluation infrastructure *}

ML {*
signature EVAL =
sig
  val eval_term: theory -> term -> term
  val term: string -> unit
  val eval_ref: term option ref
end;

structure Eval : EVAL =
struct

val eval_ref = ref (NONE : term option);

fun eval_term thy t =
  CodegenPackage.eval_term
    thy (("Eval.eval_ref", eval_ref), TermOf.mk_term_of t);

fun term t =
  let
    val thy = the_context ();
    val t = eval_term thy (Sign.read_term thy t);
  in (writeln o Sign.string_of_term thy) t end;

end;
*}

end