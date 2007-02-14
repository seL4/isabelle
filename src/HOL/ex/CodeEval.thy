(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple embedded term evaluation mechanism *}

theory CodeEval
imports CodeEmbed
begin

subsection {* The typ_of class *}

class typ_of =
  fixes typ_of :: "'a itself \<Rightarrow> typ"

ML {*
structure TypOf =
struct

local
  val thy = the_context ();
  val const_typ_of = Sign.intern_const thy "typ_of";
  fun term_typ_of ty = Const (const_typ_of, Term.itselfT ty --> Embed.typ_typ);
in
  val class_typ_of = Sign.intern_class thy "typ_of";
  fun term_typ_of_type ty =
    term_typ_of ty $ Logic.mk_type ty;
  fun mk_typ_of_def ty =
    let
      val lhs = term_typ_of ty $ Free ("x", Term.itselfT ty)
      val rhs = Embed.term_typ (fn v => term_typ_of_type (TFree v)) ty
    in Logic.mk_equals (lhs, rhs) end;
end;

end;
*}

setup {*
let
  fun mk arities _ thy =
    (maps (fn ((tyco, asorts), _) => [(("", []), TypOf.mk_typ_of_def
      (Type (tyco, map TFree (Name.names Name.context "'a" asorts))))]) arities, thy);
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
  val thy = the_context ();
  val const_term_of = Sign.intern_const thy "term_of";
  fun term_term_of ty = Const (const_term_of, ty --> Embed.typ_term);
in
  val class_term_of = Sign.intern_class thy "term_of";
  fun mk_terms_of_defs vs (tyco, cs) =
    let
      val dty = Type (tyco, map TFree vs);
      fun mk_eq c =
        let
          val lhs : term = term_term_of dty $ c;
          val rhs : term = Embed.term_term
            (fn (v, ty) => term_term_of ty $ Free (v, ty))
            (Embed.term_typ (fn (v, sort) => TypOf.term_typ_of_type (TFree (v, sort)))) c
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
      val vs = (Name.names Name.context "'a" o snd o fst o hd) arities;
      val defs = map (TermOf.mk_terms_of_defs vs) css;
      val defs' = (map (pair ("", []) o ObjectLogic.ensure_propT thy) o flat) defs;
    in
      thy
      |> PrimrecPackage.gen_primrec thy_note thy_def "" defs'
      |> snd
    end;
  fun hook specs =
    if (fst o hd) specs = (fst o dest_Type) Embed.typ_typ then I
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


subsection {* Small examples *}

ML {* Eval.term "(Suc 2 + 1) * 4" *}
ML {* Eval.term "(Suc 2 + Suc 0) * Suc 3" *}
ML {* Eval.term "[]::nat list" *}
ML {* Eval.term "fst ([]::nat list, Suc 0) = []" *}

text {* a fancy datatype *}

datatype ('a, 'b) bair =
    Bair "'a\<Colon>order" 'b
  | Shift "('a, 'b) cair"
  | Dummy unit
and ('a, 'b) cair =
    Cair 'a 'b

ML {* Eval.term "Shift (Cair (4::nat) [Suc 0])" *}

text {* also test evaluation oracle *}

lemma "True \<or> False" by eval
lemma "\<not> (Suc 0 = Suc 1)" by eval

end