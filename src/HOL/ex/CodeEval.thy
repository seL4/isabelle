(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple embedded term evaluation mechanism *}

theory CodeEval
imports CodeEmbed
begin

section {* A simple embedded term evaluation mechanism *}

subsection {* The typ_of class *}

class typ_of =
  fixes typ_of :: "'a option \<Rightarrow> typ"

ML {*
structure TypOf =
struct

local
  val thy = the_context ();
  val const_typ_of = Sign.intern_const thy "typ_of";
  val const_None = Sign.intern_const thy "None";
  fun typ_option ty = Type (Sign.intern_type (the_context ()) "option", [ty]);
  fun term_typ_of ty = Const (const_typ_of, typ_option ty --> Embed.typ_typ);
in
  val class_typ_of = Sign.intern_class thy "typ_of";
  fun term_typ_of_None ty =
    term_typ_of ty $ Const (const_None, typ_option ty);
  fun mk_typ_of_def ty =
    let
      val lhs = term_typ_of ty $ Free ("x", typ_option ty)
      val rhs = Embed.term_typ (fn v => term_typ_of_None (TFree v)) ty
    in Logic.mk_equals (lhs, rhs) end;
end;

end;
*}

setup {*
let
  fun mk _ arities _ =
    maps (fn ((tyco, asorts), _) => [(("", []), TypOf.mk_typ_of_def
      (Type (tyco, map TFree (Name.names Name.context "'a" asorts))))]) arities;
  fun tac _ = ClassPackage.intro_classes_tac [];
  fun hook specs =
    DatatypeCodegen.prove_codetypes_arities tac
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [TypOf.class_typ_of] mk
in DatatypeCodegen.add_codetypes_hook_bootstrap hook end
*}


subsection {* term_of class *}

class term_of = typ_of +
  constrains typ_of :: "'a option \<Rightarrow> typ"
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
            (Embed.term_typ (fn (v, sort) => TypOf.term_typ_of_None (TFree (v, sort)))) c
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
  fun mk thy arities css =
    let
      val vs = (Name.names Name.context "'a" o snd o fst o hd) arities;
      val raw_defs = map (TermOf.mk_terms_of_defs vs) css;
      fun mk' thy' = map (apfst (rpair [])) ((PrimrecPackage.mk_combdefs thy' o flat) raw_defs)
    in ClassPackage.assume_arities_thy thy arities mk' end;
  fun tac _ = ClassPackage.intro_classes_tac [];
  fun hook specs =
    if (fst o hd) specs = (fst o dest_Type) Embed.typ_typ then I
    else
      DatatypeCodegen.prove_codetypes_arities tac
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [TermOf.class_term_of] mk
in DatatypeCodegen.add_codetypes_hook_bootstrap hook end
*}


subsection {* Evaluation infrastructure *}

lemma lift_eq_Trueprop:
  "p == q \<Longrightarrow> Trueprop p == Trueprop q" by auto

ML {*
signature EVAL =
sig
  val eval_term: term -> theory -> term * theory
  val eval_term' : theory -> term -> term
  val term: string -> unit
  val eval_ref: term ref
  val oracle: string * (theory * exn -> term)
  val method: Method.src -> Proof.context -> Method.method
end;

structure Eval : EVAL =
struct

val eval_ref = ref Logic.protectC;

fun eval_term t =
  CodegenPackage.eval_term
    (("Eval.eval_ref", eval_ref), TermOf.mk_term_of t);

fun eval_term' thy t =
  let
    val thy' = Theory.copy thy;
    val (t', _) = eval_term t thy';
  in t' end;

fun term t =
  let
    val thy = the_context ();
    val t' = eval_term' thy (Sign.read_term thy t);
  in () end;

val lift_eq_Trueprop = thm "lift_eq_Trueprop";

exception Eval of term;

val oracle = ("Eval", fn (thy, Eval t) =>
  Logic.mk_equals (t, eval_term' thy t));

val oracle_name = NameSpace.pack [Context.theory_name (the_context ()), fst oracle];

fun conv ct =
  let
    val {thy, t, ...} = rep_cterm ct;
    val t' = HOLogic.dest_Trueprop t;
    val thm' = Thm.invoke_oracle_i thy oracle_name (thy, Eval t');
  in
    lift_eq_Trueprop OF [thm']
  end;

fun tac i = Tactical.PRIMITIVE (Drule.fconv_rule
  (Drule.goals_conv (equal i) conv));

val method =
  Method.no_args (Method.METHOD (fn _ =>
    tac 1 THEN rtac TrueI 1));

end;
*}

setup {*
  Theory.add_oracle Eval.oracle
  #> Method.add_method ("eval", Eval.method, "solve goal by evaluation")
*}


subsection {* Small examples *}

ML {* Eval.term "[]::nat list" *}
ML {* Eval.term "(Suc 2 + Suc 0) * Suc 3" *}
ML {* Eval.term "fst ([]::nat list, Suc 0) = []" *}

text {* a fancy datatype *}

datatype ('a, 'b) bair =
    Bair "'a\<Colon>order" 'b
  | Shift "('a, 'b) cair"
  | Dummy unit
and ('a, 'b) cair =
    Cair 'a 'b

code_gen term_of

ML {* Eval.term "Shift (Cair (4::nat) [Suc 0])" *}

lemma
  "Suc 0 = 1" by eval

lemma
  "rev [0, Suc 0, Suc 0] = [Suc 0, Suc 0, 0]" by eval

lemma
  "fst (snd (fst ( ((Some (2::nat), (Suc 0, ())), [0::nat]) ))) = Suc (Suc 0) - 1" by eval

end
