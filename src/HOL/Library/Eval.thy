(*  Title:      HOL/Library/Eval.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term evaluation mechanism *}

theory Eval
imports Main Pure_term
begin

subsection {* @{text typ_of} class *}

class typ_of =
  fixes typ_of :: "'a\<Colon>{} itself \<Rightarrow> typ"

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

instance "prop" :: typ_of
  "typ_of T \<equiv> STR ''prop'' {\<struct>} []" ..

instance itself :: (typ_of) typ_of
  "typ_of T \<equiv> STR ''itself'' {\<struct>} [typ_of TYPE('a\<Colon>typ_of)]" ..

instance set :: (typ_of) typ_of
  "typ_of T \<equiv> STR ''set'' {\<struct>} [typ_of TYPE('a\<Colon>typ_of)]" ..

instance int :: typ_of
  "typ_of T \<equiv> STR ''IntDef.int'' {\<struct>} []" ..

setup {*
let
  fun mk arities _ thy =
    (maps (fn (tyco, asorts, _) => [(("", []), TypOf.mk_typ_of_def
      (Type (tyco,
        map TFree (Name.names Name.context "'a" asorts))))]) arities, thy);
  fun hook specs =
    DatatypeCodegen.prove_codetypes_arities (Class.intro_classes_tac [])
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [TypOf.class_typ_of] mk ((K o K) (fold Code.add_default_func))
in DatatypeCodegen.add_codetypes_hook hook end
*}


subsection {* @{text term_of} class *}

class term_of = typ_of +
  constrains typ_of :: "'a\<Colon>{} itself \<Rightarrow> typ"
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
  fun mk arities css _ thy =
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
    if null specs orelse (fst o hd) specs = (fst o dest_Type) @{typ typ} then I
    else
      DatatypeCodegen.prove_codetypes_arities (Class.intro_classes_tac [])
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [TermOf.class_term_of] ((K o K o pair) []) mk
in DatatypeCodegen.add_codetypes_hook hook end
*}

abbreviation
  intT :: "typ"
where
  "intT \<equiv> STR ''IntDef.int'' {\<struct>} []"

abbreviation
  bitT :: "typ"
where
  "bitT \<equiv> STR ''Numeral.bit'' {\<struct>} []"

function
  mk_int :: "int \<Rightarrow> term"
where
  "mk_int k = (if k = 0 then STR ''Numeral.Pls'' \<Colon>\<subseteq> intT
    else if k = -1 then STR ''Numeral.Min'' \<Colon>\<subseteq> intT
    else let (l, m) = divAlg (k, 2)
  in STR ''Numeral.Bit'' \<Colon>\<subseteq> intT \<rightarrow> bitT \<rightarrow> intT \<bullet> mk_int l \<bullet>
    (if m = 0 then STR ''Numeral.bit.B0'' \<Colon>\<subseteq> bitT else STR ''Numeral.bit.B1'' \<Colon>\<subseteq> bitT))"
by pat_completeness auto
termination by (relation "measure (nat o abs)") (auto simp add: divAlg_mod_div)

instance int :: term_of
  "term_of k \<equiv> STR ''Numeral.number_class.number_of'' \<Colon>\<subseteq> intT \<rightarrow> intT \<bullet> mk_int k" ..


text {* Adaption for @{typ ml_string}s *}

lemmas [code func, code func del] = term_of_ml_string_def


subsection {* Evaluation infrastructure *}

ML {*
signature EVAL =
sig
  val eval_ref: (unit -> term) option ref
  val eval_conv: cterm -> thm
  val eval_print: (cterm -> thm) -> Proof.context -> term -> unit
  val eval_print_cmd: (cterm -> thm) -> string -> Toplevel.state -> unit
end;

structure Eval =
struct

val eval_ref = ref (NONE : (unit -> term) option);

end;
*}

oracle eval_oracle ("term * CodeThingol.code * (CodeThingol.typscheme * CodeThingol.iterm) * cterm") =
{* fn thy => fn (t0, code, ((vs, ty), t), ct) => 
let
  val _ = (Term.map_types o Term.map_atyps) (fn _ =>
    error ("Term " ^ Sign.string_of_term thy t0 ^ " contains polymorphic type"))
    t0;
in
  Logic.mk_equals (t0,
    CodePackage.eval_invoke thy ("Eval.eval_ref", Eval.eval_ref) code (t, ty) [])
end;
*}

ML {*
structure Eval : EVAL =
struct

open Eval;

fun eval_invoke thy t0 code vs_ty_t _ ct = eval_oracle thy (t0, code, vs_ty_t, ct);

fun eval_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    val ct' = (Thm.cterm_of thy o TermOf.mk_term_of o Thm.term_of) ct;
  in
    CodePackage.eval_term thy
      (eval_invoke thy (Thm.term_of ct)) ct'
  end;

fun eval_print conv ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;
    val ct = Thm.cterm_of thy t;
    val (_, t') = (Logic.dest_equals o Thm.prop_of o conv) ct;
    val ty = Term.type_of t';
    val p = 
      Pretty.block [Pretty.quote (ProofContext.pretty_term ctxt t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (ProofContext.pretty_typ ctxt ty)];
  in Pretty.writeln p end;

fun eval_print_cmd conv raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val thy = ProofContext.theory_of ctxt;
    val ct = Thm.cterm_of thy t;
    val (_, t') = (Logic.dest_equals o Thm.prop_of o conv) ct;
    val ty = Term.type_of t';
    val p = 
      Pretty.block [Pretty.quote (ProofContext.pretty_term ctxt t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (ProofContext.pretty_typ ctxt ty)];
  in Pretty.writeln p end;

end;
*}

ML {*
val valueP =
  OuterSyntax.improper_command "value" "read, evaluate and print term" OuterKeyword.diag
    (OuterParse.term
      >> (fn t => Toplevel.no_timing o Toplevel.keep
           (Eval.eval_print_cmd (fn ct => case try Eval.eval_conv ct
     of SOME thm => thm
      | NONE => Codegen.evaluation_conv ct) t)));

val _ = OuterSyntax.add_parsers [valueP];
*}

end
