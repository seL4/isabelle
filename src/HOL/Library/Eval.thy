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


text {* Adaption for @{typ message_string}s *}

lemmas [code func, code func del] = term_of_message_string_def


subsection {* Evaluation infrastructure *}

ML {*
signature EVAL =
sig
  val eval_ref: (unit -> term) option ref
  val eval_term: theory -> term -> term
  val evaluate: Proof.context -> term -> unit
  val evaluate': string -> Proof.context -> term -> unit
  val evaluate_cmd: string option -> Toplevel.state -> unit
end;

structure Eval =
struct

val eval_ref = ref (NONE : (unit -> term) option);

fun eval_invoke thy code ((_, ty), t) deps _ =
  CodeTarget.eval_invoke thy ("Eval.eval_ref", eval_ref) code (t, ty) [];

fun eval_term thy =
  TermOf.mk_term_of
  #> CodePackage.eval_term thy (eval_invoke thy)
  #> Code.postprocess_term thy;

val evaluators = [
  ("code", eval_term),
  ("SML", Codegen.eval_term),
  ("normal_form", Nbe.norm_term)
];

fun gen_evaluate evaluators ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;
    val (evls, evl) = split_last evaluators;
    val t' = case get_first (fn f => try (f thy) t) evls
     of SOME t' => t'
      | NONE => evl thy t;
    val ty' = Term.type_of t';
    val p = Pretty.block [Pretty.quote (Syntax.pretty_term ctxt t'),
      Pretty.fbrk, Pretty.str "::", Pretty.brk 1,
      Pretty.quote (Syntax.pretty_typ ctxt ty')];
  in Pretty.writeln p end;

val evaluate = gen_evaluate (map snd evaluators);

fun evaluate' name = gen_evaluate
  [(the o AList.lookup (op =) evaluators) name];

fun evaluate_cmd some_name raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
  in case some_name
   of NONE => evaluate ctxt t
    | SOME name => evaluate' name ctxt t
  end;

end;
*}

ML {*
  OuterSyntax.improper_command "value" "read, evaluate and print term" OuterKeyword.diag
    (Scan.option (OuterParse.$$$ "(" |-- OuterParse.name --| OuterParse.$$$ ")")
    -- OuterParse.term
      >> (fn (some_name, t) => Toplevel.no_timing o Toplevel.keep
           (Eval.evaluate_cmd some_name t)));
*}

end
