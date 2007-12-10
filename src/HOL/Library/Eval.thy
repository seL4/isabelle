(*  Title:      HOL/Library/Eval.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term evaluation mechanism *}

theory Eval
imports PreList Pure_term
begin

subsection {* @{text typ_of} class *}

class typ_of =
  fixes typ_of :: "'a\<Colon>{} itself \<Rightarrow> typ"

ML {*
structure TypOf =
struct

fun mk ty =
  Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
    $ Logic.mk_type ty;

end
*}

setup {*
let
  fun define_typ_of ty lthy =
    let
      val lhs = Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
        $ Free ("T", Term.itselfT ty);
      val rhs = Pure_term.mk_typ (fn v => TypOf.mk (TFree v)) ty;
      val eq = Class.prep_spec lthy (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))
    in lthy |> Specification.definition (NONE, (("", []), eq)) end;
  fun interpretator tyco thy =
    let
      val sorts = replicate (Sign.arity_number thy tyco) @{sort typ_of};
      val ty = Type (tyco, map TFree (Name.names Name.context "'a" sorts));
    in
      thy
      |> TheoryTarget.instantiation ([tyco], sorts, @{sort typ_of})
      |> define_typ_of ty
      |> snd
      |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
      |> LocalTheory.exit
      |> ProofContext.theory_of
    end;
in TypedefPackage.interpretation interpretator end
*}

instantiation "prop" :: typ_of
begin

definition
  "typ_of (T\<Colon>prop itself) = STR ''prop'' {\<struct>} []"

instance ..

end

instantiation itself :: (typ_of) typ_of
begin

definition
  "typ_of (T\<Colon>'a itself itself) = STR ''itself'' {\<struct>} [typ_of TYPE('a\<Colon>typ_of)]"

instance ..

end

instantiation set :: (typ_of) typ_of
begin
 
definition
  "typ_of (T\<Colon>'a set itself) = STR ''set'' {\<struct>} [typ_of TYPE('a\<Colon>typ_of)]"

instance ..

end


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
            (Pure_term.mk_typ (fn (v, sort) => TypOf.mk (TFree (v, sort)))) c
        in
          HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
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
  fun prep_dtyp thy vs tyco =
    let
      val (_, cs) = DatatypePackage.the_datatype_spec thy tyco;
      val prep_typ = map_atyps (fn TFree (v, sort) =>
        TFree (v, (the o AList.lookup (op =) vs) v));
      fun prep_c (c, tys) = list_comb (Const (c, tys ---> Type (tyco, map TFree vs)),
        map Free (Name.names Name.context "a" tys));
    in (tyco, map (prep_c o (apsnd o map) prep_typ) cs) end;
  fun prep thy tycos =
    let
      val inter_sort = curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort term_of};
      val tyco = hd tycos;
      val (vs_proto, _) = DatatypePackage.the_datatype_spec thy tyco;
      val all_typs = maps (maps snd o snd o DatatypePackage.the_datatype_spec thy) tycos;
      fun add_tycos (Type (tyco, tys)) = insert (op =) tyco #>
            fold add_tycos tys
        | add_tycos _ = I;
      val dep_tycos = [] |> fold add_tycos all_typs |> subtract (op =) tycos;
      val sorts = map (inter_sort o snd) vs_proto;
      val vs = map fst vs_proto ~~ sorts;
      val css = map (prep_dtyp thy vs) tycos;
      val defs = map (TermOf.mk_terms_of_defs vs) css;
    in if forall (fn tyco => can (Sign.arity_sorts thy tyco) @{sort term_of}) dep_tycos
        andalso not (tycos = [@{type_name typ}])
      then SOME (sorts, defs)
      else NONE
    end;
  fun prep' ctxt proto_eqs =
    let
      val eqs as eq :: _ = map (Class.prep_spec ctxt) proto_eqs;
      val (Free (v, ty), _) =
        (strip_comb o fst o HOLogic.dest_eq o HOLogic.dest_Trueprop) eq;
    in ((v, SOME ty, NoSyn), map (pair ("", [])) eqs) end;
  fun primrec primrecs ctxt =
    let
      val (fixes, eqnss) = split_list (map (prep' ctxt) primrecs);
    in PrimrecPackage.add_primrec fixes (flat eqnss) ctxt end;
  fun interpretator tycos thy = case prep thy tycos
   of SOME (sorts, defs) =>
      thy
      |> TheoryTarget.instantiation (tycos, sorts, @{sort term_of})
      |> primrec defs
      |> snd
      |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
      |> LocalTheory.exit
      |> ProofContext.theory_of
    | NONE => thy;
  in DatatypePackage.interpretation interpretator end
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

instantiation int :: term_of
begin

definition
  "term_of k = STR ''Numeral.number_class.number_of'' \<Colon>\<subseteq> intT \<rightarrow> intT \<bullet> mk_int k"

instance ..

end


text {* Adaption for @{typ message_string}s *}

lemmas [code func del] = term_of_message_string.simps


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
