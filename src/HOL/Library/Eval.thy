(*  Title:      HOL/Library/Eval.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term evaluation mechanism *}

theory Eval
imports ATP_Linkup Code_Message
begin

subsection {* Type reflection *}

subsubsection {* Definition *}

types vname = message_string;
types "class" = message_string;
types sort = "class list"

datatype "typ" =
    Type message_string "typ list"
  | TFree vname sort  

abbreviation
  Fun :: "typ \<Rightarrow> typ \<Rightarrow> typ" where
  "Fun ty1 ty2 \<equiv> Type (STR ''fun'') [ty1, ty2]"

locale (open) pure_term_syntax = -- {* FIXME drop this *}
  fixes pure_term_Type :: "message_string \<Rightarrow> typ list \<Rightarrow> typ" (infixl "{\<struct>}" 120)
    and pure_term_TFree :: "vname \<Rightarrow> sort \<Rightarrow> typ" ("\<lbrace>_\<Colon>_\<rbrace>" [118, 118] 117)
    and pure_term_Fun :: "typ \<Rightarrow> typ \<Rightarrow> typ" (infixr "\<rightarrow>" 114)

parse_translation {*
let
  fun Type_tr [tyco, tys] = Lexicon.const @{const_syntax Type} $ tyco $ tys
    | Type_tr ts = raise TERM ("Type_tr", ts);
  fun TFree_tr [v, sort] = Lexicon.const @{const_syntax TFree} $ v $ sort
    | TFree_tr ts = raise TERM ("TFree_tr", ts);
  fun Fun_tr [ty1, ty2] = Lexicon.const @{const_syntax Fun} $ ty1 $ ty2
    | Fun_tr ts = raise TERM("Fun_tr", ts);
in [
  ("\\<^fixed>pure_term_Type", Type_tr),
  ("\\<^fixed>pure_term_TFree", TFree_tr),
  ("\\<^fixed>pure_term_Fun", Fun_tr)
] end
*}

notation (output)
  Type (infixl "{\<struct>}" 120)
and
  TFree ("\<lbrace>_\<Colon>_\<rbrace>" [118, 118] 117)
and
  Fun (infixr "\<rightarrow>" 114)

ML {*
structure Eval_Aux =
struct

val mk_sort = HOLogic.mk_list @{typ class} o map Message_String.mk;

fun mk_typ f (Type (tyco, tys)) =
      @{term Type} $ Message_String.mk tyco
        $ HOLogic.mk_list @{typ typ} (map (mk_typ f) tys)
  | mk_typ f (TFree v) =
      f v;

end;
*}


subsubsection {* Class @{text typ_of} *}

class typ_of =
  fixes typ_of :: "'a\<Colon>{} itself \<Rightarrow> typ"

ML {*
structure Eval_Aux =
struct

open Eval_Aux;

fun mk_typ_of ty =
  Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
    $ Logic.mk_type ty;

end
*}

setup {*
let
  open Eval_Aux;
  fun define_typ_of ty lthy =
    let
      val lhs = Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
        $ Free ("T", Term.itselfT ty);
      val rhs = mk_typ (fn v => mk_typ_of (TFree v)) ty;
      val eq = Syntax.check_term lthy (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))
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
  "typ_of (T\<Colon>prop itself) = Type (STR ''prop'') []"

instance ..

end

instantiation itself :: (typ_of) typ_of
begin

definition
  "typ_of (T\<Colon>'a itself itself) = Type (STR ''itself'') [typ_of TYPE('a\<Colon>typ_of)]"

instance ..

end

instantiation set :: (typ_of) typ_of
begin
 
definition
  "typ_of (T\<Colon>'a set itself) = Type (STR ''set'') [typ_of TYPE('a\<Colon>typ_of)]"

instance ..

end


subsubsection {* Code generator setup *}

lemma [code func]:
  includes pure_term_syntax
  shows "tyco1 {\<struct>} tys1 = tyco2 {\<struct>} tys2 \<longleftrightarrow> tyco1 = tyco2
     \<and> list_all2 (op =) tys1 tys2"
  by (auto simp add: list_all2_eq [symmetric])

code_type "typ"
  (SML "Term.typ")

code_const Type and TFree
  (SML "Term.Type/ (_, _)" and "Term.TFree/ (_, _)")

code_reserved SML Term



subsection {* Term representation *}

subsubsection {* Definition *}

datatype "term" =
    Const message_string "typ" (infix "\<Colon>\<subseteq>" 112)
  | Fix   vname "typ" (infix ":\<epsilon>" 112)
  | App   "term" "term" (infixl "\<bullet>" 110)
  | Abs   "vname \<times> typ" "term" (infixr "\<mapsto>" 111)
  | Bnd   nat

code_datatype Const App Fix

abbreviation
  Apps :: "term \<Rightarrow> term list \<Rightarrow> term" (infixl "{\<bullet>}" 110) where
  "t {\<bullet>} ts \<equiv> foldl (op \<bullet>) t ts"
abbreviation
  Abss :: "(vname \<times> typ) list \<Rightarrow> term \<Rightarrow> term" (infixr "{\<mapsto>}" 111) where
  "vs {\<mapsto>} t \<equiv> foldr (op \<mapsto>) vs t"

ML {*
structure Eval_Aux =
struct

open Eval_Aux;

fun mk_term f g (Const (c, ty)) =
      @{term Const} $ Message_String.mk c $ g ty
  | mk_term f g (t1 $ t2) =
      @{term App} $ mk_term f g t1 $ mk_term f g t2
  | mk_term f g (Free v) = f v;

end;
*}


subsubsection {* Class @{text term_of} *}

class term_of = typ_of +
  constrains typ_of :: "'a\<Colon>{} itself \<Rightarrow> typ"
  fixes term_of :: "'a \<Rightarrow> term"

ML {*
structure Eval_Aux =
struct

open Eval_Aux;

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
          val rhs : term = mk_term
            (fn (v, ty) => term_term_of ty $ Free (v, ty))
            (mk_typ (fn (v, sort) => mk_typ_of (TFree (v, sort)))) c
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
  open Eval_Aux;
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
      val defs = map (mk_terms_of_defs vs) css;
    in if forall (fn tyco => can (Sign.arity_sorts thy tyco) @{sort term_of}) dep_tycos
        andalso not (tycos = [@{type_name typ}])
      then SOME (sorts, defs)
      else NONE
    end;
  fun prep' ctxt proto_eqs =
    let
      val eqs as eq :: _ = map (Syntax.check_term ctxt) proto_eqs;
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

abbreviation (in pure_term_syntax) (input)
  intT :: "typ"
where
  "intT \<equiv> Type (STR ''IntDef.int'') []"

abbreviation (in pure_term_syntax) (input)
  bitT :: "typ"
where
  "bitT \<equiv> Type (STR ''Numeral.bit'') []"

function (in pure_term_syntax)
  mk_int :: "int \<Rightarrow> term"
where
  "mk_int k = (if k = 0 then STR ''Numeral.Pls'' \<Colon>\<subseteq> intT
    else if k = -1 then STR ''Numeral.Min'' \<Colon>\<subseteq> intT
    else let (l, m) = divAlg (k, 2)
  in STR ''Numeral.Bit'' \<Colon>\<subseteq> intT \<rightarrow> bitT \<rightarrow> intT \<bullet> mk_int l \<bullet>
    (if m = 0 then STR ''Numeral.bit.B0'' \<Colon>\<subseteq> bitT else STR ''Numeral.bit.B1'' \<Colon>\<subseteq> bitT))"
by pat_completeness auto
termination (in pure_term_syntax)
by (relation "measure (nat o abs)") (auto simp add: divAlg_mod_div)

declare pure_term_syntax.mk_int.simps [code func]

definition (in pure_term_syntax)
  "term_of_int_aux k = STR ''Numeral.number_class.number_of'' \<Colon>\<subseteq> intT \<rightarrow> intT \<bullet> mk_int k"

declare pure_term_syntax.term_of_int_aux_def [code func]

instantiation int :: term_of
begin

definition
  "term_of = pure_term_syntax.term_of_int_aux"

instance ..

end


subsubsection {* Code generator setup *}

lemmas [code func del] = term.recs term.cases term.size
lemmas [code func del] = term_of_message_string.simps
lemma [code func, code func del]: "(t1\<Colon>term) = t2 \<longleftrightarrow> t1 = t2" ..

code_type "term"
  (SML "Term.term")

code_const Const and App and Fix
  (SML "Term.Const/ (_, _)" and "Term.$/ (_, _)" and "Term.Free/ (_, _)")


subsection {* Evaluation setup *}

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
  Eval_Aux.mk_term_of
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
