(*  Title:      HOL/Library/Eval.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term evaluation mechanism *}

theory Eval
imports
  ATP_Linkup Code_Message
  Code_Index (* this theory is just imported for a term_of setup *)
begin

subsection {* Type reflection *}

subsubsection {* Definition *}

types vname = message_string;
types "class" = message_string;
types sort = "class list"

datatype "typ" =
    Type message_string "typ list"
  | TFree vname sort  

ML {*
structure Eval =
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
structure Eval =
struct

open Eval;

fun mk_typ_of ty =
  Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
    $ Logic.mk_type ty;

fun add_typ_of_def tyco thy =
  let
    val sorts = replicate (Sign.arity_number thy tyco) @{sort typ_of};
    val vs = Name.names Name.context "'a" sorts;
    val ty = Type (tyco, map TFree vs);
    val lhs = Const (@{const_name typ_of}, Term.itselfT ty --> @{typ typ})
      $ Free ("T", Term.itselfT ty);
    val rhs = mk_typ (fn v => mk_typ_of (TFree v)) ty;
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in
    thy
    |> TheoryTarget.instantiation ([tyco], vs, @{sort typ_of})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (("", []), eq)))
    |> snd
    |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
    |> LocalTheory.exit
    |> ProofContext.theory_of
  end;

end
*}

(*setup {*
let
  open Eval;
in
  Eval.add_typ_of_def @{type_name prop}
  #> Eval.add_typ_of_def @{type_name fun}
  #> Eval.add_typ_of_def @{type_name itself}
  #> Eval.add_typ_of_def @{type_name bool}
  #> Eval.add_typ_of_def @{type_name set}
  #> TypedefPackage.interpretation Eval.add_typ_of_def
end
*}*)

subsubsection {* Code generator setup *}

lemma [code func]:
  "Type tyco1 tys1 = Type tyco2 tys2 \<longleftrightarrow> tyco1 = tyco2
     \<and> list_all2 (op =) tys1 tys2"
  by (auto simp add: list_all2_eq [symmetric])

code_type "typ"
  (SML "Term.typ")

code_const Type and TFree
  (SML "Term.Type/ (_, _)" and "Term.TFree/ (_, _)")

code_reserved SML Term


subsection {* Term representation *}

subsubsection {* Definitions *}

datatype "term" = dummy_term

definition
  Const :: "message_string \<Rightarrow> typ \<Rightarrow> term"
where
  "Const _ _ = dummy_term"

definition
  App :: "term \<Rightarrow> term \<Rightarrow> term"
where
  "App _ _ = dummy_term"

code_datatype Const App

subsubsection {* Class @{term term_of} *}

class term_of = typ_of +
  constrains typ_of :: "'a\<Colon>{} itself \<Rightarrow> typ"
  fixes term_of :: "'a \<Rightarrow> term"

lemma term_of_anything: "term_of x \<equiv> t"
  by (rule eq_reflection) (cases "term_of x", cases t, simp)

ML {*
structure Eval =
struct

open Eval;

fun mk_term f g (Const (c, ty)) =
      @{term Const} $ Message_String.mk c $ g ty
  | mk_term f g (t1 $ t2) =
      @{term App} $ mk_term f g t1 $ mk_term f g t2
  | mk_term f g (Free v) = f v;

fun mk_term_of ty t = Const (@{const_name term_of}, ty --> @{typ term}) $ t;

end;
*}

setup {*
let
  fun has_no_inst tyco sort thy =
    not (can (Sorts.mg_domain (Sign.classes_of thy) tyco)
      sort);
  fun add_term_of_def ty vs tyco thy =
    let
      val lhs = Const (@{const_name term_of}, ty --> @{typ term})
        $ Free ("x", ty);
      val rhs = @{term "undefined \<Colon> term"};
      val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
    in
      thy
      |> TheoryTarget.instantiation ([tyco], vs, @{sort term_of})
      |> `(fn lthy => Syntax.check_term lthy eq)
      |-> (fn eq => Specification.definition (NONE, (("", []), eq)))
      |> snd
      |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
      |> LocalTheory.exit
      |> ProofContext.theory_of
    end;
  fun interpretator (tyco, (raw_vs, _)) thy =
    let
      val constrain_sort =
        curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort term_of};
      val vs = (map o apsnd) constrain_sort raw_vs;
      val ty = Type (tyco, map TFree vs);
    in
      thy
      |> `(has_no_inst tyco @{sort typ_of})
      |-> (fn no_typ_of => no_typ_of ? Eval.add_typ_of_def tyco)
      |> `(has_no_inst tyco @{sort term_of})
      |-> (fn no_term_of => no_term_of ? add_term_of_def ty vs tyco)
    end;
in
  Eval.add_typ_of_def @{type_name fun}
  #> Code.type_interpretation interpretator
end
*}

setup {*
let
  fun mk_term_of_eq ty vs tyco (c, tys) =
    let
      val t = list_comb (Const (c, tys ---> ty),
        map Free (Name.names Name.context "a" tys));
    in (map_aterms (fn Free (v, ty) => Var ((v, 0), ty) | t => t) t, Eval.mk_term
      (fn (v, ty) => Eval.mk_term_of ty (Var ((v, 0), ty)))
      (Eval.mk_typ (fn (v, sort) => Eval.mk_typ_of (TFree (v, sort)))) t)
    end;
  fun prove_term_of_eq ty eq thy =
    let
      val cty = Thm.ctyp_of thy ty;
      val (arg, rhs) = pairself (Thm.cterm_of thy) eq;
      val thm = @{thm term_of_anything}
        |> Drule.instantiate' [SOME cty] [SOME arg, SOME rhs]
        |> Thm.varifyT;
    in
      thy
      |> Code.add_func thm
    end;
  fun interpretator (tyco, (raw_vs, raw_cs)) thy =
    let
      val constrain_sort =
        curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort term_of};
      val vs = (map o apsnd) constrain_sort raw_vs;
      val cs = (map o apsnd o map o map_atyps)
        (fn TFree (v, sort) => TFree (v, constrain_sort sort)) raw_cs;
      val ty = Type (tyco, map TFree vs);
      val eqs = map (mk_term_of_eq ty vs tyco) cs;
      val const = AxClass.param_of_inst thy (@{const_name term_of}, tyco);
    in
      thy
      |> Code.del_funcs const
      |> fold (prove_term_of_eq ty) eqs
    end;
in
  Code.type_interpretation interpretator
end
*}

subsubsection {* Code generator setup *}

lemmas [code func del] = term.recs term.cases term.size
lemma [code func, code func del]: "(t1\<Colon>term) = t2 \<longleftrightarrow> t1 = t2" ..

lemma [code func, code func del]: "(term_of \<Colon> typ \<Rightarrow> term) = term_of" ..
lemma [code func, code func del]: "(term_of \<Colon> term \<Rightarrow> term) = term_of" ..
lemma [code func, code func del]: "(term_of \<Colon> index \<Rightarrow> term) = term_of" ..
lemma [code func, code func del]: "(term_of \<Colon> message_string \<Rightarrow> term) = term_of" ..

code_type "term"
  (SML "Term.term")

code_const Const and App
  (SML "Term.Const/ (_, _)" and "Term.$/ (_, _)")

code_const "term_of \<Colon> index \<Rightarrow> term"
  (SML "HOLogic.mk'_number/ HOLogic.indexT")

code_const "term_of \<Colon> message_string \<Rightarrow> term"
  (SML "Message'_String.mk")


subsection {* Evaluation setup *}

ML {*
signature EVAL =
sig
  val eval_ref: (unit -> term) option ref
  val eval_term: theory -> term -> term
  val evaluate: Proof.context -> term -> unit
  val evaluate': string -> Proof.context -> term -> unit
  val evaluate_cmd: string option -> string -> Toplevel.state -> unit
end;

structure Eval : EVAL =
struct

open Eval;

val eval_ref = ref (NONE : (unit -> term) option);

fun eval_term thy t =
  t 
  |> Eval.mk_term_of (fastype_of t)
  |> (fn t => CodePackage.eval_term ("Eval.eval_ref", eval_ref) thy t [])
  |> Code.postprocess_term thy;

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

print_translation {*
let
  val term = Const ("<TERM>", dummyT);
  fun tr1' [_, _] = term;
  fun tr2' [] = term;
in
  [(@{const_syntax Const}, tr1'),
    (@{const_syntax App}, tr1'),
    (@{const_syntax dummy_term}, tr2')]
end
*}

hide (open) const Type TFree typ_of term_of
hide const Const App dummy_term

end
