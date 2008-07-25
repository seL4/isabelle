(*  Title:      HOL/Library/Eval.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term evaluation mechanism *}

theory Eval
imports
  Plain
  RType
  Code_Index (* this theory is just imported for a term_of setup *)
begin

subsection {* Term representation *}

subsubsection {* Terms and class @{text term_of} *}

datatype "term" = dummy_term

definition
  Const :: "message_string \<Rightarrow> rtype \<Rightarrow> term"
where
  "Const _ _ = dummy_term"

definition
  App :: "term \<Rightarrow> term \<Rightarrow> term"
where
  "App _ _ = dummy_term"

code_datatype Const App

class term_of = rtype +
  fixes term_of :: "'a \<Rightarrow> term"

lemma term_of_anything: "term_of x \<equiv> t"
  by (rule eq_reflection) (cases "term_of x", cases t, simp)

ML {*
structure Eval =
struct

fun mk_term f g (Const (c, ty)) =
      @{term Const} $ Message_String.mk c $ g ty
  | mk_term f g (t1 $ t2) =
      @{term App} $ mk_term f g t1 $ mk_term f g t2
  | mk_term f g (Free v) = f v
  | mk_term f g (Bound i) = Bound i
  | mk_term f g (Abs (v, _, t)) = Abs (v, @{typ term}, mk_term f g t);

fun mk_term_of ty t = Const (@{const_name term_of}, ty --> @{typ term}) $ t;

end;
*}


subsubsection {* @{text term_of} instances *}

setup {*
let
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
      val has_inst = can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of};
      val constrain_sort =
        curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort term_of};
      val vs = (map o apsnd) constrain_sort raw_vs;
      val ty = Type (tyco, map TFree vs);
    in
      thy
      |> RType.perhaps_add_def tyco
      |> not has_inst ? add_term_of_def ty vs tyco
    end;
in
  Code.type_interpretation interpretator
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
      (RType.mk (fn (v, sort) => RType.rtype (TFree (v, sort)))) t)
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

lemma [code func, code func del]: "(term_of \<Colon> rtype \<Rightarrow> term) = term_of" ..
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


subsubsection {* Syntax *}

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
setup {*
  Sign.declare_const [] ("rterm_of", @{typ "'a \<Rightarrow> 'b"}, NoSyn)
  #> snd
*}

notation (output)
  rterm_of ("\<guillemotleft>_\<guillemotright>")

locale rterm_syntax =
  fixes rterm_of_syntax :: "'a \<Rightarrow> 'b" ("\<guillemotleft>_\<guillemotright>")

parse_translation {*
let
  fun rterm_of_tr [t] = Lexicon.const @{const_name rterm_of} $ t
    | rterm_of_tr ts = raise TERM ("rterm_of_tr", ts);
in
  [(Syntax.fixedN ^ "rterm_of_syntax", rterm_of_tr)]
end
*}

setup {*
let
  val subst_rterm_of = Eval.mk_term
    (fn (v, _) => error ("illegal free variable in term quotation: " ^ quote v))
    (RType.mk (fn (v, sort) => RType.rtype (TFree (v, sort))));
  fun subst_rterm_of' (Const (@{const_name rterm_of}, _), [t]) = subst_rterm_of t
    | subst_rterm_of' (Const (@{const_name rterm_of}, _), _) =
        error ("illegal number of arguments for " ^ quote @{const_name rterm_of})
    | subst_rterm_of' (t, ts) = list_comb (t, map (subst_rterm_of' o strip_comb) ts);
  fun subst_rterm_of'' t = 
    let
      val t' = subst_rterm_of' (strip_comb t);
    in if t aconv t'
      then NONE
      else SOME t'
    end;
  fun check_rterm_of ts ctxt =
    let
      val ts' = map subst_rterm_of'' ts;
    in if exists is_some ts'
      then SOME (map2 the_default ts ts', ctxt)
      else NONE
    end;
in
  Context.theory_map (Syntax.add_term_check 0 "rterm_of" check_rterm_of)
end;
*}

hide const dummy_term
hide (open) const Const App
hide (open) const term_of


subsection {* Evaluation setup *}

ML {*
signature EVAL =
sig
  val mk_term: ((string * typ) -> term) -> (typ -> term) -> term -> term
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
  |> (fn t => CodeTarget.eval_term ("Eval.eval_ref", eval_ref) thy t [])
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

end
