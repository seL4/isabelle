(*  Title:      HOL/Code_Eval.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Term evaluation using the generic code generator *}

theory Code_Eval
imports Plain Typerep
begin

subsection {* Term representation *}

subsubsection {* Terms and class @{text term_of} *}

datatype "term" = dummy_term

definition Const :: "message_string \<Rightarrow> typerep \<Rightarrow> term" where
  "Const _ _ = dummy_term"

definition App :: "term \<Rightarrow> term \<Rightarrow> term" where
  "App _ _ = dummy_term"

code_datatype Const App

class term_of = typerep +
  fixes term_of :: "'a \<Rightarrow> term"

lemma term_of_anything: "term_of x \<equiv> t"
  by (rule eq_reflection) (cases "term_of x", cases t, simp)

definition app :: "('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)
  \<Rightarrow> 'a \<times> (unit \<Rightarrow> term) \<Rightarrow> 'b \<times> (unit \<Rightarrow> term)" where
  "app f x = (fst f (fst x), \<lambda>u. Code_Eval.App (snd f ()) (snd x ()))"

lemma app_code [code, code inline]:
  "app (f, tf) (x, tx) = (f x, \<lambda>u. Code_Eval.App (tf ()) (tx ()))"
  by (simp only: app_def fst_conv snd_conv)


subsubsection {* @{text term_of} instances *}

setup {*
let
  fun add_term_of tyco raw_vs thy =
    let
      val vs = map (fn (v, _) => (v, @{sort typerep})) raw_vs;
      val ty = Type (tyco, map TFree vs);
      val lhs = Const (@{const_name term_of}, ty --> @{typ term})
        $ Free ("x", ty);
      val rhs = @{term "undefined \<Colon> term"};
      val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
      fun triv_name_of t = (fst o dest_Free o fst o strip_comb o fst
        o HOLogic.dest_eq o HOLogic.dest_Trueprop) t ^ "_triv";
    in
      thy
      |> TheoryTarget.instantiation ([tyco], vs, @{sort term_of})
      |> `(fn lthy => Syntax.check_term lthy eq)
      |-> (fn eq => Specification.definition (NONE, ((Binding.name (triv_name_of eq), []), eq)))
      |> snd
      |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
    end;
  fun ensure_term_of (tyco, (raw_vs, _)) thy =
    let
      val need_inst = not (can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of})
        andalso can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort typerep};
    in
      thy
      |> need_inst ? add_term_of tyco raw_vs
    end;
in
  Code.type_interpretation ensure_term_of
end
*}

setup {*
let
  fun mk_term_of_eq thy ty vs tyco (c, tys) =
    let
      val t = list_comb (Const (c, tys ---> ty),
        map Free (Name.names Name.context "a" tys));
      val (arg, rhs) = pairself (Thm.cterm_of thy o map_types Logic.unvarifyT o Logic.varify)
        (t, (map_aterms (fn t as Free (v, ty) => HOLogic.mk_term_of ty t | t => t) o HOLogic.reflect_term) t)
      val cty = Thm.ctyp_of thy ty;
    in
      @{thm term_of_anything}
      |> Drule.instantiate' [SOME cty] [SOME arg, SOME rhs]
      |> Thm.varifyT
    end;
  fun add_term_of_code tyco raw_vs raw_cs thy =
    let
      val vs = map (fn (v, _) => (v, @{sort typerep})) raw_vs;
      val ty = Type (tyco, map TFree vs);
      val cs = (map o apsnd o map o map_atyps)
        (fn TFree (v, _) => TFree (v, (the o AList.lookup (op =) vs) v)) raw_cs;
      val const = AxClass.param_of_inst thy (@{const_name term_of}, tyco);
      val eqs = map (mk_term_of_eq thy ty vs tyco) cs;
   in
      thy
      |> Code.del_eqns const
      |> fold Code.add_eqn eqs
    end;
  fun ensure_term_of_code (tyco, (raw_vs, cs)) thy =
    let
      val has_inst = can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of};
    in
      thy
      |> has_inst ? add_term_of_code tyco raw_vs cs
    end;
in
  Code.type_interpretation ensure_term_of_code
end
*}


subsubsection {* Code generator setup *}

lemmas [code del] = term.recs term.cases term.size
lemma [code, code del]: "eq_class.eq (t1\<Colon>term) t2 \<longleftrightarrow> eq_class.eq t1 t2" ..

lemma [code, code del]: "(term_of \<Colon> typerep \<Rightarrow> term) = term_of" ..
lemma [code, code del]: "(term_of \<Colon> term \<Rightarrow> term) = term_of" ..
lemma [code, code del]: "(term_of \<Colon> message_string \<Rightarrow> term) = term_of" ..
lemma [code, code del]:
  "(Code_Eval.term_of \<Colon> 'a::{type, term_of} Predicate.pred \<Rightarrow> Code_Eval.term) = Code_Eval.term_of" ..
lemma [code, code del]:
  "(Code_Eval.term_of \<Colon> 'a::{type, term_of} Predicate.seq \<Rightarrow> Code_Eval.term) = Code_Eval.term_of" ..

lemma term_of_char [unfolded typerep_fun_def typerep_char_def typerep_nibble_def, code]: "Code_Eval.term_of c =
    (let (n, m) = nibble_pair_of_char c
  in Code_Eval.App (Code_Eval.App (Code_Eval.Const (STR ''Pair'') (TYPEREP(nibble \<Rightarrow> nibble \<Rightarrow> char)))
    (Code_Eval.term_of n)) (Code_Eval.term_of m))"
  by (subst term_of_anything) rule 

code_type "term"
  (Eval "Term.term")

code_const Const and App
  (Eval "Term.Const/ (_, _)" and "Term.$/ (_, _)")

code_const "term_of \<Colon> message_string \<Rightarrow> term"
  (Eval "HOLogic.mk'_message'_string")

code_reserved Eval HOLogic


subsubsection {* Syntax *}

definition termify :: "'a \<Rightarrow> 'a \<times> (unit \<Rightarrow> term)" where
  [code del]: "termify x = (x, \<lambda>u. dummy_term)"

setup {*
let
  fun map_default f xs =
    let val ys = map f xs
    in if exists is_some ys
      then SOME (map2 the_default xs ys)
      else NONE
    end;
  fun subst_termify_app (Const (@{const_name termify}, T), [t]) =
        if not (Term.has_abs t)
        then if fold_aterms (fn Const _ => I | _ => K false) t true
          then SOME (HOLogic.mk_prod
            (t, Abs ("u", HOLogic.unitT, HOLogic.reflect_term t)))
          else error "Cannot termify expression containing variables"
        else error "Cannot termify expression containing abstraction"
    | subst_termify_app (t, ts) = case map_default subst_termify ts
       of SOME ts' => SOME (list_comb (t, ts'))
        | NONE => NONE
  and subst_termify (Abs (v, T, t)) = (case subst_termify t
       of SOME t' => SOME (Abs (v, T, t'))
        | NONE => NONE)
    | subst_termify t = subst_termify_app (strip_comb t) 
  fun check_termify ts ctxt = map_default subst_termify ts
    |> Option.map (rpair ctxt)
in
  Context.theory_map (Syntax.add_term_check 0 "termify" check_termify)
end;
*}

locale term_syntax
begin

notation app (infixl "<\<cdot>>" 70) and termify ("termify")

end

interpretation term_syntax .

no_notation app (infixl "<\<cdot>>" 70) and termify ("termify")

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

hide const dummy_term termify app
hide (open) const Const App term_of



subsection {* Evaluation setup *}

ML {*
signature EVAL =
sig
  val eval_ref: (unit -> term) option ref
  val eval_term: theory -> term -> term
end;

structure Eval : EVAL =
struct

val eval_ref = ref (NONE : (unit -> term) option);

fun eval_term thy t =
  Code_ML.eval NONE ("Eval.eval_ref", eval_ref) I thy (HOLogic.mk_term_of (fastype_of t) t) [];

end;
*}

setup {*
  Value.add_evaluator ("code", Eval.eval_term o ProofContext.theory_of)
*}

end
