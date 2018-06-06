(* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset *)

section \<open>Lazy types in generated code\<close>

theory Code_Lazy
imports Main
keywords
  "code_lazy_type"
  "activate_lazy_type"
  "deactivate_lazy_type"
  "activate_lazy_types"
  "deactivate_lazy_types"
  "print_lazy_types" :: thy_decl
begin

text \<open>
  This theory and the CodeLazy tool described in @{cite "LochbihlerStoop2018"}.

  It hooks into Isabelle's code generator such that the generated code evaluates a user-specified
  set of type constructors lazily, even in target languages with eager evaluation.
  The lazy type must be algebraic, i.e., values must be built from constructors and a
  corresponding case operator decomposes them. Every datatype and codatatype is algebraic
  and thus eligible for lazification.
\<close>

subsection \<open>Eliminating pattern matches\<close>

definition missing_pattern_match :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a" where
  [code del]: "missing_pattern_match m f = f ()"

lemma missing_pattern_match_cong [cong]:
  "m = m' \<Longrightarrow> missing_pattern_match m f = missing_pattern_match m' f"
  by(rule arg_cong)

lemma missing_pattern_match_code [code_unfold]:
  "missing_pattern_match = Code.abort"
  unfolding missing_pattern_match_def Code.abort_def ..

ML_file "case_converter.ML"

subsection \<open>The type @{text lazy}\<close>

typedef 'a lazy = "UNIV :: 'a set" ..
setup_lifting type_definition_lazy
lift_definition delay :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a lazy"  is "\<lambda>f. f ()" .
lift_definition force :: "'a lazy \<Rightarrow> 'a" is "\<lambda>x. x" .

code_datatype delay
lemma force_delay [code]: "force (delay f) = f ()" by transfer(rule refl)
lemma delay_force: "delay (\<lambda>_. force s) = s" by transfer(rule refl)

text \<open>The implementations of @{typ "_ lazy"} using language primitives cache forced values.\<close>

code_printing code_module Lazy \<rightharpoonup> (SML)
\<open>signature LAZY =
sig
  type 'a lazy;
  val lazy : (unit -> 'a) -> 'a lazy;
  val force : 'a lazy -> 'a;
  val peek : 'a lazy -> 'a option
  val termify_lazy : 
   (string -> 'typerep -> 'term) -> 
   ('term -> 'term -> 'term) -> 
   (string -> 'typerep -> 'term -> 'term) ->
   'typerep -> ('typerep -> 'typerep -> 'typerep) -> ('typerep -> 'typerep) ->
   ('a -> 'term) -> 'typerep -> 'a lazy -> 'term -> 'term;
end;

structure Lazy : LAZY = 
struct

datatype 'a content =
   Delay of unit -> 'a
 | Value of 'a 
 | Exn of exn;

datatype 'a lazy = Lazy of 'a content ref;

fun lazy f = Lazy (ref (Delay f));

fun force (Lazy x) = case !x of
   Delay f => (
     let val res = f (); val _ = x := Value res; in res end
     handle exn => (x := Exn exn; raise exn))
  | Value x => x
  | Exn exn => raise exn;

fun peek (Lazy x) = case !x of
    Value x => SOME x
  | _ => NONE;

fun termify_lazy const app abs unitT funT lazyT term_of T x _ =
  app (const "Code_Lazy.delay" (funT (funT unitT T) (lazyT T))) 
    (case peek x of SOME y => abs "_" unitT (term_of y)
     | _ => const "Pure.dummy_pattern" (funT unitT T));

end;\<close>
code_reserved SML Lazy

code_printing
  type_constructor lazy \<rightharpoonup> (SML) "_ Lazy.lazy"
| constant delay \<rightharpoonup> (SML) "Lazy.lazy"
| constant force \<rightharpoonup> (SML) "Lazy.force"

code_printing \<comment> \<open>For code generation within the Isabelle environment, we reuse the thread-safe
  implementation of lazy from @{file "~~/src/Pure/Concurrent/lazy.ML"}\<close>
  code_module Lazy \<rightharpoonup> (Eval) \<open>\<close>
| type_constructor lazy \<rightharpoonup> (Eval) "_ Lazy.lazy"
| constant delay \<rightharpoonup> (Eval) "Lazy.lazy"
| constant force \<rightharpoonup> (Eval) "Lazy.force"

code_printing
  code_module Lazy \<rightharpoonup> (Haskell) 
\<open>newtype Lazy a = Lazy a;
delay f = Lazy (f ());
force (Lazy x) = x;\<close>
| type_constructor lazy \<rightharpoonup> (Haskell) "Lazy.Lazy _"
| constant delay \<rightharpoonup> (Haskell) "Lazy.delay"
| constant force \<rightharpoonup> (Haskell) "Lazy.force"
code_reserved Haskell Lazy

code_printing
  code_module Lazy \<rightharpoonup> (Scala) 
\<open>object Lazy {
  final class Lazy[A] (f: Unit => A) {
    var evaluated = false;
    lazy val x: A = f ()

    def get() : A = {
      evaluated = true;
      return x
    }
  }

  def force[A] (x: Lazy[A]) : A = {
    return x.get()
  }

  def delay[A] (f: Unit => A) : Lazy[A] = {
    return new Lazy[A] (f)
  }

  def termify_lazy[Typerep, Term, A] (
    const: String => Typerep => Term,
    app: Term => Term => Term,
    abs: String => Typerep => Term => Term,
    unitT: Typerep,
    funT: Typerep => Typerep => Typerep,
    lazyT: Typerep => Typerep,
    term_of: A => Term,
    ty: Typerep,
    x: Lazy[A],
    dummy: Term) : Term = {
    if (x.evaluated)
      app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(abs("_")(unitT)(term_of(x.get)))
    else
      app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(const("Pure.dummy_pattern")(funT(unitT)(ty)))
  }
}\<close>
| type_constructor lazy \<rightharpoonup> (Scala) "Lazy.Lazy[_]"
| constant delay \<rightharpoonup> (Scala) "Lazy.delay"
| constant force \<rightharpoonup> (Scala) "Lazy.force"
code_reserved Scala Lazy termify_lazy

code_printing
  type_constructor lazy \<rightharpoonup> (OCaml) "_ Lazy.t"
| constant delay \<rightharpoonup> (OCaml) "Lazy.from'_fun"
| constant force \<rightharpoonup> (OCaml) "Lazy.force"
code_reserved OCaml Lazy

text \<open>
  Term reconstruction for lazy looks into the lazy value and reconstructs it to the depth it has been evaluated.
  This is not done for Haskell and Scala as we do not know of any portable way to inspect whether a lazy value
  has been evaluated to or not.
\<close>
code_printing code_module Termify_Lazy \<rightharpoonup> (Eval) 
\<open>structure Termify_Lazy = struct
fun termify_lazy 
  (_: string -> typ -> term) (_: term -> term -> term)  (_: string -> typ -> term -> term)
  (_: typ) (_: typ -> typ -> typ) (_: typ -> typ)
  (term_of: 'a -> term) (T: typ) (x: 'a Lazy.lazy) (_: term) =
  Const ("Code_Lazy.delay", (HOLogic.unitT --> T) --> Type ("Code_Lazy.lazy", [T])) $ 
  (case Lazy.peek x of
    SOME (Exn.Res x) => absdummy HOLogic.unitT (term_of x)
  | _ => Const ("Pure.dummy_pattern", HOLogic.unitT --> T));
end;\<close>
code_reserved Eval Termify_Lazy TERMIFY_LAZY termify_lazy

code_printing code_module Termify_Lazy \<rightharpoonup> (OCaml) 
\<open>module Termify_Lazy : sig
  val termify_lazy :
   (string -> 'typerep -> 'term) -> 
   ('term -> 'term -> 'term) -> 
   (string -> 'typerep -> 'term -> 'term) ->
   'typerep -> ('typerep -> 'typerep -> 'typerep) -> ('typerep -> 'typerep) ->
   ('a -> 'term) -> 'typerep -> 'a Lazy.t -> 'term -> 'term
end = struct

let termify_lazy const app abs unitT funT lazyT term_of ty x _ =
  app (const "Code_Lazy.delay" (funT (funT unitT ty) (lazyT ty))) 
    (if Lazy.is_val x then abs "_" unitT (term_of (Lazy.force x))
     else const "Pure.dummy_pattern" (funT unitT ty));;

end;;\<close>
code_reserved OCaml Termify_Lazy termify_lazy

definition termify_lazy2 :: "'a :: typerep lazy \<Rightarrow> term"
where "termify_lazy2 x =
  Code_Evaluation.App (Code_Evaluation.Const (STR ''Code_Lazy.delay'') (TYPEREP((unit \<Rightarrow> 'a) \<Rightarrow> 'a lazy)))
    (Code_Evaluation.Const (STR ''Pure.dummy_pattern'') (TYPEREP((unit \<Rightarrow> 'a))))"

definition termify_lazy :: 
  "(String.literal \<Rightarrow> 'typerep \<Rightarrow> 'term) \<Rightarrow> 
   ('term \<Rightarrow> 'term \<Rightarrow> 'term) \<Rightarrow> 
   (String.literal \<Rightarrow> 'typerep \<Rightarrow> 'term \<Rightarrow> 'term) \<Rightarrow>
   'typerep \<Rightarrow> ('typerep \<Rightarrow> 'typerep \<Rightarrow> 'typerep) \<Rightarrow> ('typerep \<Rightarrow> 'typerep) \<Rightarrow>
   ('a \<Rightarrow> 'term) \<Rightarrow> 'typerep \<Rightarrow> 'a :: typerep lazy \<Rightarrow> 'term \<Rightarrow> term"
where "termify_lazy _ _ _ _ _ _ _ _ x _ = termify_lazy2 x"

declare [[code drop: "Code_Evaluation.term_of :: _ lazy \<Rightarrow> _"]]

lemma term_of_lazy_code [code]:
  "Code_Evaluation.term_of x \<equiv> 
   termify_lazy 
     Code_Evaluation.Const Code_Evaluation.App Code_Evaluation.Abs 
     TYPEREP(unit) (\<lambda>T U. typerep.Typerep (STR ''fun'') [T, U]) (\<lambda>T. typerep.Typerep (STR ''Code_Lazy.lazy'') [T])
     Code_Evaluation.term_of TYPEREP('a) x (Code_Evaluation.Const (STR '''') (TYPEREP(unit)))"
  for x :: "'a :: {typerep, term_of} lazy"
by(rule term_of_anything)

code_printing constant termify_lazy
  \<rightharpoonup> (SML) "Lazy.termify'_lazy" 
  and (Eval) "Termify'_Lazy.termify'_lazy"
  and (OCaml) "Termify'_Lazy.termify'_lazy"
  and (Scala) "Lazy.termify'_lazy"
  
text \<open>Make evaluation with the simplifier respect @{term delay}s.\<close>

lemma delay_lazy_cong: "delay f = delay f" by simp
setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm delay_lazy_cong})\<close>        

subsection \<open>Implementation\<close>

ML_file "code_lazy.ML"

setup \<open>
  Code_Preproc.add_functrans ("lazy_datatype", Code_Lazy.transform_code_eqs);
\<close>

end
