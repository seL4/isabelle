(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Setup of code generator tools *}

theory Code_Generator
imports HOL
begin

subsection {* ML code generator *}

types_code
  "bool"  ("bool")
attach (term_of) {*
fun term_of_bool b = if b then HOLogic.true_const else HOLogic.false_const;
*}
attach (test) {*
fun gen_bool i = one_of [false, true];
*}
  "prop"  ("bool")
attach (term_of) {*
fun term_of_prop b =
  HOLogic.mk_Trueprop (if b then HOLogic.true_const else HOLogic.false_const);
*}

consts_code
  "Trueprop" ("(_)")
  "True"    ("true")
  "False"   ("false")
  "Not"     ("not")
  "op |"    ("(_ orelse/ _)")
  "op &"    ("(_ andalso/ _)")
  "HOL.If"      ("(if _/ then _/ else _)")

setup {*
let

fun eq_codegen thy defs gr dep thyname b t =
    (case strip_comb t of
       (Const ("op =", Type (_, [Type ("fun", _), _])), _) => NONE
     | (Const ("op =", _), [t, u]) =>
          let
            val (gr', pt) = Codegen.invoke_codegen thy defs dep thyname false (gr, t);
            val (gr'', pu) = Codegen.invoke_codegen thy defs dep thyname false (gr', u);
            val (gr''', _) = Codegen.invoke_tycodegen thy defs dep thyname false (gr'', HOLogic.boolT)
          in
            SOME (gr''', Codegen.parens
              (Pretty.block [pt, Pretty.str " =", Pretty.brk 1, pu]))
          end
     | (t as Const ("op =", _), ts) => SOME (Codegen.invoke_codegen
         thy defs dep thyname b (gr, Codegen.eta_expand t ts 2))
     | _ => NONE);

in

Codegen.add_codegen "eq_codegen" eq_codegen

end
*}

text {* Evaluation *}

setup {*
let

val TrueI = thm "TrueI"
fun evaluation_tac i = Tactical.PRIMITIVE (Drule.fconv_rule
  (Drule.goals_conv (equal i) Codegen.evaluation_conv));
val evaluation_meth =
  Method.no_args (Method.SIMPLE_METHOD' (evaluation_tac THEN' rtac TrueI));

in

Method.add_method ("evaluation", evaluation_meth, "solve goal by evaluation")

end;
*}


subsection {* Generic code generator setup *}

text {* operational equality for code generation *}

axclass eq \<subseteq> type
  (attach "op =")


text {* equality for Haskell *}

code_class eq
  (Haskell "Eq" where "op =" \<equiv> "(==)")

code_const "op ="
  (Haskell infixl 4 "==")


text {* boolean expressions *}

lemma [code func]:
  shows "(False \<and> x) = False"
    and "(True \<and> x) = x"
    and "(x \<and> False) = False"
    and "(x \<and> True) = x" by simp_all

lemma [code func]:
  shows "(False \<or> x) = x"
    and "(True \<or> x) = True"
    and "(x \<or> False) = x"
    and "(x \<or> True) = True" by simp_all

lemma [code func]:
  shows "(\<not> True) = False"
    and "(\<not> False) = True" by (rule HOL.simp_thms)+

lemmas [code func] = imp_conv_disj

lemmas [code func] = if_True if_False

instance bool :: eq ..

lemma [code func]:
  "True = P \<longleftrightarrow> P" by simp

lemma [code func]:
  "False = P \<longleftrightarrow> \<not> P" by simp

lemma [code func]:
  "P = True \<longleftrightarrow> P" by simp

lemma [code func]:
  "P = False \<longleftrightarrow> \<not> P" by simp

code_type bool
  (SML "bool")
  (OCaml "bool")
  (Haskell "Bool")

code_instance bool :: eq
  (Haskell -)

code_const "op = \<Colon> bool \<Rightarrow> bool \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const True and False and Not and "op &" and "op |" and If
  (SML "true" and "false" and "not"
    and infixl 1 "andalso" and infixl 0 "orelse"
    and "!(if (_)/ then (_)/ else (_))")
  (OCaml "true" and "false" and "not"
    and infixl 4 "&&" and infixl 2 "||"
    and "!(if (_)/ then (_)/ else (_))")
  (Haskell "True" and "False" and "not"
    and infixl 3 "&&" and infixl 2 "||"
    and "!(if (_)/ then (_)/ else (_))")

code_reserved SML
  bool true false not

code_reserved OCaml
  bool true false not


text {* itself as a code generator datatype *}

setup {*
let fun add_itself thy =
  let
    val v = ("'a", []);
    val t = Logic.mk_type (TFree v);
    val Const (c, ty) = t;
    val (_, Type (dtco, _)) = strip_type ty;
  in
    thy
    |> CodegenData.add_datatype (dtco, (([v], [(c, [])]), CodegenData.lazy (fn () => [])))
  end
in add_itself end;
*} 


text {* code generation for arbitrary as exception *}

setup {*
  CodegenSerializer.add_undefined "SML" "arbitrary" "(raise Fail \"arbitrary\")"
  #> CodegenSerializer.add_undefined "OCaml" "arbitrary" "(failwith \"arbitrary\")"
*}

code_const arbitrary
  (Haskell "error/ \"arbitrary\"")

code_reserved SML Fail
code_reserved OCaml failwith


subsection {* Evaluation oracle *}

ML {*
signature HOL_EVAL =
sig
  val reff: bool option ref
  val prop: theory -> term -> term
  val tac: int -> tactic
  val method: Method.src -> Proof.context -> Method.method
end;

structure HOL_Eval =
struct

val reff : bool option ref = ref NONE;

fun prop thy t =
  if CodegenPackage.eval_term thy
    (("HOL_Eval.reff", reff), t)
    then HOLogic.true_const
    else HOLogic.false_const

fun mk_eq thy t =
  Logic.mk_equals (t, prop thy t)

end;
*}

setup {*
  PureThy.add_oracle ("invoke", "term", "HOL_Eval.mk_eq")
*}

ML {*
structure HOL_Eval : HOL_EVAL =
struct

open HOL_Eval;

fun conv ct =
  let
    val {thy, t, ...} = rep_cterm ct;
  in invoke thy t end;

fun tac i = Tactical.PRIMITIVE (Drule.fconv_rule
  (Drule.goals_conv (equal i) (HOLogic.Trueprop_conv conv)));

val method =
  Method.no_args (Method.SIMPLE_METHOD' (tac THEN' rtac TrueI));

end;
*}

setup {*
  Method.add_method ("eval", HOL_Eval.method, "solve goal by evaluation")
*}


subsection {* Normalization by evaluation *}

setup {*
let
  fun normalization_tac i = Tactical.PRIMITIVE (Drule.fconv_rule
    (Drule.goals_conv (equal i) (HOLogic.Trueprop_conv
      NBE.normalization_conv)));
  val normalization_meth =
    Method.no_args (Method.SIMPLE_METHOD' (normalization_tac THEN' resolve_tac [TrueI, refl]));
in
  Method.add_method ("normalization", normalization_meth, "solve goal by normalization")
end;
*}

text {* lazy @{const If} *}

definition
  if_delayed :: "bool \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "if_delayed b f g = (if b then f True else g False)"

lemma [code func]:
  shows "if_delayed True f g = f True"
    and "if_delayed False f g = g False"
  unfolding if_delayed_def by simp_all

lemma [normal pre, symmetric, normal post]:
  "(if b then x else y) = if_delayed b (\<lambda>_. x) (\<lambda>_. y)"
  unfolding if_delayed_def ..


hide (open) const if_delayed

end