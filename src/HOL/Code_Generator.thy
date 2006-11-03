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

fun evaluation_tac i = Tactical.PRIMITIVE (Drule.fconv_rule
  (Drule.goals_conv (equal i) Codegen.evaluation_conv));

val evaluation_meth =
  Method.no_args (Method.METHOD (fn _ => evaluation_tac 1 THEN rtac HOL.TrueI 1));

in

Method.add_method ("evaluation", evaluation_meth, "solve goal by evaluation")

end;
*}


subsection {* Generic code generator setup *}

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
*}

code_const arbitrary
  (Haskell "error/ \"arbitrary\"")

code_reserved SML Fail
code_reserved Haskell error


subsection {* normalization by evaluation *}

setup {*
let
  fun normalization_tac i = Tactical.PRIMITIVE (Drule.fconv_rule
    (Drule.goals_conv (equal i) (HOL.Trueprop_conv
      NBE.normalization_conv)));
  val normalization_meth =
    Method.no_args (Method.METHOD (fn _ => normalization_tac 1 THEN resolve_tac [TrueI, refl] 1));
in
  Method.add_method ("normalization", normalization_meth, "solve goal by normalization")
end;
*}

text {* lazy @{const If} *}

definition
  if_delayed :: "bool \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> 'a"
  "if_delayed b f g = (if b then f True else g False)"

lemma [code func]:
  shows "if_delayed True f g = f True"
    and "if_delayed False f g = g False"
  unfolding if_delayed_def by simp_all

lemma [normal pre, symmetric, normal post]:
  "(if b then x else y) = if_delayed b (\<lambda>_. x) (\<lambda>_. y)"
  unfolding if_delayed_def ..


subsection {* Operational equality for code generation *}

subsubsection {* eq class *}

class eq =
  fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

defs
  eq_def [normal post]: "eq \<equiv> (op =)"

lemmas [symmetric, code inline, code func] = eq_def


subsubsection {* bool type *}

instance bool :: eq ..

lemma [code func]:
  "eq True p = p" unfolding eq_def by auto

lemma [code func]:
  "eq False p = (\<not> p)" unfolding eq_def by auto

lemma [code func]:
  "eq p True = p" unfolding eq_def by auto

lemma [code func]:
  "eq p False = (\<not> p)" unfolding eq_def by auto


subsubsection {* Haskell *}

code_class eq
  (Haskell "Eq" where eq \<equiv> "(==)")

code_const eq
  (Haskell infixl 4 "==")

code_instance bool :: eq
  (Haskell -)

code_const "eq \<Colon> bool \<Rightarrow> bool \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_reserved Haskell
  Eq eq


hide (open) const eq if_delayed

end