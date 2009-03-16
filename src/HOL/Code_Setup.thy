(*  Title:      HOL/Code_Setup.thy
    ID:         $Id$
    Author:     Florian Haftmann
*)

header {* Setup of code generators and related tools *}

theory Code_Setup
imports HOL
begin

subsection {* Generic code generator foundation *}

text {* Datatypes *}

code_datatype True False

code_datatype "TYPE('a\<Colon>{})"

code_datatype Trueprop "prop"

text {* Code equations *}

lemma [code]:
  shows "(True \<Longrightarrow> PROP P) \<equiv> PROP P" 
    and "(False \<Longrightarrow> Q) \<equiv> Trueprop True" 
    and "(PROP P \<Longrightarrow> True) \<equiv> Trueprop True" 
    and "(Q \<Longrightarrow> False) \<equiv> Trueprop (\<not> Q)" by (auto intro!: equal_intr_rule)

lemma [code]:
  shows "False \<and> x \<longleftrightarrow> False"
    and "True \<and> x \<longleftrightarrow> x"
    and "x \<and> False \<longleftrightarrow> False"
    and "x \<and> True \<longleftrightarrow> x" by simp_all

lemma [code]:
  shows "False \<or> x \<longleftrightarrow> x"
    and "True \<or> x \<longleftrightarrow> True"
    and "x \<or> False \<longleftrightarrow> x"
    and "x \<or> True \<longleftrightarrow> True" by simp_all

lemma [code]:
  shows "\<not> True \<longleftrightarrow> False"
    and "\<not> False \<longleftrightarrow> True" by (rule HOL.simp_thms)+

lemmas [code] = Let_def if_True if_False

lemmas [code, code unfold, symmetric, code post] = imp_conv_disj

text {* Equality *}

context eq
begin

lemma equals_eq [code inline, code]: "op = \<equiv> eq"
  by (rule eq_reflection) (rule ext, rule ext, rule sym, rule eq_equals)

declare eq [code unfold, code inline del]

declare equals_eq [symmetric, code post]

end

declare simp_thms(6) [code nbe]

hide (open) const eq
hide const eq

setup {*
  Code_Unit.add_const_alias @{thm equals_eq}
*}

text {* Cases *}

lemma Let_case_cert:
  assumes "CASE \<equiv> (\<lambda>x. Let x f)"
  shows "CASE x \<equiv> f x"
  using assms by simp_all

lemma If_case_cert:
  assumes "CASE \<equiv> (\<lambda>b. If b f g)"
  shows "(CASE True \<equiv> f) &&& (CASE False \<equiv> g)"
  using assms by simp_all

setup {*
  Code.add_case @{thm Let_case_cert}
  #> Code.add_case @{thm If_case_cert}
  #> Code.add_undefined @{const_name undefined}
*}

code_abort undefined


subsection {* Generic code generator preprocessor *}

setup {*
  Code.map_pre (K HOL_basic_ss)
  #> Code.map_post (K HOL_basic_ss)
*}


subsection {* Generic code generator target languages *}

text {* type bool *}

code_type bool
  (SML "bool")
  (OCaml "bool")
  (Haskell "Bool")

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
  bool not

text {* using built-in Haskell equality *}

code_class eq
  (Haskell "Eq")

code_const "eq_class.eq"
  (Haskell infixl 4 "==")

code_const "op ="
  (Haskell infixl 4 "==")

text {* undefined *}

code_const undefined
  (SML "!(raise/ Fail/ \"undefined\")")
  (OCaml "failwith/ \"undefined\"")
  (Haskell "error/ \"undefined\"")


subsection {* SML code generator setup *}

types_code
  "bool"  ("bool")
attach (term_of) {*
fun term_of_bool b = if b then HOLogic.true_const else HOLogic.false_const;
*}
attach (test) {*
fun gen_bool i =
  let val b = one_of [false, true]
  in (b, fn () => term_of_bool b) end;
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
  "Not"     ("Bool.not")
  "op |"    ("(_ orelse/ _)")
  "op &"    ("(_ andalso/ _)")
  "If"      ("(if _/ then _/ else _)")

setup {*
let

fun eq_codegen thy defs dep thyname b t gr =
    (case strip_comb t of
       (Const ("op =", Type (_, [Type ("fun", _), _])), _) => NONE
     | (Const ("op =", _), [t, u]) =>
          let
            val (pt, gr') = Codegen.invoke_codegen thy defs dep thyname false t gr;
            val (pu, gr'') = Codegen.invoke_codegen thy defs dep thyname false u gr';
            val (_, gr''') = Codegen.invoke_tycodegen thy defs dep thyname false HOLogic.boolT gr'';
          in
            SOME (Codegen.parens
              (Pretty.block [pt, Codegen.str " =", Pretty.brk 1, pu]), gr''')
          end
     | (t as Const ("op =", _), ts) => SOME (Codegen.invoke_codegen
         thy defs dep thyname b (Codegen.eta_expand t ts 2) gr)
     | _ => NONE);

in
  Codegen.add_codegen "eq_codegen" eq_codegen
end
*}


subsection {* Evaluation and normalization by evaluation *}

setup {*
  Value.add_evaluator ("SML", Codegen.eval_term o ProofContext.theory_of)
*}

ML {*
structure Eval_Method =
struct

val eval_ref : (unit -> bool) option ref = ref NONE;

end;
*}

oracle eval_oracle = {* fn ct =>
  let
    val thy = Thm.theory_of_cterm ct;
    val t = Thm.term_of ct;
    val dummy = @{cprop True};
  in case try HOLogic.dest_Trueprop t
   of SOME t' => if Code_ML.eval_term
         ("Eval_Method.eval_ref", Eval_Method.eval_ref) thy t' [] 
       then Thm.capply (Thm.capply @{cterm "op \<equiv> \<Colon> prop \<Rightarrow> prop \<Rightarrow> prop"} ct) dummy
       else dummy
    | NONE => dummy
  end
*}

ML {*
fun gen_eval_method conv ctxt = SIMPLE_METHOD'
  (CONVERSION (Conv.params_conv (~1) (K (Conv.concl_conv (~1) conv)) ctxt)
    THEN' rtac TrueI)
*}

method_setup eval = {* Scan.succeed (gen_eval_method eval_oracle) *}
  "solve goal by evaluation"

method_setup evaluation = {* Scan.succeed (gen_eval_method Codegen.evaluation_conv) *}
  "solve goal by evaluation"

method_setup normalization = {*
  Scan.succeed (K (SIMPLE_METHOD' (CONVERSION Nbe.norm_conv THEN' (fn k => TRY (rtac TrueI k)))))
*} "solve goal by normalization"


subsection {* Quickcheck *}

setup {*
  Quickcheck.add_generator ("SML", Codegen.test_term)
*}

quickcheck_params [size = 5, iterations = 50]

end
