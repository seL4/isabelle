(*  Title:      HOL/Code_Setup.thy
    ID:         $Id$
    Author:     Florian Haftmann
*)

header {* Setup of code generators and derived tools *}

theory Code_Setup
imports HOL
uses "~~/src/HOL/Tools/recfun_codegen.ML"
begin

subsection {* SML code generator setup *}

setup RecfunCodegen.setup

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
              (Pretty.block [pt, Codegen.str " =", Pretty.brk 1, pu]))
          end
     | (t as Const ("op =", _), ts) => SOME (Codegen.invoke_codegen
         thy defs dep thyname b (gr, Codegen.eta_expand t ts 2))
     | _ => NONE);

in
  Codegen.add_codegen "eq_codegen" eq_codegen
end
*}

quickcheck_params [size = 5, iterations = 50]

text {* Evaluation *}

method_setup evaluation = {*
  Method.no_args (Method.SIMPLE_METHOD' (CONVERSION Codegen.evaluation_conv THEN' rtac TrueI))
*} "solve goal by evaluation"


subsection {* Generic code generator setup *}

text {* using built-in Haskell equality *}

code_class eq
  (Haskell "Eq" where "op =" \<equiv> "(==)")

code_const "op ="
  (Haskell infixl 4 "==")


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


text {* code generation for undefined as exception *}

code_abort undefined

code_const undefined
  (SML "raise/ Fail/ \"undefined\"")
  (OCaml "failwith/ \"undefined\"")
  (Haskell "error/ \"undefined\"")


subsection {* Evaluation oracle *}

ML {*
structure Eval_Method =
struct

val eval_ref : (unit -> bool) option ref = ref NONE;

end;
*}

oracle eval_oracle ("term") = {* fn thy => fn t => 
  if CodeTarget.eval_term ("Eval_Method.eval_ref", Eval_Method.eval_ref) thy
    (HOLogic.dest_Trueprop t) [] 
  then t
  else HOLogic.Trueprop $ HOLogic.true_const (*dummy*)
*}

method_setup eval = {*
let
  fun eval_tac thy = 
    SUBGOAL (fn (t, i) => rtac (eval_oracle thy t) i)
in 
  Method.ctxt_args (fn ctxt => 
    Method.SIMPLE_METHOD' (eval_tac (ProofContext.theory_of ctxt)))
end
*} "solve goal by evaluation"


subsection {* Normalization by evaluation *}

method_setup normalization = {*
  Method.no_args (Method.SIMPLE_METHOD'
    (CONVERSION (ObjectLogic.judgment_conv Nbe.norm_conv)
    THEN' (fn k => TRY (rtac TrueI k))
  ))
*} "solve goal by normalization"

end
