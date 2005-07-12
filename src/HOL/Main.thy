(*  Title:      HOL/Main.thy
    ID:         $Id$
    Author:     Stefan Berghofer, Tobias Nipkow, Tjark Weber, Markus Wenzel (TU Muenchen)
*)

header {* Main HOL *}

theory Main
    imports Refute Reconstruction

begin

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.
*}

subsection {* Configuration of the code generator *}

types_code
  "bool"  ("bool")
attach (term_of) {*
fun term_of_bool b = if b then HOLogic.true_const else HOLogic.false_const;
*}
attach (test) {*
fun gen_bool i = one_of [false, true];
*}

consts_code
  "True"    ("true")
  "False"   ("false")
  "Not"     ("not")
  "op |"    ("(_ orelse/ _)")
  "op &"    ("(_ andalso/ _)")
  "HOL.If"      ("(if _/ then _/ else _)")

  "wfrec"   ("\<module>wf'_rec?")
attach {*
fun wf_rec f x = f (wf_rec f) x;
*}

quickcheck_params [default_type = int]

ML {*
local

fun eq_codegen thy defs gr dep thyname b t =
    (case strip_comb t of
       (Const ("op =", Type (_, [Type ("fun", _), _])), _) => NONE
     | (Const ("op =", _), [t, u]) =>
          let
            val (gr', pt) = Codegen.invoke_codegen thy defs dep thyname false (gr, t);
            val (gr'', pu) = Codegen.invoke_codegen thy defs dep thyname false (gr', u)
          in
            SOME (gr'', Codegen.parens
              (Pretty.block [pt, Pretty.str " =", Pretty.brk 1, pu]))
          end
     | (t as Const ("op =", _), ts) => SOME (Codegen.invoke_codegen
         thy defs dep thyname b (gr, Codegen.eta_expand t ts 2))
     | _ => NONE);

in

val eq_codegen_setup = [Codegen.add_codegen "eq_codegen" eq_codegen];

end;
*}

setup eq_codegen_setup

lemmas [code] = imp_conv_disj

subsection {* Configuration of the 'refute' command *}

text {*
  The following are fairly reasonable default values.  For an
  explanation of these parameters, see 'HOL/Refute.thy'.
*}

refute_params ["itself"=1,
               minsize=1,
               maxsize=8,
               maxvars=10000,
               maxtime=60,
               satsolver="auto"]

end
