(*  Title:      HOL/Main.thy
    ID:         $Id$
    Author:     Stefan Berghofer, Tobias Nipkow, Tjark Weber, Markus Wenzel (TU Muenchen)
*)

header {* Main HOL *}

theory Main
    imports Extraction Refute Reconstruction

begin

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.
*}

subsection {* Configuration of the code generator *}

types_code
  "bool"  ("bool")

consts_code
  "True"    ("true")
  "False"   ("false")
  "Not"     ("not")
  "op |"    ("(_ orelse/ _)")
  "op &"    ("(_ andalso/ _)")
  "If"      ("(if _/ then _/ else _)")

  "wfrec"   ("wf'_rec?")

quickcheck_params [default_type = int]

ML {*
fun wf_rec f x = f (wf_rec f) x;

fun term_of_bool b = if b then HOLogic.true_const else HOLogic.false_const;
val term_of_int = HOLogic.mk_int;
fun term_of_fun_type _ T _ U _ = Free ("<function>", T --> U);

val eq_codegen_setup = [Codegen.add_codegen "eq_codegen"
  (fn thy => fn gr => fn dep => fn b => fn t =>
    (case strip_comb t of
       (Const ("op =", Type (_, [Type ("fun", _), _])), _) => NONE
     | (Const ("op =", _), [t, u]) =>
          let
            val (gr', pt) = Codegen.invoke_codegen thy dep false (gr, t);
            val (gr'', pu) = Codegen.invoke_codegen thy dep false (gr', u)
          in
            SOME (gr'', Codegen.parens
              (Pretty.block [pt, Pretty.str " =", Pretty.brk 1, pu]))
          end
     | (t as Const ("op =", _), ts) => SOME (Codegen.invoke_codegen
         thy dep b (gr, Codegen.eta_expand t ts 2))
     | _ => NONE))];

fun gen_bool i = one_of [false, true];

fun gen_int i = one_of [~1, 1] * random_range 0 i;

fun gen_fun_type _ G i =
  let
    val f = ref (fn x => raise ERROR);
    val _ = (f := (fn x =>
      let
        val y = G i;
        val f' = !f
      in (f := (fn x' => if x = x' then y else f' x'); y) end))
  in (fn x => !f x) end;
*}

setup eq_codegen_setup

lemma [code]: "((n::nat) < 0) = False" by simp
lemma [code]: "(0 < Suc n) = True" by simp
lemmas [code] = Suc_less_eq imp_conv_disj

subsection {* Configuration of the 'refute' command *}

text {*
  The following are fairly reasonable default values.  For an
  explanation of these parameters, see 'HOL/Refute.thy'.
*}

refute_params [minsize=1,
               maxsize=8,
               maxvars=10000,
               maxtime=60,
               satsolver="auto"]

end
