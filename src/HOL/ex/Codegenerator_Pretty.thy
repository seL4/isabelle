(*  Title:      HOL/ex/Codegenerator_Pretty.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Simple examples for pretty numerals and such *}

theory Codegenerator_Pretty
imports ExecutableContent Code_Char Efficient_Nat
begin

setup {*
  Code.del_funcs
    (AxClass.param_of_inst @{theory} (@{const_name "Eval.term_of"}, @{type_name "index"}))
  #> Code.del_funcs
    (AxClass.param_of_inst @{theory} (@{const_name "Eval.term_of"}, @{type_name "char"}))
  #> Code.del_funcs
    (AxClass.param_of_inst @{theory} (@{const_name "Eval.term_of"}, @{type_name "int"}))
  #> Code.del_funcs
    (AxClass.param_of_inst @{theory} (@{const_name "Eval.term_of"}, @{type_name "nat"}))
*}

declare char.recs [code func del]
  char.cases [code func del]
  char.size [code func del]

declare isnorm.simps [code func del]

ML {* (*FIXME get rid of this*)
nonfix union;
nonfix inter;
nonfix upto;
*}

export_code * in SML module_name CodegenTest
  in OCaml module_name CodegenTest file -
  in Haskell file -

ML {*
infix union;
infix inter;
infix 4 upto;
*}

end
