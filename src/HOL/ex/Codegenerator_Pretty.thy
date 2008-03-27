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

setup {*
let
  val charr = @{const_name Char}
  val nibbles = [@{const_name Nibble0}, @{const_name Nibble1},
    @{const_name Nibble2}, @{const_name Nibble3},
    @{const_name Nibble4}, @{const_name Nibble5},
    @{const_name Nibble6}, @{const_name Nibble7},
    @{const_name Nibble8}, @{const_name Nibble9},
    @{const_name NibbleA}, @{const_name NibbleB},
    @{const_name NibbleC}, @{const_name NibbleD},
    @{const_name NibbleE}, @{const_name NibbleF}];
in
  fold (fn target => CodeTarget.add_pretty_char target charr nibbles)
    ["SML", "OCaml", "Haskell"]
  #> CodeTarget.add_pretty_list_string "Haskell"
    @{const_name Nil} @{const_name Cons} charr nibbles
end
*}

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
