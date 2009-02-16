(*  Title:      HOL/ex/Codegenerator_Pretty.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Simple examples for pretty numerals and such *}

theory Codegenerator_Pretty
imports ExecutableContent Code_Char Efficient_Nat
begin

declare isnorm.simps [code del]

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
