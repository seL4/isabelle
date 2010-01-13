
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator using pretty literals *}

theory Codegenerator_Pretty_Test
imports Codegenerator_Pretty
begin

export_code * in SML module_name CodegenTest
  in OCaml module_name CodegenTest file -
  in Haskell file -
(*in Scala file -*)

end
