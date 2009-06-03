
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator *}

theory Codegenerator_Test
imports Codegenerator_Candidates
begin

export_code * in SML module_name CodegenTest
  in OCaml module_name CodegenTest file -
  in Haskell file -

end
