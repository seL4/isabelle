
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator *}

theory Generate
imports Candidates
begin

export_code * in SML module_name Code_Test
  in OCaml module_name Code_Test file -
  in Haskell file -
  in Scala file -

end
