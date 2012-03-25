
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator using pretty literals *}

theory Generate_Pretty
imports Candidates_Pretty
begin

lemma [code, code del]: "nat_of_char = nat_of_char" ..
lemma [code, code del]: "char_of_nat = char_of_nat" ..

declare Quickcheck_Narrowing.one_code_int_code [code del]
declare Quickcheck_Narrowing.int_of_code [code del]

subsection {* Check whether generated code compiles *}

text {*
  If any of the checks fails, inspect the code generated
  by a corresponding @{text export_code} command.
*}

export_code _ checking SML OCaml? Haskell? Scala?

end
