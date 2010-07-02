
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator using pretty literals *}

theory Generate_Pretty
imports Candidates_Pretty
begin

lemma [code, code del]: "nat_of_char = nat_of_char" ..
lemma [code, code del]: "char_of_nat = char_of_nat" ..
lemma [code, code del]: "(less_eq :: char \<Rightarrow> _) = less_eq" ..
lemma [code, code del]: "(less :: char \<Rightarrow> _) = less" ..

export_code * in SML module_name Code_Test
  in OCaml module_name Code_Test file -
  in Haskell file -
  in Scala file -

end
