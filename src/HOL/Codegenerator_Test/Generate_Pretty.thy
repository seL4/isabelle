
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator using pretty literals *}

theory Generate_Pretty
imports Candidates_Pretty
begin

lemma [code, code del]: "nat_of_char = nat_of_char" ..
lemma [code, code del]: "char_of_nat = char_of_nat" ..
lemma [code, code del]: "(less_eq :: char \<Rightarrow> _) = less_eq" ..
lemma [code, code del]: "(less :: char \<Rightarrow> _) = less" ..

subsection {* Check whether generated code compiles *}

text {*
  If any of the @{text ML} ... check fails, inspect the code generated
  by the previous @{text export_code} command.
*}

export_code "*" in SML module_name Code_Test file -
ML {* Cache_IO.with_tmp_dir "Code_Test" (Code_ML.check_SML @{theory}) *}

export_code "*" in OCaml module_name Code_Test file -
ML {* Cache_IO.with_tmp_dir "Code_Test" (Code_ML.check_OCaml @{theory}) *}

export_code "*" in Haskell module_name Code_Test file -
ML {* Cache_IO.with_tmp_dir "Code_Test" (Code_Haskell.check @{theory}) *}

export_code "*" in Scala module_name Code_Test file -
ML {* Cache_IO.with_tmp_dir "Code_Test" (Code_Scala.check @{theory}) *}

end
