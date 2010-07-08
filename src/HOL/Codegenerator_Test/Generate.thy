
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator *}

theory Generate
imports Candidates
begin

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
