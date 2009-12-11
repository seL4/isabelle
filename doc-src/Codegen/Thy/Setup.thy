theory Setup
imports Complex_Main
uses
  "../../antiquote_setup.ML"
  "../../more_antiquote.ML"
begin

ML {* no_document use_thys
  ["Efficient_Nat", "Code_Char_chr", "Product_ord", "~~/src/HOL/Imperative_HOL/Imperative_HOL",
   "~~/src/HOL/Decision_Procs/Ferrack"] *}

setup {* Code_Target.set_default_code_width 74 *}

ML_command {* Unsynchronized.reset unique_names *}

end
