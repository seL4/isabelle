(*  Title:   Tools/Code_Generator.thy
    Author:  Florian Haftmann, TU Muenchen
*)

header {* Loading the code generator modules *}

theory Code_Generator
imports Pure
uses
  "~~/src/Tools/value.ML"
  "~~/src/Tools/quickcheck.ML"
  "~~/src/Tools/code/code_wellsorted.ML" 
  "~~/src/Tools/code/code_thingol.ML"
  "~~/src/Tools/code/code_printer.ML"
  "~~/src/Tools/code/code_target.ML"
  "~~/src/Tools/code/code_ml.ML"
  "~~/src/Tools/code/code_haskell.ML"
  "~~/src/Tools/nbe.ML"
begin

setup {*
  Code_ML.setup
  #> Code_Haskell.setup
  #> Nbe.setup
*}

end