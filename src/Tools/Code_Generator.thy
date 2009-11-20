(*  Title:   Tools/Code_Generator.thy
    Author:  Florian Haftmann, TU Muenchen
*)

header {* Loading the code generator modules *}

theory Code_Generator
imports Pure
uses
  "~~/src/Tools/auto_counterexample.ML"
  "~~/src/Tools/value.ML"
  "~~/src/Tools/quickcheck.ML"
  "~~/src/Tools/Code/code_preproc.ML" 
  "~~/src/Tools/Code/code_thingol.ML"
  "~~/src/Tools/Code/code_printer.ML"
  "~~/src/Tools/Code/code_target.ML"
  "~~/src/Tools/Code/code_ml.ML"
  "~~/src/Tools/Code/code_haskell.ML"
  "~~/src/Tools/nbe.ML"
begin

setup {*
  Code_Preproc.setup
  #> Code_ML.setup
  #> Code_Haskell.setup
  #> Nbe.setup
*}

end
