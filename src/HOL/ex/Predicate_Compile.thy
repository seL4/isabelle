theory Predicate_Compile
imports Complex_Main RPred
uses
  "../Tools/Predicate_Compile/pred_compile_aux.ML"
  "../Tools/Predicate_Compile/predicate_compile_core.ML"
  "../Tools/Predicate_Compile/pred_compile_set.ML"
  "../Tools/Predicate_Compile/pred_compile_data.ML"
  "../Tools/Predicate_Compile/pred_compile_fun.ML"
  "../Tools/Predicate_Compile/pred_compile_pred.ML"
  "../Tools/Predicate_Compile/predicate_compile.ML"
  "../Tools/Predicate_Compile/pred_compile_quickcheck.ML"
begin

setup {* Predicate_Compile.setup *}
setup {* Quickcheck.add_generator ("pred_compile", Pred_Compile_Quickcheck.quickcheck) *}

end