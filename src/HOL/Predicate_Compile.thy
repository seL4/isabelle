(*  Title:      HOL/Predicate_Compile.thy
    Author:     Stefan Berghofer, Lukas Bulwahn, Florian Haftmann, TU Muenchen
*)

header {* A compiler for predicates defined by introduction rules *}

theory Predicate_Compile
imports Predicate New_Random_Sequence Quickcheck_Exhaustive
keywords "code_pred" :: thy_goal and "values" :: diag
begin

ML_file "Tools/Predicate_Compile/predicate_compile_aux.ML"
ML_file "Tools/Predicate_Compile/predicate_compile_compilations.ML"
ML_file "Tools/Predicate_Compile/core_data.ML"
ML_file "Tools/Predicate_Compile/mode_inference.ML"
ML_file "Tools/Predicate_Compile/predicate_compile_proof.ML"
ML_file "Tools/Predicate_Compile/predicate_compile_core.ML"
ML_file "Tools/Predicate_Compile/predicate_compile_data.ML"
ML_file "Tools/Predicate_Compile/predicate_compile_fun.ML"
ML_file "Tools/Predicate_Compile/predicate_compile_pred.ML"
ML_file "Tools/Predicate_Compile/predicate_compile_specialisation.ML"
ML_file "Tools/Predicate_Compile/predicate_compile.ML"

setup Predicate_Compile.setup

end
