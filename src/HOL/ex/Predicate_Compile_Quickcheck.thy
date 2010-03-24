(* Author: Lukas Bulwahn, TU Muenchen *)

header {* A Prototype of Quickcheck based on the Predicate Compiler *}

theory Predicate_Compile_Quickcheck
imports Main Predicate_Compile_Alternative_Defs
uses "../Tools/Predicate_Compile/predicate_compile_quickcheck.ML"
begin

setup {* Quickcheck.add_generator ("predicate_compile_wo_ff", Predicate_Compile_Quickcheck.quickcheck_compile_term false true 4) *}
setup {* Quickcheck.add_generator ("predicate_compile_ff_fs", Predicate_Compile_Quickcheck.quickcheck_compile_term true true 4) *}
setup {* Quickcheck.add_generator ("predicate_compile_ff_nofs", Predicate_Compile_Quickcheck.quickcheck_compile_term true false 4) *}

end