(* Author: Lukas Bulwahn, TU Muenchen *)

header {* A Prototype of Quickcheck based on the Predicate Compiler *}

theory Predicate_Compile_Quickcheck
imports Main
uses "../Tools/Predicate_Compile/predicate_compile_quickcheck.ML"
begin

setup {* Quickcheck.add_generator ("predicate_compile", Predicate_Compile_Quickcheck.quickcheck) *}

end