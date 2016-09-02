(*  Title:      HOL/Library/Predicate_Compile_Alternative_Defs.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

section \<open>A Prototype of Quickcheck based on the Predicate Compiler\<close>

theory Predicate_Compile_Quickcheck
  imports Predicate_Compile_Alternative_Defs
begin

ML_file "../Tools/Predicate_Compile/predicate_compile_quickcheck.ML"

end
