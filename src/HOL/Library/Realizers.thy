(*  Title:      HOL/Library/Realizers.thy
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
*)

section \<open>Program extraction from proofs involving datatypes and inductive predicates\<close>

theory Realizers
imports Main
begin

ML_file \<open>~~/src/HOL/Tools/datatype_realizer.ML\<close>
ML_file \<open>~~/src/HOL/Tools/inductive_realizer.ML\<close>

end
