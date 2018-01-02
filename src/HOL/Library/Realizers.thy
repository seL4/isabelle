(*  Title:      HOL/Library/Realizers.thy
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
*)

section \<open>Program extraction from proofs involving datatypes and inductive predicates\<close>

theory Realizers
imports Main
begin

ML_file "~~/src/HOL/Tools/datatype_realizer.ML"
ML_file "~~/src/HOL/Tools/inductive_realizer.ML"

end
