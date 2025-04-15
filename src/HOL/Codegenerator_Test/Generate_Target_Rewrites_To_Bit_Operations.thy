(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Test of arithmetic using target-language bit operations\<close>

theory Generate_Target_Rewrites_To_Bit_Operations
imports
  Basic_Setup
  "HOL-Library.Code_Bit_Shifts_for_Arithmetic"
  "HOL-Library.Code_Test"
begin

setup \<open>Codegenerator_Test.drop_partial_term_of\<close>

text \<open>
  If any of the checks fails, inspect the code generated
  by a corresponding \<open>export_code\<close> command.
\<close>

export_code _ checking SML OCaml? Haskell? Scala

end
