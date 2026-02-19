(*  Title:      HOL/ex/Code_Assertion.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Code_Assertion
  imports Main
begin

ML_file \<open>Tools/code_assertion.ML\<close>

attribute_setup code_assert = Code_Assertion.attribute
  \<open>check code generation for each global interpretation using the given definitions and target language\<close>

end