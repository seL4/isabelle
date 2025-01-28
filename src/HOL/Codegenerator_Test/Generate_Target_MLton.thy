(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Test of target-language specific implementations for MLton\<close>

theory Generate_Target_MLton
  imports
    "HOL-Codegenerator_Test.Generate_Target_String_Literals"
    "HOL-Codegenerator_Test.Generate_Target_Bit_Operations"
begin

test_code Generate_Target_String_Literals.check in MLton
test_code Generate_Target_Bit_Operations.check in MLton

end