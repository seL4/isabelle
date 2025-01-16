(*  Title:      HOL/Codegenerator_Test/Code_Test_PolyML.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Code_Test_PolyML
imports 
  "HOL-Library.Code_Test"
  Code_Lazy_Test
begin

text \<open>Test cases for \<^text>\<open>test_code\<close>\<close>

test_code "14 + 7 * -12 = (140 div -2 :: integer)" in PolyML

value [PolyML] "14 + 7 * -12 :: integer"

test_code "stake 10 (cycle ''ab'') = ''ababababab''" in PolyML

end
