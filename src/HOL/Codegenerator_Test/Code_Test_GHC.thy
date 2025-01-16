(*  Title:      HOL/Codegenerator_Test/Code_Test_GHC.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Code_Test_GHC
imports
  "HOL-Library.Code_Test"
  Code_Lazy_Test
begin

text \<open>Test cases for \<^text>\<open>test_code\<close>\<close>

test_code "(14 + 7 * -12 :: integer) = 140 div -2" in GHC

value [GHC] "14 + 7 * -12 :: integer"

test_code \<comment> \<open>Tests for the serialisation of \<^const>\<open>gcd\<close> on \<^typ>\<open>integer\<close>\<close>
  "gcd 15 10 = (5 :: integer)"
  "gcd 15 (- 10) = (5 :: integer)"
  "gcd (- 10) 15 = (5 :: integer)"
  "gcd (- 10) (- 15) = (5 :: integer)"
  "gcd 0 (- 10) = (10 :: integer)"
  "gcd (- 10) 0 = (10 :: integer)"
  "gcd 0 0 = (0 :: integer)"
in GHC

test_code "stake 10 (cycle ''ab'') = ''ababababab''" in GHC

end
