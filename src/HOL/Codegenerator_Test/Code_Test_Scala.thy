(*  Title:      HOL/Codegenerator_Test/Code_Test_Scala.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Code_Test_Scala
imports
  "HOL-Library.Code_Test"
  Code_Lazy_Test
begin

text \<open>Test cases for \<^text>\<open>test_code\<close>\<close>

test_code "14 + 7 * -12 = (140 div -2 :: integer)" in Scala

value [Scala] "14 + 7 * -12 :: integer"

test_code \<comment> \<open>Tests for the serialisation of \<^const>\<open>gcd\<close> on \<^typ>\<open>integer\<close>\<close>
  "gcd 15 10 = (5 :: integer)"
  "gcd 15 (- 10) = (5 :: integer)"
  "gcd (- 10) 15 = (5 :: integer)"
  "gcd (- 10) (- 15) = (5 :: integer)"
  "gcd 0 (- 10) = (10 :: integer)"
  "gcd (- 10) 0 = (10 :: integer)"
  "gcd 0 0 = (0 :: integer)"
in Scala

test_code "stake 10 (cycle ''ab'') = ''ababababab''" in Scala

end
