(*  Title:      HOL/Codegenerator_Test/Code_Test_GHC.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on GHC
*)

theory Code_Test_GHC imports "HOL-Library.Code_Test" begin

test_code "(14 + 7 * -12 :: integer) = 140 div -2" in GHC

value [GHC] "14 + 7 * -12 :: integer"

test_code \<comment> \<open>Tests for the serialisation of @{const gcd} on @{typ integer}\<close>
  "gcd 15 10 = (5 :: integer)"
  "gcd 15 (- 10) = (5 :: integer)"
  "gcd (- 10) 15 = (5 :: integer)"
  "gcd (- 10) (- 15) = (5 :: integer)"
  "gcd 0 (- 10) = (10 :: integer)"
  "gcd (- 10) 0 = (10 :: integer)"
  "gcd 0 0 = (0 :: integer)"
in GHC

end
