(*  Title:      Code_Test_Scala.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on Scala
*)

theory Code_Test_Scala imports Code_Test begin 

declare [[scala_case_insensitive]]

test_code "14 + 7 * -12 = (140 div -2 :: integer)" in Scala

value [Scala] "14 + 7 * -12 :: integer"

end
