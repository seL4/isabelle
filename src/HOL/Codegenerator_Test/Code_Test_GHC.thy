(*  Title:      Code_Test_GHC.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on GHC
*)

theory Code_Test_GHC imports "../Library/Code_Test" begin

test_code "(14 + 7 * -12 :: integer) = 140 div -2" in GHC

value [GHC] "14 + 7 * -12 :: integer"

end
