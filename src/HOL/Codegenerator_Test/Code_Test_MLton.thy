(*  Title:      HOL/Codegenerator_Test/Code_Test_MLton.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on MLton
*)

theory Code_Test_MLton imports  "../Library/Code_Test" begin

test_code "14 + 7 * -12 = (140 div -2 :: integer)" in MLton

value [MLton] "14 + 7 * -12 :: integer"

end
