(*  Title:      HOL/Codegenerator_Test/Code_Test_PolyML.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on PolyML
*)

theory Code_Test_PolyML imports  "../Library/Code_Test" begin

test_code "14 + 7 * -12 = (140 div -2 :: integer)" in PolyML

value [PolyML] "14 + 7 * -12 :: integer"

end
