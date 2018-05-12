(*  Title:      HOL/Codegenerator_Test/Code_Test_SMLNJ.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on SMLNJ
*)

theory Code_Test_SMLNJ imports  "HOL-Library.Code_Test" Code_Lazy_Test begin

test_code "14 + 7 * -12 = (140 div -2 :: integer)" in SMLNJ

value [SMLNJ] "14 + 7 * -12 :: integer"

test_code "stake 10 (cycle ''ab'') = ''ababababab''" in SMLNJ

end
