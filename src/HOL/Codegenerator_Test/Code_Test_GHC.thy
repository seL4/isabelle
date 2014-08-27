(*  Title:      Code_Test_GHC.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on GHC
*)

theory Code_Test_GHC imports Code_Test begin

definition id_integer :: "integer \<Rightarrow> integer" where "id_integer = id"

test_code "id_integer (14 + 7 * -12) = 140 div -2" in GHC

eval_term "14 + 7 * -12 :: integer" in GHC

end
