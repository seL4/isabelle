theory Quickcheck_Nesting_Example
imports Quickcheck_Nesting
begin

datatype x = X "x list"

lemma "X a = X b"
quickcheck[exhaustive, size = 4, expect = counterexample]
oops

end
