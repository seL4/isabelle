theory IArray_Examples
imports "HOL-Library.IArray" "HOL-Library.Code_Target_Numeral"
begin

lemma "IArray [True,False] !! 1 = False"
by eval

lemma "IArray.length (IArray [[],[]]) = 2"
by eval

lemma "IArray.list_of (IArray [1,3::int]) = [1,3]"
by eval

lemma "IArray.list_of (IArray.of_fun (%n. n*n) 5) = [0,1,4,9,16]"
by eval

lemma "\<not> IArray.all (\<lambda>x. x > 2) (IArray [1,3::int])"
by eval

lemma "IArray.exists (\<lambda>x. x > 2) (IArray [1,3::int])"
by eval

fun sum2 :: "'a::monoid_add iarray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
"sum2 A n s = (if n=0 then s else sum2 A (n - 1) (s + A!!(n - 1)))"

definition sum :: "'a::monoid_add iarray \<Rightarrow> 'a" where
"sum A = sum2 A (IArray.length A) 0"

lemma "sum (IArray [1,2,3,4,5,6,7,8,9::int]) = 45"
by eval

definition partial_geometric_sum :: "'a::comm_ring_1 list \<Rightarrow> 'a"
  where "partial_geometric_sum xs = (let
    values = IArray xs;
    coefficients = IArray.of_fun of_nat (length xs)
  in sum_list (map (\<lambda>i. values !! i * coefficients !! i) [0..<IArray.length values]))"

export_code partial_geometric_sum checking SML OCaml? Haskell? Scala

end

