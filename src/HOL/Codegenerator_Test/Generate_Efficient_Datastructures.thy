
(* Author: Ondrej Kuncar, TU Muenchen *)

section \<open>Pervasive test of code generator\<close>

theory Generate_Efficient_Datastructures
imports
  Candidates
  "~~/src/HOL/Library/DAList_Multiset"
  "~~/src/HOL/Library/RBT_Mapping"
  "~~/src/HOL/Library/RBT_Set"
begin

text \<open>
  The following code equations have to be deleted because they use 
  lists to implement sets in the code generetor. 
\<close>

declare [[code drop:
  "Inf :: _ Predicate.pred set \<Rightarrow> _"
  "Sup :: _ Predicate.pred set \<Rightarrow> _"
  pred_of_set
  Wellfounded.acc
  Cardinality.card'
  Cardinality.finite'
  Cardinality.subset'
  Cardinality.eq_set
  Euclidean_Algorithm.Gcd
  Euclidean_Algorithm.Lcm
  "Gcd :: _ poly set \<Rightarrow> _"
  "Lcm :: _ poly set \<Rightarrow> _"
  permutations_of_set
  permutations_of_multiset
]]

text \<open>
  If code generation fails with a message like
  @{text \<open>"List.set" is not a constructor, on left hand side of equation: ...\<close>},
  feel free to add an RBT implementation for the corrsponding operation
  of delete that code equation (see above).
\<close>
 
export_code _ checking SML OCaml? Haskell? Scala

end
