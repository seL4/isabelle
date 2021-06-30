
(* Author: Ondrej Kuncar, TU Muenchen *)

section \<open>Pervasive test of code generator\<close>

theory Generate_Efficient_Datastructures
imports
  Candidates
  "HOL-Library.DAList_Multiset"
  "HOL-Library.RBT_Mapping"
  "HOL-Library.RBT_Set"
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
  Code_Cardinality.card'
  Code_Cardinality.finite'
  Code_Cardinality.subset'
  Code_Cardinality.eq_set
  Euclidean_Algorithm.Gcd
  Euclidean_Algorithm.Lcm
  "Gcd :: _ poly set \<Rightarrow> _"
  "Lcm :: _ poly set \<Rightarrow> _"
]]

text \<open>
  If code generation fails with a message like
  \<open>"List.set" is not a constructor, on left hand side of equation: ...\<close>,
  feel free to add an RBT implementation for the corresponding operation
  or delete that code equation (see above).
\<close>

export_code _ checking SML OCaml? Haskell? Scala

end
