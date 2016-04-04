(*  Title:      HOL/Corec_Examples/Tests/Merge_C.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Tests theory merges.
*)

section \<open>Tests Theory Merges\<close>

theory Merge_C
imports Merge_A
begin

consts fc :: "'a ta \<Rightarrow> 'a ta"
consts gc :: "'a ta \<Rightarrow> 'a ta"

friend_of_corec fc :: "'a ta \<Rightarrow> 'a ta" where
  "fc t = Ca (sa1 t) (sa2 t)"
  sorry

friend_of_corec gb :: "'a ta \<Rightarrow> 'a ta" where
  "gb t = Ca (sa1 t) (sa2 t)"
  sorry

friend_of_corec gc :: "'a ta \<Rightarrow> 'a ta" where
  "gc t = Ca (sa1 t) (sa2 t)"
  sorry

end
