(*  Title:      HOL/Corec_Examples/Tests/Merge_B.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Tests theory merges.
*)

section \<open>Tests Theory Merges\<close>

theory Merge_B
imports Merge_A
begin

consts fb :: "'a ta \<Rightarrow> 'a ta"
consts gb :: "'a ta \<Rightarrow> 'a ta"

friend_of_corec fb :: "'a ta \<Rightarrow> 'a ta" where
  "fb t = Ca (sa1 t) (sa2 t)"
  sorry

friend_of_corec gb :: "'a ta \<Rightarrow> 'a ta" where
  "gb t = Ca (sa1 t) (sa2 t)"
  sorry

end
