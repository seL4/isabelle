(*  Title:      HOL/Corec_Examples/Tests/Merge_A.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Tests theory merges.
*)

section \<open>Tests Theory Merges\<close>

theory Merge_A
imports "HOL-Library.BNF_Corec"
begin

codatatype 'a ta = Ca (sa1: 'a) (sa2: "'a ta")

consts gb :: "'a ta \<Rightarrow> 'a ta"

corec fa where
  "fa = Ca (Suc 0) fa"

corec ga :: "'a ta \<Rightarrow> 'a ta" where
  "ga t = Ca (sa1 t) (sa2 t)"

friend_of_corec ga :: "'a ta \<Rightarrow> 'a ta" where
  "ga t = Ca (sa1 t) (Ca (sa1 t) (sa2 t))"
  sorry

thm ta.coinduct_upto
thm ta.cong_refl

end
