(*  Title:      HOL/ex/Case_Product.thy
    Author:     Lars Noschinski
    Copyright   2011 TU Muenchen
*)

section \<open>Examples for the 'case_product' attribute\<close>

theory Case_Product
imports Main
begin

text \<open>
  The @{attribute case_product} attribute combines multiple case distinction
  lemmas into a single case distinction lemma by building the product of all
  these case distinctions.
\<close>

lemmas nat_list_exhaust = nat.exhaust [case_product list.exhaust]

text \<open>The attribute honours preconditions.\<close>

lemmas trancl_acc_cases = trancl.cases [case_product acc.cases]

text \<open>Also, case names are generated based on the old names.\<close>

end
