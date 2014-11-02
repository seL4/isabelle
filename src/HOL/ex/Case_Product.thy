(*  Title:      HOL/ex/Case_Product.thy
    Author:     Lars Noschinski
    Copyright   2011 TU Muenchen
*)

section {* Examples for the 'case_product' attribute *}

theory Case_Product
imports Main
begin

text {*
  The {@attribute case_product} attribute combines multiple case distinction
  lemmas into a single case distinction lemma by building the product of all
  these case distinctions.
*}

lemmas nat_list_exhaust = nat.exhaust[case_product list.exhaust]

text {*
  The attribute honors preconditions
*}

lemmas trancl_acc_cases= trancl.cases[case_product acc.cases]

text {*
  Also, case names are generated based on the old names
*}

end
