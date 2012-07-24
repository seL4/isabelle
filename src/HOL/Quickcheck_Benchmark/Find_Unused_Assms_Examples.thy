theory Find_Unused_Assms_Examples
imports Complex_Main
begin

section {* Arithmetics *}

declare [[quickcheck_finite_types = false]]

find_unused_assms Divides
find_unused_assms GCD
find_unused_assms RealDef
find_unused_assms RComplete

section {* Set Theory *}

declare [[quickcheck_finite_types = true]]

find_unused_assms Fun
find_unused_assms Relation
find_unused_assms Set
find_unused_assms Wellfounded

section {* Datatypes *}

find_unused_assms List
find_unused_assms Map

end
