(*  Title:      HOL/Library/Executable_Set.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A thin compatibility layer *}

theory Executable_Set
imports More_Set
begin

abbreviation Set :: "'a list \<Rightarrow> 'a set" where
  "Set \<equiv> set"

abbreviation Coset :: "'a list \<Rightarrow> 'a set" where
  "Coset \<equiv> More_Set.coset"

end
