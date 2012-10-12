(*  Title:      HOL/Quotient_Examples/Lift_Set.thy
    Author:     Lukas Bulwahn and Ondrej Kuncar
*)

header {* Example of lifting definitions with the lifting infrastructure *}

theory Lift_Set
imports Main
begin

definition set where "set = (UNIV :: ('a \<Rightarrow> bool) set)"

typedef 'a set = "set :: ('a \<Rightarrow> bool) set"
  morphisms member Set
  unfolding set_def by auto

setup_lifting type_definition_set[unfolded set_def]

text {* Now, we can employ lift_definition to lift definitions. *}

lift_definition empty :: "'a set" is "bot :: 'a \<Rightarrow> bool" done

term "Lift_Set.empty"
thm Lift_Set.empty_def

lift_definition insert :: "'a => 'a set => 'a set" is "\<lambda> x P y. y = x \<or> P y" done 

term "Lift_Set.insert"
thm Lift_Set.insert_def

export_code empty insert in SML

end

