(*  Title:      HOL/Quotient_Examples/Lift_Set.thy
    Author:     Lukas Bulwahn and Ondrej Kuncar
*)

header {* Example of lifting definitions with the quotient infrastructure *}

theory Lift_Set
imports Main
begin

definition set where "set = (UNIV :: ('a \<Rightarrow> bool) set)"

typedef (open) 'a set = "set :: ('a \<Rightarrow> bool) set"
  morphisms member Set
  unfolding set_def by auto

setup_lifting type_definition_set[unfolded set_def]

text {* Now, we can employ quotient_definition to lift definitions. *}

quotient_definition empty where "empty :: 'a set"
is "bot :: 'a \<Rightarrow> bool" done

term "Lift_Set.empty"
thm Lift_Set.empty_def

definition insertp :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "insertp x P y \<longleftrightarrow> y = x \<or> P y"

quotient_definition insert where "insert :: 'a => 'a set => 'a set"
is insertp done

term "Lift_Set.insert"
thm Lift_Set.insert_def

export_code empty insert in SML

end

