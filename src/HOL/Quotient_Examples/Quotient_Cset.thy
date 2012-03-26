(*  Title:      HOL/Quotient_Examples/Quotient_Cset.thy
    Author:     Florian Haftmann, Alexander Krauss, TU Muenchen
*)

header {* A variant of theory Cset from Library, defined as a quotient *}

theory Quotient_Cset
imports Main "~~/src/HOL/Library/Quotient_Syntax"
begin

subsection {* Lifting *}

(*FIXME: quotient package requires a dedicated constant*)
definition set_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp]: "set_eq \<equiv> op ="

quotient_type 'a set = "'a Set.set" / "set_eq"
by (simp add: identity_equivp)

hide_type (open) set

subsection {* Operations *}

quotient_definition "member :: 'a => 'a Quotient_Cset.set => bool"
is "op \<in>" by simp
quotient_definition "Set :: ('a => bool) => 'a Quotient_Cset.set"
is Collect done
quotient_definition is_empty where "is_empty :: 'a Quotient_Cset.set \<Rightarrow> bool"
is Set.is_empty by simp 
quotient_definition insert where "insert :: 'a \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set"
is Set.insert by simp
quotient_definition remove where "remove :: 'a \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set"
is Set.remove by simp
quotient_definition map where "map :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> 'b Quotient_Cset.set"
is image by simp
quotient_definition filter where "filter :: ('a \<Rightarrow> bool) \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set"
is Set.project by simp
quotient_definition "forall :: 'a Quotient_Cset.set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
is Ball by simp
quotient_definition "exists :: 'a Quotient_Cset.set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
is Bex by simp
quotient_definition card where "card :: 'a Quotient_Cset.set \<Rightarrow> nat"
is Finite_Set.card by simp
quotient_definition set where "set :: 'a list => 'a Quotient_Cset.set"
is List.set done
quotient_definition subset where "subset :: 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> bool"
is "op \<subseteq> :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool" by simp
quotient_definition psubset where "psubset :: 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> bool"
is "op \<subset> :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool" by simp
quotient_definition inter where "inter :: 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set"
is "op \<inter> :: 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" by simp
quotient_definition union where "union :: 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set"
is "op \<union> :: 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" by simp
quotient_definition empty where "empty :: 'a Quotient_Cset.set"
is "{} :: 'a set" done
quotient_definition UNIV where "UNIV :: 'a Quotient_Cset.set"
is "Set.UNIV :: 'a set" done
quotient_definition uminus where "uminus :: 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set"
is "uminus_class.uminus :: 'a set \<Rightarrow> 'a set" by simp
quotient_definition minus where "minus :: 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set \<Rightarrow> 'a Quotient_Cset.set"
is "(op -) :: 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" by simp
quotient_definition Inf where "Inf :: ('a :: Inf) Quotient_Cset.set \<Rightarrow> 'a"
is "Inf_class.Inf :: ('a :: Inf) set \<Rightarrow> 'a" by simp
quotient_definition Sup where "Sup :: ('a :: Sup) Quotient_Cset.set \<Rightarrow> 'a"
is "Sup_class.Sup :: ('a :: Sup) set \<Rightarrow> 'a" by simp
quotient_definition UNION where "UNION :: 'a Quotient_Cset.set \<Rightarrow> ('a \<Rightarrow> 'b Quotient_Cset.set) \<Rightarrow> 'b Quotient_Cset.set"
is "Complete_Lattices.UNION :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" by simp

hide_const (open) is_empty insert remove map filter forall exists card
  set subset psubset inter union empty UNIV uminus minus Inf Sup UNION

hide_fact (open) is_empty_def insert_def remove_def map_def filter_def
  forall_def exists_def card_def set_def subset_def psubset_def
  inter_def union_def empty_def UNIV_def uminus_def minus_def Inf_def Sup_def
  UNION_eq

end
