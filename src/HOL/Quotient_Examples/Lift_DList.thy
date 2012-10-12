(*  Title:      HOL/Quotient_Examples/Lift_DList.thy
    Author:     Ondrej Kuncar
*)

theory Lift_DList
imports Main "~~/src/HOL/Library/Quotient_List"
begin

subsection {* The type of distinct lists *}

typedef 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> {xs. distinct xs}" by simp
qed

setup_lifting type_definition_dlist

text {* Fundamental operations: *}

lift_definition empty :: "'a dlist" is "[]"
by simp
  
lift_definition insert :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" is List.insert
by simp

lift_definition remove :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" is List.remove1
by simp

lift_definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b dlist" is "\<lambda>f. remdups o List.map f"
by simp

lift_definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" is List.filter
by simp

text {* Derived operations: *}

lift_definition null :: "'a dlist \<Rightarrow> bool" is List.null
by simp

lift_definition member :: "'a dlist \<Rightarrow> 'a \<Rightarrow> bool" is List.member
by simp

lift_definition length :: "'a dlist \<Rightarrow> nat" is List.length
by simp

lift_definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" is List.fold
by simp

lift_definition foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" is List.foldr
by simp

lift_definition concat :: "'a dlist dlist \<Rightarrow> 'a dlist" is "remdups o List.concat"
proof -
  {
    fix x y
    have "list_all2 cr_dlist x y \<Longrightarrow> x = List.map list_of_dlist y"
      unfolding list_all2_def cr_dlist_def by (induction x y rule: list_induct2') auto
  }
  note cr = this
  fix x :: "'a list list" and y :: "'a list list"
  assume "(list_all2 cr_dlist OO Lifting.invariant distinct OO (list_all2 cr_dlist)\<inverse>\<inverse>) x y"
  then have "x = y" by (auto dest: cr simp add: Lifting.invariant_def)
  then show "?thesis x y" unfolding Lifting.invariant_def by auto
qed

text {* We can export code: *}

export_code empty insert remove map filter null member length fold foldr concat in SML

end
