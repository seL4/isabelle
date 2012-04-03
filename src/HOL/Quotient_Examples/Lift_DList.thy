(*  Title:      HOL/Quotient_Examples/Lift_DList.thy
    Author:     Ondrej Kuncar
*)

theory Lift_DList
imports Main "~~/src/HOL/Library/Quotient_List"
begin

subsection {* The type of distinct lists *}

typedef (open) 'a dlist = "{xs::'a list. distinct xs}"
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
    have "list_all2 cr_dlist x y \<Longrightarrow> 
      List.map Abs_dlist x = y \<and> list_all2 (Lifting.invariant distinct) x x"
      unfolding list_all2_def cr_dlist_def by (induction x y rule: list_induct2') auto
  }
  note cr = this

  fix x :: "'a list list" and y :: "'a list list"
  assume a: "(list_all2 cr_dlist OO Lifting.invariant distinct OO (list_all2 cr_dlist)\<inverse>\<inverse>) x y"
  from a have l_x: "list_all2 (Lifting.invariant distinct) x x" by (auto simp add: cr)
  from a have l_y: "list_all2 (Lifting.invariant distinct) y y" by (auto simp add: cr)
  from a have m: "(Lifting.invariant distinct) (List.map Abs_dlist x) (List.map Abs_dlist y)" 
    by (auto simp add: cr)

  have "x = y" 
  proof -
    have m':"List.map Abs_dlist x = List.map Abs_dlist y" using m unfolding Lifting.invariant_def by simp
    have dist: "\<And>l. list_all2 (Lifting.invariant distinct) l l \<Longrightarrow> !x. x \<in> (set l) \<longrightarrow> distinct x"
      unfolding list_all2_def Lifting.invariant_def by (auto simp add: zip_same)
    from dist[OF l_x] dist[OF l_y] have "inj_on Abs_dlist (set x \<union> set y)" by (intro inj_onI) 
      (metis CollectI UnE Abs_dlist_inverse)
    with m' show ?thesis by (rule map_inj_on)
  qed
  then show "?thesis x y" unfolding Lifting.invariant_def by auto
qed

text {* We can export code: *}

export_code empty insert remove map filter null member length fold foldr concat in SML

end
