(*  Title:      HOL/Quotient_Examples/Lift_DList.thy
    Author:     Ondrej Kuncar
*)

theory Lift_DList
imports Main
begin

subsection \<open>The type of distinct lists\<close>

typedef 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> {xs. distinct xs}" by simp
qed

setup_lifting type_definition_dlist

text \<open>Fundamental operations:\<close>

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

text \<open>Derived operations:\<close>

lift_definition null :: "'a dlist \<Rightarrow> bool" is List.null .

lift_definition member :: "'a dlist \<Rightarrow> 'a \<Rightarrow> bool" is List.member .

lift_definition length :: "'a dlist \<Rightarrow> nat" is List.length .

lift_definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" is List.fold .

lift_definition foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" is List.foldr .

lift_definition concat :: "'a dlist dlist \<Rightarrow> 'a dlist" is "remdups o List.concat" by auto

text \<open>We can export code:\<close>

export_code empty insert remove map filter null member length fold foldr concat in SML
  file_prefix dlist

end
