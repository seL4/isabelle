(*  Title:      HOL/Library/Executable_Set.thy
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Implementation of finite sets by lists *}

theory Executable_Set
imports Main Code_Set
begin

subsection {* Derived set operations *}

declare member [code] 

definition subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subset = op \<le>"

declare subset_def [symmetric, code unfold]

lemma [code]:
  "subset A B \<longleftrightarrow> (\<forall>x\<in>A. x \<in> B)"
  by (simp add: subset_def subset_eq)

definition eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [code del]: "eq_set = op ="

(* FIXME allow for Stefan's code generator:
declare set_eq_subset[code unfold]
*)

lemma [code]:
  "eq_set A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  by (simp add: eq_set_def set_eq)

declare inter [code]

declare Inter_image_eq [symmetric, code]
declare Union_image_eq [symmetric, code]


subsection {* Rewrites for primitive operations *}

declare List_Set.project_def [symmetric, code unfold]


subsection {* code generator setup *}

text {* eliminate popular infixes *}

ML {*
nonfix inter;
nonfix union;
nonfix subset;
*}

text {* type @{typ "'a fset"} *}

types_code
  fset ("(_/ list)")

consts_code
  Set ("_")

text {* primitive operations *}

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
  "flip f a b = f b a"

consts_code
  "Set.empty"         ("{*Code_Set.empty*}")
  "List_Set.is_empty" ("{*Code_Set.is_empty*}")
  "Set.insert"        ("{*Code_Set.insert*}")
  "List_Set.remove"   ("{*Code_Set.remove*}")
  "Set.image"         ("{*Code_Set.map*}")
  "List_Set.project"  ("{*Code_Set.filter*}")
  "Ball"              ("{*flip Code_Set.forall*}")
  "Bex"               ("{*flip Code_Set.exists*}")
  "op \<union>"              ("{*Code_Set.union*}")
  "op \<inter>"              ("{*Code_Set.inter*}")
  "op - \<Colon> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("{*flip subtract*}")
  "Set.Union"         ("{*Code_Set.union*}")
  "Set.Inter"         ("{*Code_Set.inter*}")
  fold                ("{*foldl o flip*}")

end