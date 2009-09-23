(*  Title:      HOL/Library/Executable_Set.thy
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Implementation of finite sets by lists *}

theory Executable_Set
imports Main Fset
begin

subsection {* Preprocessor setup *}

declare member [code] 

definition subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subset = op \<le>"

declare subset_def [symmetric, code_unfold]

lemma [code]:
  "subset A B \<longleftrightarrow> (\<forall>x\<in>A. x \<in> B)"
  by (simp add: subset_def subset_eq)

definition eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [code del]: "eq_set = op ="

(*declare eq_set_def [symmetric, code_unfold]*)

lemma [code]:
  "eq_set A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  by (simp add: eq_set_def set_eq)

declare inter [code]

declare Inter_image_eq [symmetric, code_unfold]
declare Union_image_eq [symmetric, code_unfold]

declare List_Set.project_def [symmetric, code_unfold]

definition Inter :: "'a set set \<Rightarrow> 'a set" where
  "Inter = Complete_Lattice.Inter"

declare Inter_def [symmetric, code_unfold]

definition Union :: "'a set set \<Rightarrow> 'a set" where
  "Union = Complete_Lattice.Union"

declare Union_def [symmetric, code_unfold]


subsection {* Code generator setup *}

ML {*
nonfix inter;
nonfix union;
nonfix subset;
*}

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
  "flip f a b = f b a"

types_code
  fset ("(_/ \<module>fset)")
attach {*
datatype 'a fset = Set of 'a list;
*}

consts_code
  Set ("\<module>Set")

consts_code
  "Set.empty"         ("{*Fset.empty*}")
  "List_Set.is_empty" ("{*Fset.is_empty*}")
  "Set.insert"        ("{*Fset.insert*}")
  "List_Set.remove"   ("{*Fset.remove*}")
  "Set.image"         ("{*Fset.map*}")
  "List_Set.project"  ("{*Fset.filter*}")
  "Ball"              ("{*flip Fset.forall*}")
  "Bex"               ("{*flip Fset.exists*}")
  "op \<union>"              ("{*Fset.union*}")
  "op \<inter>"              ("{*Fset.inter*}")
  "op - \<Colon> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("{*flip Fset.subtract*}")
  "Union"             ("{*Fset.Union*}")
  "Inter"             ("{*Fset.Inter*}")
  card                ("{*Fset.card*}")
  fold                ("{*foldl o flip*}")

hide (open) const subset eq_set Inter Union flip

end