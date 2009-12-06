(*  Title:      HOL/Library/Crude_Executable_Set.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A crude implementation of finite sets by lists -- avoid using this at any cost! *}

theory Crude_Executable_Set
imports List_Set
begin

declare mem_def [code del]
declare Collect_def [code del]
declare insert_code [code del]
declare vimage_code [code del]

subsection {* Set representation *}

setup {*
  Code.add_type_cmd "set"
*}

definition Set :: "'a list \<Rightarrow> 'a set" where
  [simp]: "Set = set"

definition Coset :: "'a list \<Rightarrow> 'a set" where
  [simp]: "Coset xs = - set xs"

setup {*
  Code.add_signature_cmd ("Set", "'a list \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("Coset", "'a list \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("set", "'a list \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("op \<in>", "'a \<Rightarrow> 'a set \<Rightarrow> bool")
*}

code_datatype Set Coset


subsection {* Basic operations *}

lemma [code]:
  "set xs = Set (remdups xs)"
  by simp

lemma [code]:
  "x \<in> Set xs \<longleftrightarrow> member x xs"
  "x \<in> Coset xs \<longleftrightarrow> \<not> member x xs"
  by (simp_all add: mem_iff)

definition is_empty :: "'a set \<Rightarrow> bool" where
  [simp]: "is_empty A \<longleftrightarrow> A = {}"

lemma [code_inline]:
  "A = {} \<longleftrightarrow> is_empty A"
  by simp

definition empty :: "'a set" where
  [simp]: "empty = {}"

lemma [code_inline]:
  "{} = empty"
  by simp

setup {*
  Code.add_signature_cmd ("is_empty", "'a set \<Rightarrow> bool")
  #> Code.add_signature_cmd ("empty", "'a set")
  #> Code.add_signature_cmd ("insert", "'a \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("List_Set.remove", "'a \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("image", "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set")
  #> Code.add_signature_cmd ("List_Set.project", "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("Ball", "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool")
  #> Code.add_signature_cmd ("Bex", "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool")
  #> Code.add_signature_cmd ("card", "'a set \<Rightarrow> nat")
*}

lemma is_empty_Set [code]:
  "is_empty (Set xs) \<longleftrightarrow> null xs"
  by (simp add: empty_null)

lemma empty_Set [code]:
  "empty = Set []"
  by simp

lemma insert_Set [code]:
  "insert x (Set xs) = Set (List_Set.insert x xs)"
  "insert x (Coset xs) = Coset (remove_all x xs)"
  by (simp_all add: insert_set insert_set_compl)

lemma remove_Set [code]:
  "remove x (Set xs) = Set (remove_all x xs)"
  "remove x (Coset xs) = Coset (List_Set.insert x xs)"
  by (simp_all add:remove_set remove_set_compl)

lemma image_Set [code]:
  "image f (Set xs) = Set (remdups (map f xs))"
  by simp

lemma project_Set [code]:
  "project P (Set xs) = Set (filter P xs)"
  by (simp add: project_set)

lemma Ball_Set [code]:
  "Ball (Set xs) P \<longleftrightarrow> list_all P xs"
  by (simp add: ball_set)

lemma Bex_Set [code]:
  "Bex (Set xs) P \<longleftrightarrow> list_ex P xs"
  by (simp add: bex_set)

lemma card_Set [code]:
  "card (Set xs) = length (remdups xs)"
proof -
  have "card (set (remdups xs)) = length (remdups xs)"
    by (rule distinct_card) simp
  then show ?thesis by simp
qed


subsection {* Derived operations *}

definition set_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [simp]: "set_eq = op ="

lemma [code_inline]:
  "op = = set_eq"
  by simp

definition subset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [simp]: "subset_eq = op \<subseteq>"

lemma [code_inline]:
  "op \<subseteq> = subset_eq"
  by simp

definition subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [simp]: "subset = op \<subset>"

lemma [code_inline]:
  "op \<subset> = subset"
  by simp

setup {*
  Code.add_signature_cmd ("set_eq", "'a set \<Rightarrow> 'a set \<Rightarrow> bool")
  #> Code.add_signature_cmd ("subset_eq", "'a set \<Rightarrow> 'a set \<Rightarrow> bool")
  #> Code.add_signature_cmd ("subset", "'a set \<Rightarrow> 'a set \<Rightarrow> bool")
*}

lemma set_eq_subset_eq [code]:
  "set_eq A B \<longleftrightarrow> subset_eq A B \<and> subset_eq B A"
  by auto

lemma subset_eq_forall [code]:
  "subset_eq A B \<longleftrightarrow> (\<forall>x\<in>A. x \<in> B)"
  by (simp add: subset_eq)

lemma subset_subset_eq [code]:
  "subset A B \<longleftrightarrow> subset_eq A B \<and> \<not> subset_eq B A"
  by (simp add: subset)


subsection {* Functorial operations *}

definition inter :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  [simp]: "inter = op \<inter>"

lemma [code_inline]:
  "op \<inter> = inter"
  by simp

definition subtract :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  [simp]: "subtract A B = B - A"

lemma [code_inline]:
  "B - A = subtract A B"
  by simp

definition union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  [simp]: "union = op \<union>"

lemma [code_inline]:
  "op \<union> = union"
  by simp

definition Inf :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp]: "Inf = Complete_Lattice.Inf"

lemma [code_inline]:
  "Complete_Lattice.Inf = Inf"
  by simp

definition Sup :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp]: "Sup = Complete_Lattice.Sup"

lemma [code_inline]:
  "Complete_Lattice.Sup = Sup"
  by simp

definition Inter :: "'a set set \<Rightarrow> 'a set" where
  [simp]: "Inter = Inf"

lemma [code_inline]:
  "Inf = Inter"
  by simp

definition Union :: "'a set set \<Rightarrow> 'a set" where
  [simp]: "Union = Sup"

lemma [code_inline]:
  "Sup = Union"
  by simp

setup {*
  Code.add_signature_cmd ("inter", "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("subtract", "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("union", "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("Inf", "'a set \<Rightarrow> 'a")
  #> Code.add_signature_cmd ("Sup", "'a set \<Rightarrow> 'a")
  #> Code.add_signature_cmd ("Inter", "'a set set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("Union", "'a set set \<Rightarrow> 'a set")
*}

lemma inter_project [code]:
  "inter A (Set xs) = Set (List.filter (\<lambda>x. x \<in> A) xs)"
  "inter A (Coset xs) = foldl (\<lambda>A x. remove x A) A xs"
  by (simp add: inter project_def, simp add: Diff_eq [symmetric] minus_set)

lemma subtract_remove [code]:
  "subtract (Set xs) A = foldl (\<lambda>A x. remove x A) A xs"
  "subtract (Coset xs) A = Set (List.filter (\<lambda>x. x \<in> A) xs)"
  by (auto simp add: minus_set)

lemma union_insert [code]:
  "union (Set xs) A = foldl (\<lambda>A x. insert x A) A xs"
  "union (Coset xs) A = Coset (List.filter (\<lambda>x. x \<notin> A) xs)"
  by (auto simp add: union_set)

lemma Inf_inf [code]:
  "Inf (Set xs) = foldl inf (top :: 'a::complete_lattice) xs"
  "Inf (Coset []) = (bot :: 'a::complete_lattice)"
  by (simp_all add: Inf_UNIV Inf_set_fold)

lemma Sup_sup [code]:
  "Sup (Set xs) = foldl sup (bot :: 'a::complete_lattice) xs"
  "Sup (Coset []) = (top :: 'a::complete_lattice)"
  by (simp_all add: Sup_UNIV Sup_set_fold)

lemma Inter_inter [code]:
  "Inter (Set xs) = foldl inter (Coset []) xs"
  "Inter (Coset []) = empty"
  unfolding Inter_def Inf_inf by simp_all

lemma Union_union [code]:
  "Union (Set xs) = foldl union empty xs"
  "Union (Coset []) = Coset []"
  unfolding Union_def Sup_sup by simp_all

hide (open) const is_empty empty remove
  set_eq subset_eq subset inter union subtract Inf Sup Inter Union

end
