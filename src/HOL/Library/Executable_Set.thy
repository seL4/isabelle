(*  Title:      HOL/Library/Executable_Set.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A crude implementation of finite sets by lists -- avoid using this at any cost! *}

theory Executable_Set
imports More_Set
begin

text {*
  This is just an ad-hoc hack which will rarely give you what you want.
  For the moment, whenever you need executable sets, consider using
  type @{text Cset.set} from theory @{text Cset}.
*}

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

consts_code
  Coset ("\<module>Coset")
  Set ("\<module>Set")
attach {*
  datatype 'a set = Set of 'a list | Coset of 'a list;
*} -- {* This assumes that there won't be a @{text Coset} without a @{text Set} *}


subsection {* Basic operations *}

lemma [code]:
  "set xs = Set (remdups xs)"
  by simp

lemma [code]:
  "x \<in> Set xs \<longleftrightarrow> List.member xs x"
  "x \<in> Coset xs \<longleftrightarrow> \<not> List.member xs x"
  by (simp_all add: member_def)

definition is_empty :: "'a set \<Rightarrow> bool" where
  [simp]: "is_empty A \<longleftrightarrow> A = {}"

lemma [code_unfold]:
  "A = {} \<longleftrightarrow> is_empty A"
  by simp

definition empty :: "'a set" where
  [simp]: "empty = {}"

lemma [code_unfold]:
  "{} = empty"
  by simp

lemma [code_unfold, code_inline del]:
  "empty = Set []"
  by simp -- {* Otherwise @{text \<eta>}-expansion produces funny things. *}

setup {*
  Code.add_signature_cmd ("is_empty", "'a set \<Rightarrow> bool")
  #> Code.add_signature_cmd ("empty", "'a set")
  #> Code.add_signature_cmd ("insert", "'a \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("More_Set.remove", "'a \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("image", "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set")
  #> Code.add_signature_cmd ("More_Set.project", "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set")
  #> Code.add_signature_cmd ("Ball", "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool")
  #> Code.add_signature_cmd ("Bex", "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool")
  #> Code.add_signature_cmd ("card", "'a set \<Rightarrow> nat")
*}

lemma is_empty_Set [code]:
  "is_empty (Set xs) \<longleftrightarrow> List.null xs"
  by (simp add: null_def)

lemma empty_Set [code]:
  "empty = Set []"
  by simp

lemma insert_Set [code]:
  "insert x (Set xs) = Set (List.insert x xs)"
  "insert x (Coset xs) = Coset (removeAll x xs)"
  by simp_all

lemma remove_Set [code]:
  "remove x (Set xs) = Set (removeAll x xs)"
  "remove x (Coset xs) = Coset (List.insert x xs)"
  by (auto simp add: remove_def)

lemma image_Set [code]:
  "image f (Set xs) = Set (remdups (map f xs))"
  by simp

lemma project_Set [code]:
  "project P (Set xs) = Set (filter P xs)"
  by (simp add: project_set)

lemma Ball_Set [code]:
  "Ball (Set xs) P \<longleftrightarrow> list_all P xs"
  by (simp add: list_all_iff)

lemma Bex_Set [code]:
  "Bex (Set xs) P \<longleftrightarrow> list_ex P xs"
  by (simp add: list_ex_iff)

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

lemma [code_unfold]:
  "op = = set_eq"
  by simp

definition subset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [simp]: "subset_eq = op \<subseteq>"

lemma [code_unfold]:
  "op \<subseteq> = subset_eq"
  by simp

definition subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  [simp]: "subset = op \<subset>"

lemma [code_unfold]:
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

lemma [code_unfold]:
  "op \<inter> = inter"
  by simp

definition subtract :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  [simp]: "subtract A B = B - A"

lemma [code_unfold]:
  "B - A = subtract A B"
  by simp

definition union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  [simp]: "union = op \<union>"

lemma [code_unfold]:
  "op \<union> = union"
  by simp

definition Inf :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp]: "Inf = Complete_Lattices.Inf"

lemma [code_unfold]:
  "Complete_Lattices.Inf = Inf"
  by simp

definition Sup :: "'a::complete_lattice set \<Rightarrow> 'a" where
  [simp]: "Sup = Complete_Lattices.Sup"

lemma [code_unfold]:
  "Complete_Lattices.Sup = Sup"
  by simp

definition Inter :: "'a set set \<Rightarrow> 'a set" where
  [simp]: "Inter = Inf"

lemma [code_unfold]:
  "Inf = Inter"
  by simp

definition Union :: "'a set set \<Rightarrow> 'a set" where
  [simp]: "Union = Sup"

lemma [code_unfold]:
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
  "inter A (Coset xs) = foldr remove xs A"
  by (simp add: inter project_def) (simp add: Diff_eq [symmetric] minus_set_foldr)

lemma subtract_remove [code]:
  "subtract (Set xs) A = foldr remove xs A"
  "subtract (Coset xs) A = Set (List.filter (\<lambda>x. x \<in> A) xs)"
  by (auto simp add: minus_set_foldr)

lemma union_insert [code]:
  "union (Set xs) A = foldr insert xs A"
  "union (Coset xs) A = Coset (List.filter (\<lambda>x. x \<notin> A) xs)"
  by (auto simp add: union_set_foldr)

lemma Inf_inf [code]:
  "Inf (Set xs) = foldr inf xs (top :: 'a::complete_lattice)"
  "Inf (Coset []) = (bot :: 'a::complete_lattice)"
  by (simp_all add: Inf_set_foldr)

lemma Sup_sup [code]:
  "Sup (Set xs) = foldr sup xs (bot :: 'a::complete_lattice)"
  "Sup (Coset []) = (top :: 'a::complete_lattice)"
  by (simp_all add: Sup_set_foldr)

lemma Inter_inter [code]:
  "Inter (Set xs) = foldr inter xs (Coset [])"
  "Inter (Coset []) = empty"
  unfolding Inter_def Inf_inf by simp_all

lemma Union_union [code]:
  "Union (Set xs) = foldr union xs empty"
  "Union (Coset []) = Coset []"
  unfolding Union_def Sup_sup by simp_all

hide_const (open) is_empty empty remove
  set_eq subset_eq subset inter union subtract Inf Sup Inter Union


subsection {* Operations on relations *}

text {* Initially contributed by Tjark Weber. *}

lemma [code]:
  "Domain r = fst ` r"
  by (fact Domain_fst)

lemma [code]:
  "Range r = snd ` r"
  by (fact Range_snd)

lemma [code]:
  "trans r \<longleftrightarrow> (\<forall>(x, y1) \<in> r. \<forall>(y2, z) \<in> r. y1 = y2 \<longrightarrow> (x, z) \<in> r)"
  by (fact trans_join)

lemma [code]:
  "irrefl r \<longleftrightarrow> (\<forall>(x, y) \<in> r. x \<noteq> y)"
  by (fact irrefl_distinct)

lemma [code]:
  "acyclic r \<longleftrightarrow> irrefl (r^+)"
  by (fact acyclic_irrefl)

lemma [code]:
  "More_Set.product (Set xs) (Set ys) = Set [(x, y). x \<leftarrow> xs, y \<leftarrow> ys]"
  by (unfold Set_def) (fact product_code)

lemma [code]:
  "Id_on (Set xs) = Set [(x, x). x \<leftarrow> xs]"
  by (unfold Set_def) (fact Id_on_set)

lemma [code]:
  "Set xys O Set yzs = Set ([(fst xy, snd yz). xy \<leftarrow> xys, yz \<leftarrow> yzs, snd xy = fst yz])"
  by (unfold Set_def) (fact set_rel_comp)

lemma [code]:
  "wf (Set xs) = acyclic (Set xs)"
  by (unfold Set_def) (fact wf_set)

end
