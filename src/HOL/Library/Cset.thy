
(* Author: Florian Haftmann, TU Muenchen *)

header {* A dedicated set type which is executable on its finite part *}

theory Cset
imports Main
begin

subsection {* Lifting *}

typedef (open) 'a set = "UNIV :: 'a set set"
  morphisms set_of Set by rule+
hide_type (open) set

lemma set_of_Set [simp]:
  "set_of (Set A) = A"
  by (rule Set_inverse) rule

lemma Set_set_of [simp]:
  "Set (set_of A) = A"
  by (fact set_of_inverse)

definition member :: "'a Cset.set \<Rightarrow> 'a \<Rightarrow> bool" where
  "member A x \<longleftrightarrow> x \<in> set_of A"

lemma member_Set [simp]:
  "member (Set A) x \<longleftrightarrow> x \<in> A"
  by (simp add: member_def)

lemma Set_inject [simp]:
  "Set A = Set B \<longleftrightarrow> A = B"
  by (simp add: Set_inject)

lemma set_eq_iff:
  "A = B \<longleftrightarrow> member A = member B"
  by (auto simp add: fun_eq_iff set_of_inject [symmetric] member_def)
hide_fact (open) set_eq_iff

lemma set_eqI:
  "member A = member B \<Longrightarrow> A = B"
  by (simp add: Cset.set_eq_iff)
hide_fact (open) set_eqI

subsection {* Lattice instantiation *}

instantiation Cset.set :: (type) boolean_algebra
begin

definition less_eq_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "A \<le> B \<longleftrightarrow> set_of A \<subseteq> set_of B"

definition less_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "A < B \<longleftrightarrow> set_of A \<subset> set_of B"

definition inf_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "inf A B = Set (set_of A \<inter> set_of B)"

definition sup_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "sup A B = Set (set_of A \<union> set_of B)"

definition bot_set :: "'a Cset.set" where
  [simp]: "bot = Set {}"

definition top_set :: "'a Cset.set" where
  [simp]: "top = Set UNIV"

definition uminus_set :: "'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "- A = Set (- (set_of A))"

definition minus_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "A - B = Set (set_of A - set_of B)"

instance proof
qed (auto intro!: Cset.set_eqI simp add: member_def)

end

instantiation Cset.set :: (type) complete_lattice
begin

definition Inf_set :: "'a Cset.set set \<Rightarrow> 'a Cset.set" where
  [simp]: "Inf_set As = Set (Inf (image set_of As))"

definition Sup_set :: "'a Cset.set set \<Rightarrow> 'a Cset.set" where
  [simp]: "Sup_set As = Set (Sup (image set_of As))"

instance proof
qed (auto simp add: le_fun_def)

end

instance Cset.set :: (type) complete_boolean_algebra proof
qed (unfold INF_def SUP_def, auto)


subsection {* Basic operations *}

abbreviation empty :: "'a Cset.set" where "empty \<equiv> bot"
hide_const (open) empty

abbreviation UNIV :: "'a Cset.set" where "UNIV \<equiv> top"
hide_const (open) UNIV

definition is_empty :: "'a Cset.set \<Rightarrow> bool" where
  [simp]: "is_empty A \<longleftrightarrow> Set.is_empty (set_of A)"

definition insert :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "insert x A = Set (Set.insert x (set_of A))"

definition remove :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "remove x A = Set (Set.remove x (set_of A))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Cset.set \<Rightarrow> 'b Cset.set" where
  [simp]: "map f A = Set (image f (set_of A))"

enriched_type map: map
  by (simp_all add: fun_eq_iff image_compose)

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "filter P A = Set (Set.project P (set_of A))"

definition forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "forall P A \<longleftrightarrow> Ball (set_of A) P"

definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "exists P A \<longleftrightarrow> Bex (set_of A) P"

definition card :: "'a Cset.set \<Rightarrow> nat" where
  [simp]: "card A = Finite_Set.card (set_of A)"
  
context complete_lattice
begin

definition Infimum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Infimum A = Inf (set_of A)"

definition Supremum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Supremum A = Sup (set_of A)"

end

subsection {* More operations *}

text {* conversion from @{typ "'a list"} *}

definition set :: "'a list \<Rightarrow> 'a Cset.set" where
  "set xs = Set (List.set xs)"
hide_const (open) set

definition coset :: "'a list \<Rightarrow> 'a Cset.set" where
  "coset xs = Set (- List.set xs)"
hide_const (open) coset

text {* conversion from @{typ "'a Predicate.pred"} *}

definition pred_of_cset :: "'a Cset.set \<Rightarrow> 'a Predicate.pred" where
  [code del]: "pred_of_cset = Predicate.Pred \<circ> Cset.member"

definition of_pred :: "'a Predicate.pred \<Rightarrow> 'a Cset.set" where
  "of_pred = Cset.Set \<circ> Collect \<circ> Predicate.eval"

definition of_seq :: "'a Predicate.seq \<Rightarrow> 'a Cset.set" where 
  "of_seq = of_pred \<circ> Predicate.pred_of_seq"

text {* monad operations *}

definition single :: "'a \<Rightarrow> 'a Cset.set" where
  "single a = Set {a}"

definition bind :: "'a Cset.set \<Rightarrow> ('a \<Rightarrow> 'b Cset.set) \<Rightarrow> 'b Cset.set" (infixl "\<guillemotright>=" 70) where
  "A \<guillemotright>= f = (SUP x : set_of A. f x)"


subsection {* Simplified simprules *}

lemma empty_simp [simp]: "member Cset.empty = bot"
  by (simp add: fun_eq_iff bot_apply)

lemma UNIV_simp [simp]: "member Cset.UNIV = top"
  by (simp add: fun_eq_iff top_apply)

lemma is_empty_simp [simp]:
  "is_empty A \<longleftrightarrow> set_of A = {}"
  by (simp add: Set.is_empty_def)
declare is_empty_def [simp del]

lemma remove_simp [simp]:
  "remove x A = Set (set_of A - {x})"
  by (simp add: Set.remove_def)
declare remove_def [simp del]

lemma filter_simp [simp]:
  "filter P A = Set {x \<in> set_of A. P x}"
  by (simp add: Set.project_def)
declare filter_def [simp del]

lemma set_of_set [simp]:
  "set_of (Cset.set xs) = set xs"
  by (simp add: set_def)
hide_fact (open) set_def

lemma member_set [simp]:
  "member (Cset.set xs) = (\<lambda>x. x \<in> set xs)"
  by (simp add: fun_eq_iff member_def)
hide_fact (open) member_set

lemma set_of_coset [simp]:
  "set_of (Cset.coset xs) = - set xs"
  by (simp add: coset_def)
hide_fact (open) coset_def

lemma member_coset [simp]:
  "member (Cset.coset xs) = (\<lambda>x. x \<in> - set xs)"
  by (simp add: fun_eq_iff member_def)
hide_fact (open) member_coset

lemma set_simps [simp]:
  "Cset.set [] = Cset.empty"
  "Cset.set (x # xs) = insert x (Cset.set xs)"
by(simp_all add: Cset.set_def)

lemma member_SUP [simp]:
  "member (SUPR A f) = SUPR A (member \<circ> f)"
  by (auto simp add: fun_eq_iff SUP_apply member_def, unfold SUP_def, auto)

lemma member_bind [simp]:
  "member (P \<guillemotright>= f) = SUPR (set_of P) (member \<circ> f)"
  by (simp add: bind_def Cset.set_eq_iff)

lemma member_single [simp]:
  "member (single a) = (\<lambda>x. x \<in> {a})"
  by (simp add: single_def fun_eq_iff)

lemma single_sup_simps [simp]:
  shows single_sup: "sup (single a) A = insert a A"
  and sup_single: "sup A (single a) = insert a A"
  by (auto simp add: Cset.set_eq_iff single_def)

lemma single_bind [simp]:
  "single a \<guillemotright>= B = B a"
  by (simp add: Cset.set_eq_iff SUP_insert single_def)

lemma bind_bind:
  "(A \<guillemotright>= B) \<guillemotright>= C = A \<guillemotright>= (\<lambda>x. B x \<guillemotright>= C)"
  by (simp add: bind_def, simp only: SUP_def image_image, simp)
 
lemma bind_single [simp]:
  "A \<guillemotright>= single = A"
  by (simp add: Cset.set_eq_iff SUP_apply fun_eq_iff single_def member_def)

lemma bind_const: "A \<guillemotright>= (\<lambda>_. B) = (if Cset.is_empty A then Cset.empty else B)"
  by (auto simp add: Cset.set_eq_iff fun_eq_iff)

lemma empty_bind [simp]:
  "Cset.empty \<guillemotright>= f = Cset.empty"
  by (simp add: Cset.set_eq_iff fun_eq_iff bot_apply)

lemma member_of_pred [simp]:
  "member (of_pred P) = (\<lambda>x. x \<in> {x. Predicate.eval P x})"
  by (simp add: of_pred_def fun_eq_iff)

lemma member_of_seq [simp]:
  "member (of_seq xq) = (\<lambda>x. x \<in> {x. Predicate.member xq x})"
  by (simp add: of_seq_def eval_member)

lemma eval_pred_of_cset [simp]: 
  "Predicate.eval (pred_of_cset A) = Cset.member A"
  by (simp add: pred_of_cset_def)

subsection {* Default implementations *}

lemma set_code [code]:
  "Cset.set = (\<lambda>xs. fold insert xs Cset.empty)"
proof (rule ext, rule Cset.set_eqI)
  fix xs :: "'a list"
  show "member (Cset.set xs) = member (fold insert xs Cset.empty)"
    by (simp add: fold_commute_apply [symmetric, where ?h = Set and ?g = Set.insert]
      fun_eq_iff Cset.set_def union_set_fold [symmetric])
qed

lemma single_code [code]:
  "single a = insert a Cset.empty"
  by (simp add: Cset.single_def)

lemma compl_set [simp]:
  "- Cset.set xs = Cset.coset xs"
  by (simp add: Cset.set_def Cset.coset_def)

lemma compl_coset [simp]:
  "- Cset.coset xs = Cset.set xs"
  by (simp add: Cset.set_def Cset.coset_def)

lemma inter_project:
  "inf A (Cset.set xs) = Cset.set (List.filter (Cset.member A) xs)"
  "inf A (Cset.coset xs) = foldr Cset.remove xs A"
proof -
  show "inf A (Cset.set xs) = Cset.set (List.filter (member A) xs)"
    by (simp add: project_def Cset.set_def member_def) auto
  have *: "\<And>x::'a. Cset.remove = (\<lambda>x. Set \<circ> Set.remove x \<circ> set_of)"
    by (simp add: fun_eq_iff Set.remove_def)
  have "set_of \<circ> fold (\<lambda>x. Set \<circ> Set.remove x \<circ> set_of) xs =
    fold Set.remove xs \<circ> set_of"
    by (rule fold_commute) (simp add: fun_eq_iff)
  then have "fold Set.remove xs (set_of A) = 
    set_of (fold (\<lambda>x. Set \<circ> Set.remove x \<circ> set_of) xs A)"
    by (simp add: fun_eq_iff)
  then have "inf A (Cset.coset xs) = fold Cset.remove xs A"
    by (simp add: Diff_eq [symmetric] minus_set_fold *)
  moreover have "\<And>x y :: 'a. Cset.remove y \<circ> Cset.remove x = Cset.remove x \<circ> Cset.remove y"
    by (auto simp add: Set.remove_def *)
  ultimately show "inf A (Cset.coset xs) = foldr Cset.remove xs A"
    by (simp add: foldr_fold)
qed

lemma union_insert:
  "sup (Cset.set xs) A = foldr Cset.insert xs A"
  "sup (Cset.coset xs) A = Cset.coset (List.filter (Not \<circ> member A) xs)"
proof -
  have *: "\<And>x::'a. Cset.insert = (\<lambda>x. Set \<circ> Set.insert x \<circ> set_of)"
    by (simp add: fun_eq_iff)
  have "set_of \<circ> fold (\<lambda>x. Set \<circ> Set.insert x \<circ> set_of) xs =
    fold Set.insert xs \<circ> set_of"
    by (rule fold_commute) (simp add: fun_eq_iff)
  then have "fold Set.insert xs (set_of A) =
    set_of (fold (\<lambda>x. Set \<circ> Set.insert x \<circ> set_of) xs A)"
    by (simp add: fun_eq_iff)
  then have "sup (Cset.set xs) A = fold Cset.insert xs A"
    by (simp add: union_set_fold *)
  moreover have "\<And>x y :: 'a. Cset.insert y \<circ> Cset.insert x = Cset.insert x \<circ> Cset.insert y"
    by (auto simp add: *)
  ultimately show "sup (Cset.set xs) A = foldr Cset.insert xs A"
    by (simp add: foldr_fold)
  show "sup (Cset.coset xs) A = Cset.coset (List.filter (Not \<circ> member A) xs)"
    by (auto simp add: Cset.coset_def Cset.member_def)
qed

lemma subtract_remove:
  "A - Cset.set xs = foldr Cset.remove xs A"
  "A - Cset.coset xs = Cset.set (List.filter (member A) xs)"
  by (simp_all only: diff_eq compl_set compl_coset inter_project)

context complete_lattice
begin

lemma Infimum_inf:
  "Infimum (Cset.set As) = foldr inf As top"
  "Infimum (Cset.coset []) = bot"
  by (simp_all add: Inf_set_foldr)

lemma Supremum_sup:
  "Supremum (Cset.set As) = foldr sup As bot"
  "Supremum (Cset.coset []) = top"
  by (simp_all add: Sup_set_foldr)

end

lemma of_pred_code [code]:
  "of_pred (Predicate.Seq f) = (case f () of
     Predicate.Empty \<Rightarrow> Cset.empty
   | Predicate.Insert x P \<Rightarrow> Cset.insert x (of_pred P)
   | Predicate.Join P xq \<Rightarrow> sup (of_pred P) (of_seq xq))"
  by (auto split: seq.split simp add: Predicate.Seq_def of_pred_def Cset.set_eq_iff sup_apply eval_member [symmetric] member_def [symmetric])

lemma of_seq_code [code]:
  "of_seq Predicate.Empty = Cset.empty"
  "of_seq (Predicate.Insert x P) = Cset.insert x (of_pred P)"
  "of_seq (Predicate.Join P xq) = sup (of_pred P) (of_seq xq)"
  by (auto simp add: of_seq_def of_pred_def Cset.set_eq_iff)

lemma bind_set:
  "Cset.bind (Cset.set xs) f = fold (sup \<circ> f) xs (Cset.set [])"
  by (simp add: Cset.bind_def SUP_set_fold)
hide_fact (open) bind_set

lemma pred_of_cset_set:
  "pred_of_cset (Cset.set xs) = foldr sup (List.map Predicate.single xs) bot"
proof -
  have "pred_of_cset (Cset.set xs) = Predicate.Pred (\<lambda>x. x \<in> set xs)"
    by (simp add: Cset.pred_of_cset_def)
  moreover have "foldr sup (List.map Predicate.single xs) bot = \<dots>"
    by (induct xs) (auto simp add: bot_pred_def intro: pred_eqI)
  ultimately show ?thesis by simp
qed
hide_fact (open) pred_of_cset_set

no_notation bind (infixl "\<guillemotright>=" 70)

hide_const (open) is_empty insert remove map filter forall exists card
  Inter Union bind single of_pred of_seq

hide_fact (open) set_def pred_of_cset_def of_pred_def of_seq_def single_def 
  bind_def empty_simp UNIV_simp set_simps member_bind 
  member_single single_sup_simps single_sup sup_single single_bind
  bind_bind bind_single bind_const empty_bind member_of_pred member_of_seq
  eval_pred_of_cset set_code single_code of_pred_code of_seq_code

end
