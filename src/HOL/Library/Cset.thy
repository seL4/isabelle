
(* Author: Florian Haftmann, TU Muenchen *)

header {* A dedicated set type which is executable on its finite part *}

theory Cset
imports More_Set More_List
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

lemma member_set_of:
  "set_of = member"
  by (rule ext)+ (simp add: member_def mem_def)

lemma member_Set [simp]:
  "member (Set A) x \<longleftrightarrow> x \<in> A"
  by (simp add: member_def)

lemma Set_inject [simp]:
  "Set A = Set B \<longleftrightarrow> A = B"
  by (simp add: Set_inject)

lemma set_eq_iff:
  "A = B \<longleftrightarrow> member A = member B"
  by (auto simp add: fun_eq_iff set_of_inject [symmetric] member_def mem_def)
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
qed (auto intro!: Cset.set_eqI simp add: member_def mem_def)

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
  [simp]: "is_empty A \<longleftrightarrow> More_Set.is_empty (set_of A)"

definition insert :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "insert x A = Set (Set.insert x (set_of A))"

definition remove :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "remove x A = Set (More_Set.remove x (set_of A))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Cset.set \<Rightarrow> 'b Cset.set" where
  [simp]: "map f A = Set (image f (set_of A))"

enriched_type map: map
  by (simp_all add: fun_eq_iff image_compose)

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "filter P A = Set (More_Set.project P (set_of A))"

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
  by (simp add: More_Set.is_empty_def)
declare is_empty_def [simp del]

lemma remove_simp [simp]:
  "remove x A = Set (set_of A - {x})"
  by (simp add: More_Set.remove_def)
declare remove_def [simp del]

lemma filter_simp [simp]:
  "filter P A = Set {x \<in> set_of A. P x}"
  by (simp add: More_Set.project_def)
declare filter_def [simp del]

lemma set_of_set [simp]:
  "set_of (Cset.set xs) = set xs"
  by (simp add: set_def)
hide_fact (open) set_def

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
      fun_eq_iff Cset.set_def union_set [symmetric])
qed

lemma single_code [code]:
  "single a = insert a Cset.empty"
  by (simp add: Cset.single_def)

lemma of_pred_code [code]:
  "of_pred (Predicate.Seq f) = (case f () of
     Predicate.Empty \<Rightarrow> Cset.empty
   | Predicate.Insert x P \<Rightarrow> Cset.insert x (of_pred P)
   | Predicate.Join P xq \<Rightarrow> sup (of_pred P) (of_seq xq))"
  apply (auto split: seq.split simp add: Predicate.Seq_def of_pred_def Cset.set_eq_iff sup_apply eval_member [symmetric] member_def [symmetric] Collect_def mem_def member_set_of)
  apply (unfold Set.insert_def Collect_def sup_apply member_set_of)
  apply simp_all
  done

lemma of_seq_code [code]:
  "of_seq Predicate.Empty = Cset.empty"
  "of_seq (Predicate.Insert x P) = Cset.insert x (of_pred P)"
  "of_seq (Predicate.Join P xq) = sup (of_pred P) (of_seq xq)"
  apply (auto simp add: of_seq_def of_pred_def Cset.set_eq_iff mem_def Collect_def)
  apply (unfold Set.insert_def Collect_def sup_apply member_set_of)
  apply simp_all
  done

no_notation bind (infixl "\<guillemotright>=" 70)

hide_const (open) is_empty insert remove map filter forall exists card
  Inter Union bind single of_pred of_seq

hide_fact (open) set_def pred_of_cset_def of_pred_def of_seq_def single_def 
  bind_def empty_simp UNIV_simp set_simps member_bind 
  member_single single_sup_simps single_sup sup_single single_bind
  bind_bind bind_single bind_const empty_bind member_of_pred member_of_seq
  eval_pred_of_cset set_code single_code of_pred_code of_seq_code

end
