
(* Author: Florian Haftmann, TU Muenchen *)

header {* A dedicated set type which is executable on its finite part *}

theory Cset
imports More_Set More_List
begin

subsection {* Lifting *}

typedef (open) 'a set = "UNIV :: 'a set set"
  morphisms member Set by rule+
hide_type (open) set

lemma member_Set [simp]:
  "member (Set A) = A"
  by (rule Set_inverse) rule

lemma Set_member [simp]:
  "Set (member A) = A"
  by (fact member_inverse)

lemma Set_inject [simp]:
  "Set A = Set B \<longleftrightarrow> A = B"
  by (simp add: Set_inject)

lemma set_eq_iff:
  "A = B \<longleftrightarrow> member A = member B"
  by (simp add: member_inject)
hide_fact (open) set_eq_iff

lemma set_eqI:
  "member A = member B \<Longrightarrow> A = B"
  by (simp add: Cset.set_eq_iff)
hide_fact (open) set_eqI

subsection {* Lattice instantiation *}

instantiation Cset.set :: (type) boolean_algebra
begin

definition less_eq_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "A \<le> B \<longleftrightarrow> member A \<subseteq> member B"

definition less_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "A < B \<longleftrightarrow> member A \<subset> member B"

definition inf_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "inf A B = Set (member A \<inter> member B)"

definition sup_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "sup A B = Set (member A \<union> member B)"

definition bot_set :: "'a Cset.set" where
  [simp]: "bot = Set {}"

definition top_set :: "'a Cset.set" where
  [simp]: "top = Set UNIV"

definition uminus_set :: "'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "- A = Set (- (member A))"

definition minus_set :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "A - B = Set (member A - member B)"

instance proof
qed (auto intro: Cset.set_eqI)

end

instantiation Cset.set :: (type) complete_lattice
begin

definition Inf_set :: "'a Cset.set set \<Rightarrow> 'a Cset.set" where
  [simp]: "Inf_set As = Set (Inf (image member As))"

definition Sup_set :: "'a Cset.set set \<Rightarrow> 'a Cset.set" where
  [simp]: "Sup_set As = Set (Sup (image member As))"

instance proof
qed (auto simp add: le_fun_def le_bool_def)

end


subsection {* Basic operations *}

abbreviation empty :: "'a Cset.set" where "empty \<equiv> bot"
hide_const (open) empty

abbreviation UNIV :: "'a Cset.set" where "UNIV \<equiv> top"
hide_const (open) UNIV

definition is_empty :: "'a Cset.set \<Rightarrow> bool" where
  [simp]: "is_empty A \<longleftrightarrow> More_Set.is_empty (member A)"

definition insert :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "insert x A = Set (Set.insert x (member A))"

definition remove :: "'a \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "remove x A = Set (More_Set.remove x (member A))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Cset.set \<Rightarrow> 'b Cset.set" where
  [simp]: "map f A = Set (image f (member A))"

enriched_type map: map
  by (simp_all add: fun_eq_iff image_compose)

definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set" where
  [simp]: "filter P A = Set (More_Set.project P (member A))"

definition forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "forall P A \<longleftrightarrow> Ball (member A) P"

definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Cset.set \<Rightarrow> bool" where
  [simp]: "exists P A \<longleftrightarrow> Bex (member A) P"

definition card :: "'a Cset.set \<Rightarrow> nat" where
  [simp]: "card A = Finite_Set.card (member A)"
  
context complete_lattice
begin

definition Infimum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Infimum A = Inf (member A)"

definition Supremum :: "'a Cset.set \<Rightarrow> 'a" where
  [simp]: "Supremum A = Sup (member A)"

end

subsection {* More operations *}

text {* conversion from @{typ "'a list"} *}

definition set :: "'a list \<Rightarrow> 'a Cset.set" where
  "set xs = Set (List.set xs)"
hide_const (open) set

text {* conversion from @{typ "'a Predicate.pred"} *}

definition pred_of_cset :: "'a Cset.set \<Rightarrow> 'a Predicate.pred"
where [code del]: "pred_of_cset = Predicate.Pred \<circ> Cset.member"

definition of_pred :: "'a Predicate.pred \<Rightarrow> 'a Cset.set"
where "of_pred = Cset.Set \<circ> Predicate.eval"

definition of_seq :: "'a Predicate.seq \<Rightarrow> 'a Cset.set"
where "of_seq = of_pred \<circ> Predicate.pred_of_seq"

text {* monad operations *}

definition single :: "'a \<Rightarrow> 'a Cset.set" where
  "single a = Set {a}"

definition bind :: "'a Cset.set \<Rightarrow> ('a \<Rightarrow> 'b Cset.set) \<Rightarrow> 'b Cset.set"
                (infixl "\<guillemotright>=" 70)
  where "A \<guillemotright>= f = Set (\<Union>x \<in> member A. member (f x))"

subsection {* Simplified simprules *}

lemma empty_simp [simp]: "member Cset.empty = {}"
  by(simp)

lemma UNIV_simp [simp]: "member Cset.UNIV = UNIV"
  by simp

lemma is_empty_simp [simp]:
  "is_empty A \<longleftrightarrow> member A = {}"
  by (simp add: More_Set.is_empty_def)
declare is_empty_def [simp del]

lemma remove_simp [simp]:
  "remove x A = Set (member A - {x})"
  by (simp add: More_Set.remove_def)
declare remove_def [simp del]

lemma filter_simp [simp]:
  "filter P A = Set {x \<in> member A. P x}"
  by (simp add: More_Set.project_def)
declare filter_def [simp del]

lemma member_set [simp]:
  "member (Cset.set xs) = set xs"
  by (simp add: set_def)
hide_fact (open) member_set set_def

lemma set_simps [simp]:
  "Cset.set [] = Cset.empty"
  "Cset.set (x # xs) = insert x (Cset.set xs)"
by(simp_all add: Cset.set_def)

lemma member_SUPR [simp]:
  "member (SUPR A f) = SUPR A (member \<circ> f)"
unfolding SUPR_def by simp

lemma member_bind [simp]:
  "member (P \<guillemotright>= f) = member (SUPR (member P) f)"
by (simp add: bind_def Cset.set_eq_iff)

lemma member_single [simp]:
  "member (single a) = {a}"
by(simp add: single_def)

lemma single_sup_simps [simp]:
  shows single_sup: "sup (single a) A = insert a A"
  and sup_single: "sup A (single a) = insert a A"
by(auto simp add: Cset.set_eq_iff)

lemma single_bind [simp]:
  "single a \<guillemotright>= B = B a"
by(simp add: bind_def single_def)

lemma bind_bind:
  "(A \<guillemotright>= B) \<guillemotright>= C = A \<guillemotright>= (\<lambda>x. B x \<guillemotright>= C)"
by(simp add: bind_def)

lemma bind_single [simp]:
  "A \<guillemotright>= single = A"
by(simp add: bind_def single_def)

lemma bind_const: "A \<guillemotright>= (\<lambda>_. B) = (if Cset.is_empty A then Cset.empty else B)"
by(auto simp add: Cset.set_eq_iff)

lemma empty_bind [simp]:
  "Cset.empty \<guillemotright>= f = Cset.empty"
by(simp add: Cset.set_eq_iff)

lemma member_of_pred [simp]:
  "member (of_pred P) = {x. Predicate.eval P x}"
by(simp add: of_pred_def Collect_def)

lemma member_of_seq [simp]:
  "member (of_seq xq) = {x. Predicate.member xq x}"
by(simp add: of_seq_def eval_member)

lemma eval_pred_of_cset [simp]: 
  "Predicate.eval (pred_of_cset A) = Cset.member A"
by(simp add: pred_of_cset_def)

subsection {* Default implementations *}

lemma set_code [code]:
  "Cset.set = foldl (\<lambda>A x. insert x A) Cset.empty"
proof(rule ext, rule Cset.set_eqI)
  fix xs
  show "member (Cset.set xs) = member (foldl (\<lambda>A x. insert x A) Cset.empty xs)"
    by(induct xs rule: rev_induct)(simp_all)
qed

lemma single_code [code]:
  "single a = insert a Cset.empty"
by(simp add: Cset.single_def)

lemma of_pred_code [code]:
  "of_pred (Predicate.Seq f) = (case f () of
     Predicate.Empty \<Rightarrow> Cset.empty
   | Predicate.Insert x P \<Rightarrow> Cset.insert x (of_pred P)
   | Predicate.Join P xq \<Rightarrow> sup (of_pred P) (of_seq xq))"
by(auto split: seq.split 
        simp add: Predicate.Seq_def of_pred_def eval_member Cset.set_eq_iff)

lemma of_seq_code [code]:
  "of_seq Predicate.Empty = Cset.empty"
  "of_seq (Predicate.Insert x P) = Cset.insert x (of_pred P)"
  "of_seq (Predicate.Join P xq) = sup (of_pred P) (of_seq xq)"
by(auto simp add: of_seq_def of_pred_def Cset.set_eq_iff)

declare mem_def [simp del]

no_notation bind (infixl "\<guillemotright>=" 70)

hide_const (open) is_empty insert remove map filter forall exists card
  Inter Union bind single of_pred of_seq

hide_fact (open) set_def pred_of_cset_def of_pred_def of_seq_def single_def 
  bind_def empty_simp UNIV_simp member_set set_simps member_SUPR member_bind 
  member_single single_sup_simps single_sup sup_single single_bind
  bind_bind bind_single bind_const empty_bind member_of_pred member_of_seq
  eval_pred_of_cset set_code single_code of_pred_code of_seq_code

end
