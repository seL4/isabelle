(*  Title:      HOL/Library/RBT_Set.thy
    Author:     Ondrej Kuncar
*)

section \<open>Implementation of sets using RBT trees\<close>

theory RBT_Set
imports RBT Product_Lexorder
begin

(*
  Users should be aware that by including this file all code equations
  outside of List.thy using 'a list as an implementation of sets cannot be
  used for code generation. If such equations are not needed, they can be
  deleted from the code generator. Otherwise, a user has to provide their 
  own equations using RBT trees. 
*)

section \<open>Definition of code datatype constructors\<close>

definition Set :: "('a::linorder, unit) rbt \<Rightarrow> 'a set" 
  where "Set t = {x . RBT.lookup t x = Some ()}"

definition Coset :: "('a::linorder, unit) rbt \<Rightarrow> 'a set" 
  where [simp]: "Coset t = - Set t"


section \<open>Deletion of already existing code equations\<close>

declare [[code drop: Set.empty Set.is_empty uminus_set_inst.uminus_set
  Set.member Set.insert Set.remove UNIV Set.filter image
  Set.subset_eq Ball Bex can_select Set.union minus_set_inst.minus_set Set.inter
  card the_elem Pow sum prod Product_Type.product Id_on
  Image trancl relcomp wf Min Inf_fin Max Sup_fin
  "(Inf :: 'a set set \<Rightarrow> 'a set)" "(Sup :: 'a set set \<Rightarrow> 'a set)"
  sorted_list_of_set List.map_project List.Bleast]]


section \<open>Lemmas\<close>

subsection \<open>Auxiliary lemmas\<close>

lemma [simp]: "x \<noteq> Some () \<longleftrightarrow> x = None"
by (auto simp: not_Some_eq[THEN iffD1])

lemma Set_set_keys: "Set x = dom (RBT.lookup x)" 
by (auto simp: Set_def)

lemma finite_Set [simp, intro!]: "finite (Set x)"
by (simp add: Set_set_keys)

lemma set_keys: "Set t = set(RBT.keys t)"
by (simp add: Set_set_keys lookup_keys)

subsection \<open>fold and filter\<close>

lemma finite_fold_rbt_fold_eq:
  assumes "comp_fun_commute f" 
  shows "Finite_Set.fold f A (set (RBT.entries t)) = RBT.fold (curry f) t A"
proof -
  have *: "remdups (RBT.entries t) = RBT.entries t"
    using distinct_entries distinct_map by (auto intro: distinct_remdups_id)
  show ?thesis using assms by (auto simp: fold_def_alt comp_fun_commute.fold_set_fold_remdups *)
qed

definition fold_keys :: "('a :: linorder \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, _) rbt \<Rightarrow> 'b \<Rightarrow> 'b" 
  where [code_unfold]:"fold_keys f t A = RBT.fold (\<lambda>k _ t. f k t) t A"

lemma fold_keys_def_alt:
  "fold_keys f t s = List.fold f (RBT.keys t) s"
by (auto simp: fold_map o_def split_def fold_def_alt keys_def_alt fold_keys_def)

lemma finite_fold_fold_keys:
  assumes "comp_fun_commute f"
  shows "Finite_Set.fold f A (Set t) = fold_keys f t A"
using assms
proof -
  interpret comp_fun_commute f by fact
  have "set (RBT.keys t) = fst ` (set (RBT.entries t))" by (auto simp: fst_eq_Domain keys_entries)
  moreover have "inj_on fst (set (RBT.entries t))" using distinct_entries distinct_map by auto
  ultimately show ?thesis 
    by (auto simp add: set_keys fold_keys_def curry_def fold_image finite_fold_rbt_fold_eq 
      comp_comp_fun_commute)
qed

definition rbt_filter :: "('a :: linorder \<Rightarrow> bool) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> 'a set" where
  "rbt_filter P t = RBT.fold (\<lambda>k _ A'. if P k then Set.insert k A' else A') t {}"

lemma Set_filter_rbt_filter:
  "Set.filter P (Set t) = rbt_filter P t"
by (simp add: fold_keys_def Set_filter_fold rbt_filter_def 
  finite_fold_fold_keys[OF comp_fun_commute_filter_fold])


subsection \<open>foldi and Ball\<close>

lemma Ball_False: "RBT_Impl.fold (\<lambda>k v s. s \<and> P k) t False = False"
by (induction t) auto

lemma rbt_foldi_fold_conj: 
  "RBT_Impl.foldi (\<lambda>s. s = True) (\<lambda>k v s. s \<and> P k) t val = RBT_Impl.fold (\<lambda>k v s. s \<and> P k) t val"
proof (induction t arbitrary: val) 
  case (Branch c t1) then show ?case
    by (cases "RBT_Impl.fold (\<lambda>k v s. s \<and> P k) t1 True") (simp_all add: Ball_False) 
qed simp

lemma foldi_fold_conj: "RBT.foldi (\<lambda>s. s = True) (\<lambda>k v s. s \<and> P k) t val = fold_keys (\<lambda>k s. s \<and> P k) t val"
unfolding fold_keys_def including rbt.lifting by transfer (rule rbt_foldi_fold_conj)


subsection \<open>foldi and Bex\<close>

lemma Bex_True: "RBT_Impl.fold (\<lambda>k v s. s \<or> P k) t True = True"
by (induction t) auto

lemma rbt_foldi_fold_disj: 
  "RBT_Impl.foldi (\<lambda>s. s = False) (\<lambda>k v s. s \<or> P k) t val = RBT_Impl.fold (\<lambda>k v s. s \<or> P k) t val"
proof (induction t arbitrary: val) 
  case (Branch c t1) then show ?case
    by (cases "RBT_Impl.fold (\<lambda>k v s. s \<or> P k) t1 False") (simp_all add: Bex_True) 
qed simp

lemma foldi_fold_disj: "RBT.foldi (\<lambda>s. s = False) (\<lambda>k v s. s \<or> P k) t val = fold_keys (\<lambda>k s. s \<or> P k) t val"
unfolding fold_keys_def including rbt.lifting by transfer (rule rbt_foldi_fold_disj)


subsection \<open>folding over non empty trees and selecting the minimal and maximal element\<close>

subsubsection \<open>concrete\<close>

text \<open>The concrete part is here because it's probably not general enough to be moved to \<open>RBT_Impl\<close>\<close>

definition rbt_fold1_keys :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a::linorder, 'b) RBT_Impl.rbt \<Rightarrow> 'a" 
  where "rbt_fold1_keys f t = List.fold f (tl(RBT_Impl.keys t)) (hd(RBT_Impl.keys t))"


paragraph \<open>minimum\<close>

definition rbt_min :: "('a::linorder, unit) RBT_Impl.rbt \<Rightarrow> 'a" 
  where "rbt_min t = rbt_fold1_keys min t"

lemma key_le_right: "rbt_sorted (Branch c lt k v rt) \<Longrightarrow> (\<And>x. x \<in>set (RBT_Impl.keys rt) \<Longrightarrow> k \<le> x)"
by  (auto simp: rbt_greater_prop less_imp_le)

lemma left_le_key: "rbt_sorted (Branch c lt k v rt) \<Longrightarrow> (\<And>x. x \<in>set (RBT_Impl.keys lt) \<Longrightarrow> x \<le> k)"
by (auto simp: rbt_less_prop less_imp_le)

lemma fold_min_triv:
  fixes k :: "_ :: linorder"
  shows "(\<forall>x\<in>set xs. k \<le> x) \<Longrightarrow> List.fold min xs k = k" 
by (induct xs) (auto simp add: min_def)

lemma rbt_min_simps:
  "is_rbt (Branch c RBT_Impl.Empty k v rt) \<Longrightarrow> rbt_min (Branch c RBT_Impl.Empty k v rt) = k"
by (auto intro: fold_min_triv dest: key_le_right is_rbt_rbt_sorted simp: rbt_fold1_keys_def rbt_min_def)

fun rbt_min_opt where
  "rbt_min_opt (Branch c RBT_Impl.Empty k v rt) = k" |
  "rbt_min_opt (Branch c (Branch lc llc lk lv lrt) k v rt) = rbt_min_opt (Branch lc llc lk lv lrt)"

lemma rbt_min_opt_Branch:
  "t1 \<noteq> rbt.Empty \<Longrightarrow> rbt_min_opt (Branch c t1 k () t2) = rbt_min_opt t1" 
by (cases t1) auto

lemma rbt_min_opt_induct [case_names empty left_empty left_non_empty]:
  fixes t :: "('a :: linorder, unit) RBT_Impl.rbt"
  assumes "P rbt.Empty"
  assumes "\<And>color t1 a b t2. P t1 \<Longrightarrow> P t2 \<Longrightarrow> t1 = rbt.Empty \<Longrightarrow> P (Branch color t1 a b t2)"
  assumes "\<And>color t1 a b t2. P t1 \<Longrightarrow> P t2 \<Longrightarrow> t1 \<noteq> rbt.Empty \<Longrightarrow> P (Branch color t1 a b t2)"
  shows "P t"
  using assms
proof (induct t)
  case Empty
  then show ?case by simp
next
  case (Branch x1 t1 x3 x4 t2)
  then show ?case by (cases "t1 = rbt.Empty") simp_all
qed

lemma rbt_min_opt_in_set: 
  fixes t :: "('a :: linorder, unit) RBT_Impl.rbt"
  assumes "t \<noteq> rbt.Empty"
  shows "rbt_min_opt t \<in> set (RBT_Impl.keys t)"
using assms by (induction t rule: rbt_min_opt.induct) (auto)

lemma rbt_min_opt_is_min:
  fixes t :: "('a :: linorder, unit) RBT_Impl.rbt"
  assumes "rbt_sorted t"
  assumes "t \<noteq> rbt.Empty"
  shows "\<And>y. y \<in> set (RBT_Impl.keys t) \<Longrightarrow> y \<ge> rbt_min_opt t"
using assms 
proof (induction t rule: rbt_min_opt_induct)
  case empty
  then show ?case by simp
next
  case left_empty
  then show ?case by (auto intro: key_le_right simp del: rbt_sorted.simps)
next
  case (left_non_empty c t1 k v t2 y)
  then consider "y = k" | "y \<in> set (RBT_Impl.keys t1)" | "y \<in> set (RBT_Impl.keys t2)"
    by auto
  then show ?case 
  proof cases
    case 1
    with left_non_empty show ?thesis
      by (auto simp add: rbt_min_opt_Branch intro: left_le_key rbt_min_opt_in_set)
  next
    case 2
    with left_non_empty show ?thesis
      by (auto simp add: rbt_min_opt_Branch)
  next 
    case y: 3
    have "rbt_min_opt t1 \<le> k"
      using left_non_empty by (simp add: left_le_key rbt_min_opt_in_set)
    moreover have "k \<le> y"
      using left_non_empty y by (simp add: key_le_right)
    ultimately show ?thesis
      using left_non_empty y by (simp add: rbt_min_opt_Branch)
  qed
qed

lemma rbt_min_eq_rbt_min_opt:
  assumes "t \<noteq> RBT_Impl.Empty"
  assumes "is_rbt t"
  shows "rbt_min t = rbt_min_opt t"
proof -
  from assms have "hd (RBT_Impl.keys t) # tl (RBT_Impl.keys t) = RBT_Impl.keys t" by (cases t) simp_all
  with assms show ?thesis
    by (simp add: rbt_min_def rbt_fold1_keys_def rbt_min_opt_is_min
      Min.set_eq_fold [symmetric] Min_eqI rbt_min_opt_in_set)
qed


paragraph \<open>maximum\<close>

definition rbt_max :: "('a::linorder, unit) RBT_Impl.rbt \<Rightarrow> 'a" 
  where "rbt_max t = rbt_fold1_keys max t"

lemma fold_max_triv:
  fixes k :: "_ :: linorder"
  shows "(\<forall>x\<in>set xs. x \<le> k) \<Longrightarrow> List.fold max xs k = k" 
by (induct xs) (auto simp add: max_def)

lemma fold_max_rev_eq:
  fixes xs :: "('a :: linorder) list"
  assumes "xs \<noteq> []"
  shows "List.fold max (tl xs) (hd xs) = List.fold max (tl (rev xs)) (hd (rev xs))" 
  using assms by (simp add: Max.set_eq_fold [symmetric])

lemma rbt_max_simps:
  assumes "is_rbt (Branch c lt k v RBT_Impl.Empty)" 
  shows "rbt_max (Branch c lt k v RBT_Impl.Empty) = k"
proof -
  have "List.fold max (tl (rev(RBT_Impl.keys lt @ [k]))) (hd (rev(RBT_Impl.keys lt @ [k]))) = k"
    using assms by (auto intro!: fold_max_triv dest!: left_le_key is_rbt_rbt_sorted)
  then show ?thesis by (auto simp add: rbt_max_def rbt_fold1_keys_def fold_max_rev_eq)
qed

fun rbt_max_opt where
  "rbt_max_opt (Branch c lt k v RBT_Impl.Empty) = k" |
  "rbt_max_opt (Branch c lt k v (Branch rc rlc rk rv rrt)) = rbt_max_opt (Branch rc rlc rk rv rrt)"

lemma rbt_max_opt_Branch:
  "t2 \<noteq> rbt.Empty \<Longrightarrow> rbt_max_opt (Branch c t1 k () t2) = rbt_max_opt t2" 
by (cases t2) auto

lemma rbt_max_opt_induct [case_names empty right_empty right_non_empty]:
  fixes t :: "('a :: linorder, unit) RBT_Impl.rbt"
  assumes "P rbt.Empty"
  assumes "\<And>color t1 a b t2. P t1 \<Longrightarrow> P t2 \<Longrightarrow> t2 = rbt.Empty \<Longrightarrow> P (Branch color t1 a b t2)"
  assumes "\<And>color t1 a b t2. P t1 \<Longrightarrow> P t2 \<Longrightarrow> t2 \<noteq> rbt.Empty \<Longrightarrow> P (Branch color t1 a b t2)"
  shows "P t"
  using assms
proof (induct t)
  case Empty
  then show ?case by simp
next
  case (Branch x1 t1 x3 x4 t2)
  then show ?case by (cases "t2 = rbt.Empty") simp_all
qed

lemma rbt_max_opt_in_set: 
  fixes t :: "('a :: linorder, unit) RBT_Impl.rbt"
  assumes "t \<noteq> rbt.Empty"
  shows "rbt_max_opt t \<in> set (RBT_Impl.keys t)"
using assms by (induction t rule: rbt_max_opt.induct) (auto)

lemma rbt_max_opt_is_max:
  fixes t :: "('a :: linorder, unit) RBT_Impl.rbt"
  assumes "rbt_sorted t"
  assumes "t \<noteq> rbt.Empty"
  shows "\<And>y. y \<in> set (RBT_Impl.keys t) \<Longrightarrow> y \<le> rbt_max_opt t"
using assms 
proof (induction t rule: rbt_max_opt_induct)
  case empty
  then show ?case by simp
next
  case right_empty
  then show ?case by (auto intro: left_le_key simp del: rbt_sorted.simps)
next
  case (right_non_empty c t1 k v t2 y)
  then consider "y = k" | "y \<in> set (RBT_Impl.keys t2)" | "y \<in> set (RBT_Impl.keys t1)"
    by auto
  then show ?case 
  proof cases
    case 1
    with right_non_empty show ?thesis
      by (auto simp add: rbt_max_opt_Branch intro: key_le_right rbt_max_opt_in_set)
  next
    case 2
    with right_non_empty show ?thesis
      by (auto simp add: rbt_max_opt_Branch)
  next 
    case y: 3
    have "rbt_max_opt t2 \<ge> k"
      using right_non_empty by (simp add: key_le_right rbt_max_opt_in_set)
    moreover have "y \<le> k"
      using right_non_empty y by (simp add: left_le_key)
    ultimately show ?thesis
      using right_non_empty by (simp add: rbt_max_opt_Branch)
  qed
qed

lemma rbt_max_eq_rbt_max_opt:
  assumes "t \<noteq> RBT_Impl.Empty"
  assumes "is_rbt t"
  shows "rbt_max t = rbt_max_opt t"
proof -
  from assms have "hd (RBT_Impl.keys t) # tl (RBT_Impl.keys t) = RBT_Impl.keys t" by (cases t) simp_all
  with assms show ?thesis
    by (simp add: rbt_max_def rbt_fold1_keys_def rbt_max_opt_is_max
      Max.set_eq_fold [symmetric] Max_eqI rbt_max_opt_in_set)
qed


subsubsection \<open>abstract\<close>

context includes rbt.lifting begin
lift_definition fold1_keys :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a::linorder, 'b) rbt \<Rightarrow> 'a"
  is rbt_fold1_keys .

lemma fold1_keys_def_alt:
  "fold1_keys f t = List.fold f (tl (RBT.keys t)) (hd (RBT.keys t))"
  by transfer (simp add: rbt_fold1_keys_def)

lemma finite_fold1_fold1_keys:
  assumes "semilattice f"
  assumes "\<not> RBT.is_empty t"
  shows "semilattice_set.F f (Set t) = fold1_keys f t"
proof -
  from \<open>semilattice f\<close> interpret semilattice_set f by (rule semilattice_set.intro)
  show ?thesis using assms 
    by (auto simp: fold1_keys_def_alt set_keys fold_def_alt non_empty_keys set_eq_fold [symmetric])
qed


paragraph \<open>minimum\<close>

lift_definition r_min :: "('a :: linorder, unit) rbt \<Rightarrow> 'a" is rbt_min .

lift_definition r_min_opt :: "('a :: linorder, unit) rbt \<Rightarrow> 'a" is rbt_min_opt .

lemma r_min_alt_def: "r_min t = fold1_keys min t"
by transfer (simp add: rbt_min_def)

lemma r_min_eq_r_min_opt:
  assumes "\<not> (RBT.is_empty t)"
  shows "r_min t = r_min_opt t"
using assms unfolding is_empty_empty by transfer (auto intro: rbt_min_eq_rbt_min_opt)

lemma fold_keys_min_top_eq:
  fixes t :: "('a::{linorder,bounded_lattice_top}, unit) rbt"
  assumes "\<not> (RBT.is_empty t)"
  shows "fold_keys min t top = fold1_keys min t"
proof -
  have *: "\<And>t. RBT_Impl.keys t \<noteq> [] \<Longrightarrow> List.fold min (RBT_Impl.keys t) top = 
      List.fold min (hd (RBT_Impl.keys t) # tl (RBT_Impl.keys t)) top"
    by (simp add: hd_Cons_tl[symmetric])
  have **: "List.fold min (x # xs) top = List.fold min xs x" for x :: 'a and xs
    by (simp add: inf_min[symmetric])
  show ?thesis
    using assms
    unfolding fold_keys_def_alt fold1_keys_def_alt is_empty_empty
    apply transfer 
    apply (case_tac t) 
     apply simp 
    apply (subst *)
     apply simp
    apply (subst **)
    apply simp
    done
qed


paragraph \<open>maximum\<close>

lift_definition r_max :: "('a :: linorder, unit) rbt \<Rightarrow> 'a" is rbt_max .

lift_definition r_max_opt :: "('a :: linorder, unit) rbt \<Rightarrow> 'a" is rbt_max_opt .

lemma r_max_alt_def: "r_max t = fold1_keys max t"
by transfer (simp add: rbt_max_def)

lemma r_max_eq_r_max_opt:
  assumes "\<not> (RBT.is_empty t)"
  shows "r_max t = r_max_opt t"
using assms unfolding is_empty_empty by transfer (auto intro: rbt_max_eq_rbt_max_opt)

lemma fold_keys_max_bot_eq:
  fixes t :: "('a::{linorder,bounded_lattice_bot}, unit) rbt"
  assumes "\<not> (RBT.is_empty t)"
  shows "fold_keys max t bot = fold1_keys max t"
proof -
  have *: "\<And>t. RBT_Impl.keys t \<noteq> [] \<Longrightarrow> List.fold max (RBT_Impl.keys t) bot = 
      List.fold max (hd(RBT_Impl.keys t) # tl(RBT_Impl.keys t)) bot"
    by (simp add: hd_Cons_tl[symmetric])
  have **: "List.fold max (x # xs) bot = List.fold max xs x" for x :: 'a and xs
    by (simp add: sup_max[symmetric])
  show ?thesis
    using assms
    unfolding fold_keys_def_alt fold1_keys_def_alt is_empty_empty
    apply transfer 
    apply (case_tac t) 
     apply simp 
    apply (subst *)
     apply simp
    apply (subst **)
    apply simp
    done
qed

end

section \<open>Code equations\<close>

code_datatype Set Coset

declare list.set[code] (* needed? *)

lemma empty_Set [code]:
  "Set.empty = Set RBT.empty"
by (auto simp: Set_def)

lemma UNIV_Coset [code]:
  "UNIV = Coset RBT.empty"
by (auto simp: Set_def)

lemma is_empty_Set [code]:
  "Set.is_empty (Set t) = RBT.is_empty t"
  unfolding Set.is_empty_def by (auto simp: fun_eq_iff Set_def intro: lookup_empty_empty[THEN iffD1])

lemma compl_code [code]:
  "- Set xs = Coset xs"
  "- Coset xs = Set xs"
by (simp_all add: Set_def)

lemma member_code [code]:
  "x \<in> (Set t) = (RBT.lookup t x = Some ())"
  "x \<in> (Coset t) = (RBT.lookup t x = None)"
by (simp_all add: Set_def)

lemma insert_code [code]:
  "Set.insert x (Set t) = Set (RBT.insert x () t)"
  "Set.insert x (Coset t) = Coset (RBT.delete x t)"
by (auto simp: Set_def)

lemma remove_code [code]:
  "Set.remove x (Set t) = Set (RBT.delete x t)"
  "Set.remove x (Coset t) = Coset (RBT.insert x () t)"
by (auto simp: Set_def)

lemma union_Set [code]:
  "Set t \<union> A = fold_keys Set.insert t A"
proof -
  interpret comp_fun_idem Set.insert
    by (fact comp_fun_idem_insert)
  from finite_fold_fold_keys[OF comp_fun_commute_axioms]
  show ?thesis by (auto simp add: union_fold_insert)
qed

lemma inter_Set [code]:
  "A \<inter> Set t = rbt_filter (\<lambda>k. k \<in> A) t"
by (simp add: inter_Set_filter Set_filter_rbt_filter)

lemma minus_Set [code]:
  "A - Set t = fold_keys Set.remove t A"
proof -
  interpret comp_fun_idem Set.remove
    by (fact comp_fun_idem_remove)
  from finite_fold_fold_keys[OF comp_fun_commute_axioms]
  show ?thesis by (auto simp add: minus_fold_remove)
qed

lemma union_Coset [code]:
  "Coset t \<union> A = - rbt_filter (\<lambda>k. k \<notin> A) t"
proof -
  have *: "\<And>A B. (-A \<union> B) = -(-B \<inter> A)" by blast
  show ?thesis by (simp del: boolean_algebra_class.compl_inf add: * inter_Set)
qed
 
lemma union_Set_Set [code]:
  "Set t1 \<union> Set t2 = Set (RBT.union t1 t2)"
by (auto simp add: lookup_union map_add_Some_iff Set_def)

lemma inter_Coset [code]:
  "A \<inter> Coset t = fold_keys Set.remove t A"
by (simp add: Diff_eq [symmetric] minus_Set)

lemma inter_Coset_Coset [code]:
  "Coset t1 \<inter> Coset t2 = Coset (RBT.union t1 t2)"
by (auto simp add: lookup_union map_add_Some_iff Set_def)

lemma minus_Coset [code]:
  "A - Coset t = rbt_filter (\<lambda>k. k \<in> A) t"
by (simp add: inter_Set[simplified Int_commute])

lemma filter_Set [code]:
  "Set.filter P (Set t) = (rbt_filter P t)"
by (auto simp add: Set_filter_rbt_filter)

lemma image_Set [code]:
  "image f (Set t) = fold_keys (\<lambda>k A. Set.insert (f k) A) t {}"
proof -
  have "comp_fun_commute (\<lambda>k. Set.insert (f k))"
    by standard auto
  then show ?thesis
    by (auto simp add: image_fold_insert intro!: finite_fold_fold_keys)
qed

lemma Ball_Set [code]:
  "Ball (Set t) P \<longleftrightarrow> RBT.foldi (\<lambda>s. s = True) (\<lambda>k v s. s \<and> P k) t True"
proof -
  have "comp_fun_commute (\<lambda>k s. s \<and> P k)"
    by standard auto
  then show ?thesis 
    by (simp add: foldi_fold_conj[symmetric] Ball_fold finite_fold_fold_keys)
qed

lemma Bex_Set [code]:
  "Bex (Set t) P \<longleftrightarrow> RBT.foldi (\<lambda>s. s = False) (\<lambda>k v s. s \<or> P k) t False"
proof -
  have "comp_fun_commute (\<lambda>k s. s \<or> P k)"
    by standard auto
  then show ?thesis 
    by (simp add: foldi_fold_disj[symmetric] Bex_fold finite_fold_fold_keys)
qed

lemma subset_code [code]:
  "Set t \<le> B \<longleftrightarrow> (\<forall>x\<in>Set t. x \<in> B)"
  "A \<le> Coset t \<longleftrightarrow> (\<forall>y\<in>Set t. y \<notin> A)"
by auto

lemma subset_Coset_empty_Set_empty [code]:
  "Coset t1 \<le> Set t2 \<longleftrightarrow> (case (RBT.impl_of t1, RBT.impl_of t2) of 
    (rbt.Empty, rbt.Empty) \<Rightarrow> False |
    (_, _) \<Rightarrow> Code.abort (STR ''non_empty_trees'') (\<lambda>_. Coset t1 \<le> Set t2))"
proof -
  have *: "\<And>t. RBT.impl_of t = rbt.Empty \<Longrightarrow> t = RBT rbt.Empty"
    by (subst(asm) RBT_inverse[symmetric]) (auto simp: impl_of_inject)
  have **: "eq_onp is_rbt rbt.Empty rbt.Empty" unfolding eq_onp_def by simp
  show ?thesis  
    by (auto simp: Set_def lookup.abs_eq[OF **] dest!: * split: rbt.split)
qed

text \<open>A frequent case -- avoid intermediate sets\<close>
lemma [code_unfold]:
  "Set t1 \<subseteq> Set t2 \<longleftrightarrow> RBT.foldi (\<lambda>s. s = True) (\<lambda>k v s. s \<and> k \<in> Set t2) t1 True"
by (simp add: subset_code Ball_Set)

lemma card_Set [code]:
  "card (Set t) = fold_keys (\<lambda>_ n. n + 1) t 0"
  by (auto simp add: card.eq_fold intro: finite_fold_fold_keys comp_fun_commute_const)

lemma sum_Set [code]:
  "sum f (Set xs) = fold_keys (plus \<circ> f) xs 0"
proof -
  have "comp_fun_commute (\<lambda>x. (+) (f x))"
    by standard (auto simp: ac_simps)
  then show ?thesis 
    by (auto simp add: sum.eq_fold finite_fold_fold_keys o_def)
qed

lemma the_elem_set [code]:
  fixes t :: "('a :: linorder, unit) rbt"
  shows "the_elem (Set t) = (case RBT.impl_of t of 
    (Branch RBT_Impl.B RBT_Impl.Empty x () RBT_Impl.Empty) \<Rightarrow> x
    | _ \<Rightarrow> Code.abort (STR ''not_a_singleton_tree'') (\<lambda>_. the_elem (Set t)))"
proof -
  {
    fix x :: "'a :: linorder"
    let ?t = "Branch RBT_Impl.B RBT_Impl.Empty x () RBT_Impl.Empty" 
    have *:"?t \<in> {t. is_rbt t}" unfolding is_rbt_def by auto
    then have **:"eq_onp is_rbt ?t ?t" unfolding eq_onp_def by auto

    have "RBT.impl_of t = ?t \<Longrightarrow> the_elem (Set t) = x" 
      by (subst(asm) RBT_inverse[symmetric, OF *])
        (auto simp: Set_def the_elem_def lookup.abs_eq[OF **] impl_of_inject)
  }
  then show ?thesis
    by(auto split: rbt.split unit.split color.split)
qed

lemma Pow_Set [code]: "Pow (Set t) = fold_keys (\<lambda>x A. A \<union> Set.insert x ` A) t {{}}"
  by (simp add: Pow_fold finite_fold_fold_keys[OF comp_fun_commute_Pow_fold])

lemma product_Set [code]:
  "Product_Type.product (Set t1) (Set t2) = 
    fold_keys (\<lambda>x A. fold_keys (\<lambda>y. Set.insert (x, y)) t2 A) t1 {}"
proof -
  have *: "comp_fun_commute (\<lambda>y. Set.insert (x, y))" for x
    by standard auto
  show ?thesis using finite_fold_fold_keys[OF comp_fun_commute_product_fold, of "Set t2" "{}" "t1"]  
    by (simp add: product_fold Product_Type.product_def finite_fold_fold_keys[OF *])
qed

lemma Id_on_Set [code]: "Id_on (Set t) =  fold_keys (\<lambda>x. Set.insert (x, x)) t {}"
proof -
  have "comp_fun_commute (\<lambda>x. Set.insert (x, x))"
    by standard auto
  then show ?thesis
    by (auto simp add: Id_on_fold intro!: finite_fold_fold_keys)
qed

lemma Image_Set [code]:
  "(Set t) `` S = fold_keys (\<lambda>(x,y) A. if x \<in> S then Set.insert y A else A) t {}"
by (auto simp add: Image_fold finite_fold_fold_keys[OF comp_fun_commute_Image_fold])

lemma trancl_set_ntrancl [code]:
  "trancl (Set t) = ntrancl (card (Set t) - 1) (Set t)"
by (simp add: finite_trancl_ntranl)

lemma relcomp_Set[code]:
  "(Set t1) O (Set t2) = fold_keys 
    (\<lambda>(x,y) A. fold_keys (\<lambda>(w,z) A'. if y = w then Set.insert (x,z) A' else A') t2 A) t1 {}"
proof -
  interpret comp_fun_idem Set.insert
    by (fact comp_fun_idem_insert)
  have *: "\<And>x y. comp_fun_commute (\<lambda>(w, z) A'. if y = w then Set.insert (x, z) A' else A')"
    by standard (auto simp add: fun_eq_iff)
  show ?thesis
    using finite_fold_fold_keys[OF comp_fun_commute_relcomp_fold, of "Set t2" "{}" t1]
    by (simp add: relcomp_fold finite_fold_fold_keys[OF *])
qed

lemma wf_set [code]:
  "wf (Set t) = acyclic (Set t)"
by (simp add: wf_iff_acyclic_if_finite)

lemma Min_fin_set_fold [code]:
  "Min (Set t) = 
  (if RBT.is_empty t
   then Code.abort (STR ''not_non_empty_tree'') (\<lambda>_. Min (Set t))
   else r_min_opt t)"
proof -
  have *: "semilattice (min :: 'a \<Rightarrow> 'a \<Rightarrow> 'a)" ..
  with finite_fold1_fold1_keys [OF *, folded Min_def]
  show ?thesis
    by (simp add: r_min_alt_def r_min_eq_r_min_opt [symmetric])  
qed

lemma Inf_fin_set_fold [code]:
  "Inf_fin (Set t) = Min (Set t)"
by (simp add: inf_min Inf_fin_def Min_def)

lemma Inf_Set_fold:
  fixes t :: "('a :: {linorder, complete_lattice}, unit) rbt"
  shows "Inf (Set t) = (if RBT.is_empty t then top else r_min_opt t)"
proof -
  have "comp_fun_commute (min :: 'a \<Rightarrow> 'a \<Rightarrow> 'a)"
    by standard (simp add: fun_eq_iff ac_simps)
  then have "t \<noteq> RBT.empty \<Longrightarrow> Finite_Set.fold min top (Set t) = fold1_keys min t"
    by (simp add: finite_fold_fold_keys fold_keys_min_top_eq)
  then show ?thesis 
    by (auto simp add: Inf_fold_inf inf_min empty_Set[symmetric]
      r_min_eq_r_min_opt[symmetric] r_min_alt_def)
qed

lemma Max_fin_set_fold [code]:
  "Max (Set t) = 
  (if RBT.is_empty t
   then Code.abort (STR ''not_non_empty_tree'') (\<lambda>_. Max (Set t))
   else r_max_opt t)"
proof -
  have *: "semilattice (max :: 'a \<Rightarrow> 'a \<Rightarrow> 'a)" ..
  with finite_fold1_fold1_keys [OF *, folded Max_def]
  show ?thesis
    by (simp add: r_max_alt_def r_max_eq_r_max_opt [symmetric])  
qed

lemma Sup_fin_set_fold [code]:
  "Sup_fin (Set t) = Max (Set t)"
by (simp add: sup_max Sup_fin_def Max_def)

lemma Sup_Set_fold:
  fixes t :: "('a :: {linorder, complete_lattice}, unit) rbt"
  shows "Sup (Set t) = (if RBT.is_empty t then bot else r_max_opt t)"
proof -
  have "comp_fun_commute (max :: 'a \<Rightarrow> 'a \<Rightarrow> 'a)"
    by standard (simp add: fun_eq_iff ac_simps)
  then have "t \<noteq> RBT.empty \<Longrightarrow> Finite_Set.fold max bot (Set t) = fold1_keys max t"
    by (simp add: finite_fold_fold_keys fold_keys_max_bot_eq)
  then show ?thesis 
    by (auto simp add: Sup_fold_sup sup_max empty_Set[symmetric]
      r_max_eq_r_max_opt[symmetric] r_max_alt_def)
qed

context
begin

qualified definition Inf' :: "'a :: {linorder, complete_lattice} set \<Rightarrow> 'a"
  where [code_abbrev]: "Inf' = Inf"

lemma Inf'_Set_fold [code]:
  "Inf' (Set t) = (if RBT.is_empty t then top else r_min_opt t)"
  by (simp add: Inf'_def Inf_Set_fold)

qualified definition Sup' :: "'a :: {linorder, complete_lattice} set \<Rightarrow> 'a"
  where [code_abbrev]: "Sup' = Sup"

lemma Sup'_Set_fold [code]:
  "Sup' (Set t) = (if RBT.is_empty t then bot else r_max_opt t)"
  by (simp add: Sup'_def Sup_Set_fold)

lemma [code drop: Gcd_fin, code]:
  "Gcd\<^sub>f\<^sub>i\<^sub>n (Set t) = fold_keys gcd t (0::'a::{semiring_gcd, linorder})"
proof -
  have "comp_fun_commute (gcd :: 'a \<Rightarrow> _)"
    by standard (simp add: fun_eq_iff ac_simps)
  with finite_fold_fold_keys [of _ 0 t]
  have "Finite_Set.fold gcd 0 (Set t) = fold_keys gcd t 0"
    by blast
  then show ?thesis
    by (simp add: Gcd_fin.eq_fold)
qed
    
lemma [code drop: "Gcd :: _ \<Rightarrow> nat", code]:
  "Gcd (Set t) = (Gcd\<^sub>f\<^sub>i\<^sub>n (Set t) :: nat)"
  by simp

lemma [code drop: "Gcd :: _ \<Rightarrow> int", code]:
  "Gcd (Set t) = (Gcd\<^sub>f\<^sub>i\<^sub>n (Set t) :: int)"
  by simp

lemma [code drop: Lcm_fin,code]:
  "Lcm\<^sub>f\<^sub>i\<^sub>n (Set t) = fold_keys lcm t (1::'a::{semiring_gcd, linorder})"
proof -
  have "comp_fun_commute (lcm :: 'a \<Rightarrow> _)"
    by standard (simp add: fun_eq_iff ac_simps)
  with finite_fold_fold_keys [of _ 1 t]
  have "Finite_Set.fold lcm 1 (Set t) = fold_keys lcm t 1"
    by blast
  then show ?thesis
    by (simp add: Lcm_fin.eq_fold)
qed

qualified definition Lcm' :: "'a :: semiring_Gcd set \<Rightarrow> 'a"
  where [code_abbrev]: "Lcm' = Lcm"

lemma [code drop: "Lcm :: _ \<Rightarrow> nat", code]:
  "Lcm (Set t) = (Lcm\<^sub>f\<^sub>i\<^sub>n (Set t) :: nat)"
  by simp

lemma [code drop: "Lcm :: _ \<Rightarrow> int", code]:
  "Lcm (Set t) = (Lcm\<^sub>f\<^sub>i\<^sub>n (Set t) :: int)"
  by simp

end

lemma sorted_list_set[code]: "sorted_list_of_set (Set t) = RBT.keys t"
  by (auto simp add: set_keys intro: sorted_distinct_set_unique) 

lemma Bleast_code [code]:
  "Bleast (Set t) P =
    (case List.filter P (RBT.keys t) of
      x # xs \<Rightarrow> x
    | [] \<Rightarrow> abort_Bleast (Set t) P)"
proof (cases "List.filter P (RBT.keys t)")
  case Nil
  thus ?thesis by (simp add: Bleast_def abort_Bleast_def)
next
  case (Cons x ys)
  have "(LEAST x. x \<in> Set t \<and> P x) = x"
  proof (rule Least_equality)
    show "x \<in> Set t \<and> P x"
      using Cons[symmetric]
      by (auto simp add: set_keys Cons_eq_filter_iff)
    next
      fix y
      assume "y \<in> Set t \<and> P y"
      then show "x \<le> y"
        using Cons[symmetric]
        by(auto simp add: set_keys Cons_eq_filter_iff)
          (metis sorted_wrt.simps(2) sorted_append sorted_keys)
  qed
  thus ?thesis using Cons by (simp add: Bleast_def)
qed

hide_const (open) RBT_Set.Set RBT_Set.Coset

end
