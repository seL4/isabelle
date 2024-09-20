(*  Title:      HOL/Library/Finite_Map.thy
    Author:     Lars Hupel, TU München
*)

section \<open>Type of finite maps defined as a subtype of maps\<close>

theory Finite_Map
  imports FSet AList Conditional_Parametricity
  abbrevs "(=" = "\<subseteq>\<^sub>f"
begin

subsection \<open>Auxiliary constants and lemmas over \<^type>\<open>map\<close>\<close>

parametric_constant map_add_transfer[transfer_rule]: map_add_def
parametric_constant map_of_transfer[transfer_rule]: map_of_def

context includes lifting_syntax begin

abbreviation rel_map :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'c) \<Rightarrow> bool" where
"rel_map f \<equiv> (=) ===> rel_option f"

lemma ran_transfer[transfer_rule]: "(rel_map A ===> rel_set A) ran ran"
proof
  fix m n
  assume "rel_map A m n"
  show "rel_set A (ran m) (ran n)"
    proof (rule rel_setI)
      fix x
      assume "x \<in> ran m"
      then obtain a where "m a = Some x"
        unfolding ran_def by auto

      have "rel_option A (m a) (n a)"
        using \<open>rel_map A m n\<close>
        by (auto dest: rel_funD)
      then obtain y where "n a = Some y" "A x y"
        unfolding \<open>m a = _\<close>
        by cases auto
      then show "\<exists>y \<in> ran n. A x y"
        unfolding ran_def by blast
    next
      fix y
      assume "y \<in> ran n"
      then obtain a where "n a = Some y"
        unfolding ran_def by auto

      have "rel_option A (m a) (n a)"
        using \<open>rel_map A m n\<close>
        by (auto dest: rel_funD)
      then obtain x where "m a = Some x" "A x y"
        unfolding \<open>n a = _\<close>
        by cases auto
      then show "\<exists>x \<in> ran m. A x y"
        unfolding ran_def by blast
    qed
qed

lemma ran_alt_def: "ran m = (the \<circ> m) ` dom m"
unfolding ran_def dom_def by force

parametric_constant dom_transfer[transfer_rule]: dom_def

definition map_upd :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_upd k v m = m(k \<mapsto> v)"

parametric_constant map_upd_transfer[transfer_rule]: map_upd_def

definition map_filter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_filter P m = (\<lambda>x. if P x then m x else None)"

parametric_constant map_filter_transfer[transfer_rule]: map_filter_def

lemma map_filter_map_of[simp]: "map_filter P (map_of m) = map_of [(k, _) \<leftarrow> m. P k]"
proof
  fix x
  show "map_filter P (map_of m) x = map_of [(k, _) \<leftarrow> m. P k] x"
    by (induct m) (auto simp: map_filter_def)
qed

lemma map_filter_finite[intro]:
  assumes "finite (dom m)"
  shows "finite (dom (map_filter P m))"
proof -
  have "dom (map_filter P m) = Set.filter P (dom m)"
    unfolding map_filter_def Set.filter_def dom_def
    by auto
  then show ?thesis
    using assms
    by (simp add: Set.filter_def)
qed

definition map_drop :: "'a \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_drop a = map_filter (\<lambda>a'. a' \<noteq> a)"

parametric_constant map_drop_transfer[transfer_rule]: map_drop_def

definition map_drop_set :: "'a set \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_drop_set A = map_filter (\<lambda>a. a \<notin> A)"

parametric_constant map_drop_set_transfer[transfer_rule]: map_drop_set_def

definition map_restrict_set :: "'a set \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_restrict_set A = map_filter (\<lambda>a. a \<in> A)"

parametric_constant map_restrict_set_transfer[transfer_rule]: map_restrict_set_def

definition map_pred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool" where
"map_pred P m \<longleftrightarrow> (\<forall>x. case m x of None \<Rightarrow> True | Some y \<Rightarrow> P x y)"

parametric_constant map_pred_transfer[transfer_rule]: map_pred_def

definition rel_map_on_set :: "'a set \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'c) \<Rightarrow> bool" where
"rel_map_on_set S P = eq_onp (\<lambda>x. x \<in> S) ===> rel_option P"

definition set_of_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b) set" where
"set_of_map m = {(k, v)|k v. m k = Some v}"

lemma set_of_map_alt_def: "set_of_map m = (\<lambda>k. (k, the (m k))) ` dom m"
unfolding set_of_map_def dom_def
by auto

lemma set_of_map_finite: "finite (dom m) \<Longrightarrow> finite (set_of_map m)"
unfolding set_of_map_alt_def
by auto

lemma set_of_map_inj: "inj set_of_map"
proof
  fix x y
  assume "set_of_map x = set_of_map y"
  hence "(x a = Some b) = (y a = Some b)" for a b
    unfolding set_of_map_def by auto
  hence "x k = y k" for k
    by (metis not_None_eq)
  thus "x = y" ..
qed

lemma dom_comp: "dom (m \<circ>\<^sub>m n) \<subseteq> dom n"
unfolding map_comp_def dom_def
by (auto split: option.splits)

lemma dom_comp_finite: "finite (dom n) \<Longrightarrow> finite (dom (map_comp m n))"
by (metis finite_subset dom_comp)

parametric_constant map_comp_transfer[transfer_rule]: map_comp_def

end


subsection \<open>Abstract characterisation\<close>

typedef ('a, 'b) fmap = "{m. finite (dom m)} :: ('a \<rightharpoonup> 'b) set"
  morphisms fmlookup Abs_fmap
proof
  show "Map.empty \<in> {m. finite (dom m)}"
    by auto
qed

setup_lifting type_definition_fmap

lemma dom_fmlookup_finite[intro, simp]: "finite (dom (fmlookup m))"
using fmap.fmlookup by auto

lemma fmap_ext:
  assumes "\<And>x. fmlookup m x = fmlookup n x"
  shows "m = n"
using assms
by transfer' auto


subsection \<open>Operations\<close>

context
  includes fset.lifting
begin

lift_definition fmran :: "('a, 'b) fmap \<Rightarrow> 'b fset"
  is ran
  parametric ran_transfer
by (rule finite_ran)

lemma fmlookup_ran_iff: "y |\<in>| fmran m \<longleftrightarrow> (\<exists>x. fmlookup m x = Some y)"
by transfer' (auto simp: ran_def)

lemma fmranI: "fmlookup m x = Some y \<Longrightarrow> y |\<in>| fmran m" by (auto simp: fmlookup_ran_iff)

lemma fmranE[elim]:
  assumes "y |\<in>| fmran m"
  obtains x where "fmlookup m x = Some y"
using assms by (auto simp: fmlookup_ran_iff)

lift_definition fmdom :: "('a, 'b) fmap \<Rightarrow> 'a fset"
  is dom
  parametric dom_transfer
.

lemma fmlookup_dom_iff: "x |\<in>| fmdom m \<longleftrightarrow> (\<exists>a. fmlookup m x = Some a)"
by transfer' auto

lemma fmdom_notI: "fmlookup m x = None \<Longrightarrow> x |\<notin>| fmdom m" by (simp add: fmlookup_dom_iff)
lemma fmdomI: "fmlookup m x = Some y \<Longrightarrow> x |\<in>| fmdom m" by (simp add: fmlookup_dom_iff)
lemma fmdom_notD[dest]: "x |\<notin>| fmdom m \<Longrightarrow> fmlookup m x = None" by (simp add: fmlookup_dom_iff)

lemma fmdomE[elim]:
  assumes "x |\<in>| fmdom m"
  obtains y where "fmlookup m x = Some y"
using assms by (auto simp: fmlookup_dom_iff)

lift_definition fmdom' :: "('a, 'b) fmap \<Rightarrow> 'a set"
  is dom
  parametric dom_transfer
.

lemma fmlookup_dom'_iff: "x \<in> fmdom' m \<longleftrightarrow> (\<exists>a. fmlookup m x = Some a)"
by transfer' auto

lemma fmdom'_notI: "fmlookup m x = None \<Longrightarrow> x \<notin> fmdom' m" by (simp add: fmlookup_dom'_iff)
lemma fmdom'I: "fmlookup m x = Some y \<Longrightarrow> x \<in> fmdom' m" by (simp add: fmlookup_dom'_iff)
lemma fmdom'_notD[dest]: "x \<notin> fmdom' m \<Longrightarrow> fmlookup m x = None" by (simp add: fmlookup_dom'_iff)

lemma fmdom'E[elim]:
  assumes "x \<in> fmdom' m"
  obtains x y where "fmlookup m x = Some y"
using assms by (auto simp: fmlookup_dom'_iff)

lemma fmdom'_alt_def: "fmdom' m = fset (fmdom m)"
by transfer' force

lemma finite_fmdom'[simp]: "finite (fmdom' m)"
unfolding fmdom'_alt_def by simp

lemma dom_fmlookup[simp]: "dom (fmlookup m) = fmdom' m"
by transfer' simp

lift_definition fmempty :: "('a, 'b) fmap"
  is Map.empty
by simp

lemma fmempty_lookup[simp]: "fmlookup fmempty x = None"
by transfer' simp

lemma fmdom_empty[simp]: "fmdom fmempty = {||}" by transfer' simp
lemma fmdom'_empty[simp]: "fmdom' fmempty = {}" by transfer' simp
lemma fmran_empty[simp]: "fmran fmempty = fempty" by transfer' (auto simp: ran_def map_filter_def)

lift_definition fmupd :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_upd
  parametric map_upd_transfer
unfolding map_upd_def[abs_def]
by simp

lemma fmupd_lookup[simp]: "fmlookup (fmupd a b m) a' = (if a = a' then Some b else fmlookup m a')"
by transfer' (auto simp: map_upd_def)

lemma fmdom_fmupd[simp]: "fmdom (fmupd a b m) = finsert a (fmdom m)" by transfer (simp add: map_upd_def)
lemma fmdom'_fmupd[simp]: "fmdom' (fmupd a b m) = insert a (fmdom' m)" by transfer (simp add: map_upd_def)

lemma fmupd_reorder_neq:
  assumes "a \<noteq> b"
  shows "fmupd a x (fmupd b y m) = fmupd b y (fmupd a x m)"
using assms
by transfer' (auto simp: map_upd_def)

lemma fmupd_idem[simp]: "fmupd a x (fmupd a y m) = fmupd a x m"
by transfer' (auto simp: map_upd_def)

lift_definition fmfilter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_filter
  parametric map_filter_transfer
by auto

lemma fmdom_filter[simp]: "fmdom (fmfilter P m) = ffilter P (fmdom m)"
by transfer' (auto simp: map_filter_def Set.filter_def split: if_splits)

lemma fmdom'_filter[simp]: "fmdom' (fmfilter P m) = Set.filter P (fmdom' m)"
by transfer' (auto simp: map_filter_def Set.filter_def split: if_splits)

lemma fmlookup_filter[simp]: "fmlookup (fmfilter P m) x = (if P x then fmlookup m x else None)"
by transfer' (auto simp: map_filter_def)

lemma fmfilter_empty[simp]: "fmfilter P fmempty = fmempty"
by transfer' (auto simp: map_filter_def)

lemma fmfilter_true[simp]:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> P x"
  shows "fmfilter P m = m"
proof (rule fmap_ext)
  fix x
  have "fmlookup m x = None" if "\<not> P x"
    using that assms by fastforce
  then show "fmlookup (fmfilter P m) x = fmlookup m x"
    by simp
qed

lemma fmfilter_false[simp]:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> \<not> P x"
  shows "fmfilter P m = fmempty"
using assms by transfer' (fastforce simp: map_filter_def)

lemma fmfilter_comp[simp]: "fmfilter P (fmfilter Q m) = fmfilter (\<lambda>x. P x \<and> Q x) m"
by transfer' (auto simp: map_filter_def)

lemma fmfilter_comm: "fmfilter P (fmfilter Q m) = fmfilter Q (fmfilter P m)"
unfolding fmfilter_comp by meson

lemma fmfilter_cong[cong]:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> P x = Q x"
  shows "fmfilter P m = fmfilter Q m"
proof (rule fmap_ext)
  fix x
  have "fmlookup m x = None" if "P x \<noteq> Q x"
    using that assms by fastforce
  then show "fmlookup (fmfilter P m) x = fmlookup (fmfilter Q m) x"
    by auto
qed

lemma fmfilter_cong'[fundef_cong]:
  assumes "m = n" "\<And>x. x \<in> fmdom' m \<Longrightarrow> P x = Q x"
  shows "fmfilter P m = fmfilter Q n"
using assms(2) unfolding assms(1)
by (rule fmfilter_cong) (metis fmdom'I)

lemma fmfilter_upd[simp]:
  "fmfilter P (fmupd x y m) = (if P x then fmupd x y (fmfilter P m) else fmfilter P m)"
by transfer' (auto simp: map_upd_def map_filter_def)

lift_definition fmdrop :: "'a \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_drop
  parametric map_drop_transfer
unfolding map_drop_def by auto

lemma fmdrop_lookup[simp]: "fmlookup (fmdrop a m) a = None"
by transfer' (auto simp: map_drop_def map_filter_def)

lift_definition fmdrop_set :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_drop_set
  parametric map_drop_set_transfer
unfolding map_drop_set_def by auto

lift_definition fmdrop_fset :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_drop_set
  parametric map_drop_set_transfer
unfolding map_drop_set_def by auto

lift_definition fmrestrict_set :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_restrict_set
  parametric map_restrict_set_transfer
unfolding map_restrict_set_def by auto

lift_definition fmrestrict_fset :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_restrict_set
  parametric map_restrict_set_transfer
unfolding map_restrict_set_def by auto

lemma fmfilter_alt_defs:
  "fmdrop a = fmfilter (\<lambda>a'. a' \<noteq> a)"
  "fmdrop_set A = fmfilter (\<lambda>a. a \<notin> A)"
  "fmdrop_fset B = fmfilter (\<lambda>a. a |\<notin>| B)"
  "fmrestrict_set A = fmfilter (\<lambda>a. a \<in> A)"
  "fmrestrict_fset B = fmfilter (\<lambda>a. a |\<in>| B)"
by (transfer'; simp add: map_drop_def map_drop_set_def map_restrict_set_def)+

lemma fmdom_drop[simp]: "fmdom (fmdrop a m) = fmdom m - {|a|}" unfolding fmfilter_alt_defs by auto
lemma fmdom'_drop[simp]: "fmdom' (fmdrop a m) = fmdom' m - {a}" unfolding fmfilter_alt_defs by auto
lemma fmdom'_drop_set[simp]: "fmdom' (fmdrop_set A m) = fmdom' m - A" unfolding fmfilter_alt_defs by auto
lemma fmdom_drop_fset[simp]: "fmdom (fmdrop_fset A m) = fmdom m - A" unfolding fmfilter_alt_defs by auto
lemma fmdom'_restrict_set: "fmdom' (fmrestrict_set A m) \<subseteq> A" unfolding fmfilter_alt_defs by auto
lemma fmdom_restrict_fset: "fmdom (fmrestrict_fset A m) |\<subseteq>| A" unfolding fmfilter_alt_defs by auto

lemma fmdrop_fmupd: "fmdrop x (fmupd y z m) = (if x = y then fmdrop x m else fmupd y z (fmdrop x m))"
by transfer' (auto simp: map_drop_def map_filter_def map_upd_def)

lemma fmdrop_idle: "x |\<notin>| fmdom B \<Longrightarrow> fmdrop x B = B"
by transfer' (auto simp: map_drop_def map_filter_def)

lemma fmdrop_idle': "x \<notin> fmdom' B \<Longrightarrow> fmdrop x B = B"
by transfer' (auto simp: map_drop_def map_filter_def)

lemma fmdrop_fmupd_same: "fmdrop x (fmupd x y m) = fmdrop x m"
by transfer' (auto simp: map_drop_def map_filter_def map_upd_def)

lemma fmdom'_restrict_set_precise: "fmdom' (fmrestrict_set A m) = fmdom' m \<inter> A"
unfolding fmfilter_alt_defs by auto

lemma fmdom'_restrict_fset_precise: "fmdom (fmrestrict_fset A m) = fmdom m |\<inter>| A"
unfolding fmfilter_alt_defs by auto

lemma fmdom'_drop_fset[simp]: "fmdom' (fmdrop_fset A m) = fmdom' m - fset A"
unfolding fmfilter_alt_defs by transfer' (auto simp: map_filter_def split: if_splits)

lemma fmdom'_restrict_fset: "fmdom' (fmrestrict_fset A m) \<subseteq> fset A"
unfolding fmfilter_alt_defs by transfer' (auto simp: map_filter_def)

lemma fmlookup_drop[simp]:
  "fmlookup (fmdrop a m) x = (if x \<noteq> a then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_drop_set[simp]:
  "fmlookup (fmdrop_set A m) x = (if x \<notin> A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_drop_fset[simp]:
  "fmlookup (fmdrop_fset A m) x = (if x |\<notin>| A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_restrict_set[simp]:
  "fmlookup (fmrestrict_set A m) x = (if x \<in> A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_restrict_fset[simp]:
  "fmlookup (fmrestrict_fset A m) x = (if x |\<in>| A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_dom[simp]: "fmrestrict_set (fmdom' m) m = m"
by (rule fmap_ext) auto

lemma fmrestrict_fset_dom[simp]: "fmrestrict_fset (fmdom m) m = m"
by (rule fmap_ext) auto

lemma fmdrop_empty[simp]: "fmdrop a fmempty = fmempty"
unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_empty[simp]: "fmdrop_set A fmempty = fmempty"
unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_empty[simp]: "fmdrop_fset A fmempty = fmempty"
unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_fmdom[simp]: "fmdrop_fset (fmdom A) A = fmempty"
by transfer' (auto simp: map_drop_set_def map_filter_def)

lemma fmdrop_set_fmdom[simp]: "fmdrop_set (fmdom' A) A = fmempty"
by transfer' (auto simp: map_drop_set_def map_filter_def)

lemma fmrestrict_set_empty[simp]: "fmrestrict_set A fmempty = fmempty"
unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_empty[simp]: "fmrestrict_fset A fmempty = fmempty"
unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_null[simp]: "fmdrop_set {} m = m"
by (rule fmap_ext) auto

lemma fmdrop_fset_null[simp]: "fmdrop_fset {||} m = m"
by (rule fmap_ext) auto

lemma fmdrop_set_single[simp]: "fmdrop_set {a} m = fmdrop a m"
unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_single[simp]: "fmdrop_fset {|a|} m = fmdrop a m"
unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_null[simp]: "fmrestrict_set {} m = fmempty"
unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_null[simp]: "fmrestrict_fset {||} m = fmempty"
unfolding fmfilter_alt_defs by simp

lemma fmdrop_comm: "fmdrop a (fmdrop b m) = fmdrop b (fmdrop a m)"
unfolding fmfilter_alt_defs by (rule fmfilter_comm)

lemma fmdrop_set_insert[simp]: "fmdrop_set (insert x S) m = fmdrop x (fmdrop_set S m)"
by (rule fmap_ext) auto

lemma fmdrop_fset_insert[simp]: "fmdrop_fset (finsert x S) m = fmdrop x (fmdrop_fset S m)"
by (rule fmap_ext) auto

lemma fmrestrict_set_twice[simp]: "fmrestrict_set S (fmrestrict_set T m) = fmrestrict_set (S \<inter> T) m"
unfolding fmfilter_alt_defs by auto

lemma fmrestrict_fset_twice[simp]: "fmrestrict_fset S (fmrestrict_fset T m) = fmrestrict_fset (S |\<inter>| T) m"
unfolding fmfilter_alt_defs by auto

lemma fmrestrict_set_drop[simp]: "fmrestrict_set S (fmdrop b m) = fmrestrict_set (S - {b}) m"
unfolding fmfilter_alt_defs by auto

lemma fmrestrict_fset_drop[simp]: "fmrestrict_fset S (fmdrop b m) = fmrestrict_fset (S - {| b |}) m"
unfolding fmfilter_alt_defs by auto

lemma fmdrop_fmrestrict_set[simp]: "fmdrop b (fmrestrict_set S m) = fmrestrict_set (S - {b}) m"
by (rule fmap_ext) auto

lemma fmdrop_fmrestrict_fset[simp]: "fmdrop b (fmrestrict_fset S m) = fmrestrict_fset (S - {| b |}) m"
by (rule fmap_ext) auto

lemma fmdrop_idem[simp]: "fmdrop a (fmdrop a m) = fmdrop a m"
unfolding fmfilter_alt_defs by auto

lemma fmdrop_set_twice[simp]: "fmdrop_set S (fmdrop_set T m) = fmdrop_set (S \<union> T) m"
unfolding fmfilter_alt_defs by auto

lemma fmdrop_fset_twice[simp]: "fmdrop_fset S (fmdrop_fset T m) = fmdrop_fset (S |\<union>| T) m"
unfolding fmfilter_alt_defs by auto

lemma fmdrop_set_fmdrop[simp]: "fmdrop_set S (fmdrop b m) = fmdrop_set (insert b S) m"
by (rule fmap_ext) auto

lemma fmdrop_fset_fmdrop[simp]: "fmdrop_fset S (fmdrop b m) = fmdrop_fset (finsert b S) m"
by (rule fmap_ext) auto

lift_definition fmadd :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl \<open>++\<^sub>f\<close> 100)
  is map_add
  parametric map_add_transfer
  by simp

lemma fmlookup_add[simp]:
  "fmlookup (m ++\<^sub>f n) x = (if x |\<in>| fmdom n then fmlookup n x else fmlookup m x)"
  by transfer' (auto simp: map_add_def split: option.splits)

lemma fmdom_add[simp]: "fmdom (m ++\<^sub>f n) = fmdom m |\<union>| fmdom n" by transfer' auto
lemma fmdom'_add[simp]: "fmdom' (m ++\<^sub>f n) = fmdom' m \<union> fmdom' n" by transfer' auto

lemma fmadd_drop_left_dom: "fmdrop_fset (fmdom n) m ++\<^sub>f n = m ++\<^sub>f n"
  by (rule fmap_ext) auto

lemma fmadd_restrict_right_dom: "fmrestrict_fset (fmdom n) (m ++\<^sub>f n) = n"
  by (rule fmap_ext) auto

lemma fmfilter_add_distrib[simp]: "fmfilter P (m ++\<^sub>f n) = fmfilter P m ++\<^sub>f fmfilter P n"
  by transfer' (auto simp: map_filter_def map_add_def)

lemma fmdrop_add_distrib[simp]: "fmdrop a (m ++\<^sub>f n) = fmdrop a m ++\<^sub>f fmdrop a n"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_add_distrib[simp]: "fmdrop_set A (m ++\<^sub>f n) = fmdrop_set A m ++\<^sub>f fmdrop_set A n"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_add_distrib[simp]: "fmdrop_fset A (m ++\<^sub>f n) = fmdrop_fset A m ++\<^sub>f fmdrop_fset A n"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_add_distrib[simp]:
  "fmrestrict_set A (m ++\<^sub>f n) = fmrestrict_set A m ++\<^sub>f fmrestrict_set A n"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_add_distrib[simp]:
  "fmrestrict_fset A (m ++\<^sub>f n) = fmrestrict_fset A m ++\<^sub>f fmrestrict_fset A n"
  unfolding fmfilter_alt_defs by simp

lemma fmadd_empty[simp]: "fmempty ++\<^sub>f m = m" "m ++\<^sub>f fmempty = m"
  by (transfer'; auto)+

lemma fmadd_idempotent[simp]: "m ++\<^sub>f m = m"
  by transfer' (auto simp: map_add_def split: option.splits)

lemma fmadd_assoc[simp]: "m ++\<^sub>f (n ++\<^sub>f p) = m ++\<^sub>f n ++\<^sub>f p"
  by transfer' simp

lemma fmadd_fmupd[simp]: "m ++\<^sub>f fmupd a b n = fmupd a b (m ++\<^sub>f n)"
  by (rule fmap_ext) simp

lift_definition fmpred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool"
  is map_pred
  parametric map_pred_transfer
  .

lemma fmpredI[intro]:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> P x y"
  shows "fmpred P m"
  using assms
  by transfer' (auto simp: map_pred_def split: option.splits)

lemma fmpredD[dest]: "fmpred P m \<Longrightarrow> fmlookup m x = Some y \<Longrightarrow> P x y"
  by transfer' (auto simp: map_pred_def split: option.split_asm)

lemma fmpred_iff: "fmpred P m \<longleftrightarrow> (\<forall>x y. fmlookup m x = Some y \<longrightarrow> P x y)"
  by auto

lemma fmpred_alt_def: "fmpred P m \<longleftrightarrow> fBall (fmdom m) (\<lambda>x. P x (the (fmlookup m x)))"
  unfolding fmpred_iff
  using fmdomI by fastforce

lemma fmpred_mono_strong:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  shows "fmpred P m \<Longrightarrow> fmpred Q m"
using assms unfolding fmpred_iff by auto

lemma fmpred_mono[mono]: "P \<le> Q \<Longrightarrow> fmpred P \<le> fmpred Q"
  by auto

lemma fmpred_empty[intro!, simp]: "fmpred P fmempty"
  by auto

lemma fmpred_upd[intro]: "fmpred P m \<Longrightarrow> P x y \<Longrightarrow> fmpred P (fmupd x y m)"
  by transfer' (auto simp: map_pred_def map_upd_def)

lemma fmpred_updD[dest]: "fmpred P (fmupd x y m) \<Longrightarrow> P x y"
  by auto

lemma fmpred_add[intro]: "fmpred P m \<Longrightarrow> fmpred P n \<Longrightarrow> fmpred P (m ++\<^sub>f n)"
  by transfer' (auto simp: map_pred_def map_add_def split: option.splits)

lemma fmpred_filter[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmfilter Q m)"
  by transfer' (auto simp: map_pred_def map_filter_def)

lemma fmpred_drop[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmdrop a m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_drop_set[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmdrop_set A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_drop_fset[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmdrop_fset A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_restrict_set[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmrestrict_set A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_restrict_fset[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmrestrict_fset A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_cases[consumes 1]:
  assumes "fmpred P m"
  obtains (none) "fmlookup m x = None" | (some) y where "fmlookup m x = Some y" "P x y"
using assms by auto

lift_definition fmsubset :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool" (infix \<open>\<subseteq>\<^sub>f\<close> 50)
  is map_le
.

lemma fmsubset_alt_def: "m \<subseteq>\<^sub>f n \<longleftrightarrow> fmpred (\<lambda>k v. fmlookup n k = Some v) m"
by transfer' (auto simp: map_pred_def map_le_def dom_def split: option.splits)

lemma fmsubset_pred: "fmpred P m \<Longrightarrow> n \<subseteq>\<^sub>f m \<Longrightarrow> fmpred P n"
unfolding fmsubset_alt_def fmpred_iff
by auto

lemma fmsubset_filter_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmfilter P m \<subseteq>\<^sub>f fmfilter P n"
unfolding fmsubset_alt_def fmpred_iff
by auto

lemma fmsubset_drop_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmdrop a m \<subseteq>\<^sub>f fmdrop a n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_drop_set_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmdrop_set A m \<subseteq>\<^sub>f fmdrop_set A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_drop_fset_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmdrop_fset A m \<subseteq>\<^sub>f fmdrop_fset A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_restrict_set_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmrestrict_set A m \<subseteq>\<^sub>f fmrestrict_set A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_restrict_fset_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmrestrict_fset A m \<subseteq>\<^sub>f fmrestrict_fset A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmfilter_subset[simp]: "fmfilter P m \<subseteq>\<^sub>f m"
unfolding fmsubset_alt_def fmpred_iff by auto

lemma fmsubset_drop[simp]: "fmdrop a m \<subseteq>\<^sub>f m"
unfolding fmfilter_alt_defs by (rule fmfilter_subset)

lemma fmsubset_drop_set[simp]: "fmdrop_set S m \<subseteq>\<^sub>f m"
unfolding fmfilter_alt_defs by (rule fmfilter_subset)

lemma fmsubset_drop_fset[simp]: "fmdrop_fset S m \<subseteq>\<^sub>f m"
unfolding fmfilter_alt_defs by (rule fmfilter_subset)

lemma fmsubset_restrict_set[simp]: "fmrestrict_set S m \<subseteq>\<^sub>f m"
unfolding fmfilter_alt_defs by (rule fmfilter_subset)

lemma fmsubset_restrict_fset[simp]: "fmrestrict_fset S m \<subseteq>\<^sub>f m"
unfolding fmfilter_alt_defs by (rule fmfilter_subset)

lift_definition fset_of_fmap :: "('a, 'b) fmap \<Rightarrow> ('a \<times> 'b) fset" is set_of_map
  by (rule set_of_map_finite)

lemma fset_of_fmap_inj[intro, simp]: "inj fset_of_fmap"
  apply rule
  apply transfer'
  using set_of_map_inj unfolding inj_def by auto

lemma fset_of_fmap_iff[simp]: "(a, b) |\<in>| fset_of_fmap m \<longleftrightarrow> fmlookup m a = Some b"
by transfer' (auto simp: set_of_map_def)

lemma fset_of_fmap_iff': "(a, b) \<in> fset (fset_of_fmap m) \<longleftrightarrow> fmlookup m a = Some b"
  by simp

lift_definition fmap_of_list :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) fmap"
  is map_of
  parametric map_of_transfer
by (rule finite_dom_map_of)

lemma fmap_of_list_simps[simp]:
  "fmap_of_list [] = fmempty"
  "fmap_of_list ((k, v) # kvs) = fmupd k v (fmap_of_list kvs)"
  by (transfer, simp add: map_upd_def)+

lemma fmap_of_list_app[simp]: "fmap_of_list (xs @ ys) = fmap_of_list ys ++\<^sub>f fmap_of_list xs"
  by transfer' simp

lemma fmupd_alt_def: "fmupd k v m = m ++\<^sub>f fmap_of_list [(k, v)]"
  by simp

lemma fmpred_of_list[intro]:
  assumes "\<And>k v. (k, v) \<in> set xs \<Longrightarrow> P k v"
  shows "fmpred P (fmap_of_list xs)"
  using assms
  by (induction xs) (transfer'; auto simp: map_pred_def)+

lemma fmap_of_list_SomeD: "fmlookup (fmap_of_list xs) k = Some v \<Longrightarrow> (k, v) \<in> set xs"
  by transfer' (auto dest: map_of_SomeD)

lemma fmdom_fmap_of_list[simp]: "fmdom (fmap_of_list xs) = fset_of_list (map fst xs)"
  by transfer' (simp add: dom_map_of_conv_image_fst)

lift_definition fmrel_on_fset :: "'a fset \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap \<Rightarrow> bool"
  is rel_map_on_set
.

lemma fmrel_on_fset_alt_def: "fmrel_on_fset S P m n \<longleftrightarrow> fBall S (\<lambda>x. rel_option P (fmlookup m x) (fmlookup n x))"
by transfer' (auto simp: rel_map_on_set_def eq_onp_def rel_fun_def)

lemma fmrel_on_fsetI[intro]:
  assumes "\<And>x. x |\<in>| S \<Longrightarrow> rel_option P (fmlookup m x) (fmlookup n x)"
  shows "fmrel_on_fset S P m n"
  by (simp add: assms fmrel_on_fset_alt_def)

lemma fmrel_on_fset_mono[mono]: "R \<le> Q \<Longrightarrow> fmrel_on_fset S R \<le> fmrel_on_fset S Q"
  unfolding fmrel_on_fset_alt_def[abs_def]
  using option.rel_mono by blast

lemma fmrel_on_fsetD: "x |\<in>| S \<Longrightarrow> fmrel_on_fset S P m n \<Longrightarrow> rel_option P (fmlookup m x) (fmlookup n x)"
  unfolding fmrel_on_fset_alt_def
  by auto

lemma fmrel_on_fsubset: "fmrel_on_fset S R m n \<Longrightarrow> T |\<subseteq>| S \<Longrightarrow> fmrel_on_fset T R m n"
  unfolding fmrel_on_fset_alt_def
  by auto

lemma fmrel_on_fset_unionI:
  "fmrel_on_fset A R m n \<Longrightarrow> fmrel_on_fset B R m n \<Longrightarrow> fmrel_on_fset (A |\<union>| B) R m n"
  unfolding fmrel_on_fset_alt_def
  by auto

lemma fmrel_on_fset_updateI:
  assumes "fmrel_on_fset S P m n" "P v\<^sub>1 v\<^sub>2"
  shows "fmrel_on_fset (finsert k S) P (fmupd k v\<^sub>1 m) (fmupd k v\<^sub>2 n)"
  using assms
  unfolding fmrel_on_fset_alt_def
  by auto

lift_definition fmimage :: "('a, 'b) fmap \<Rightarrow> 'a fset \<Rightarrow> 'b fset" is "\<lambda>m S. {b|a b. m a = Some b \<and> a \<in> S}"
  by (smt (verit, del_insts) Collect_mono_iff finite_surj ran_alt_def ran_def)

lemma fmimage_alt_def: "fmimage m S = fmran (fmrestrict_fset S m)"
  by transfer' (auto simp: ran_def map_restrict_set_def map_filter_def)

lemma fmimage_empty[simp]: "fmimage m fempty = fempty"
  by transfer' auto

lemma fmimage_subset_ran[simp]: "fmimage m S |\<subseteq>| fmran m"
  by transfer' (auto simp: ran_def)

lemma fmimage_dom[simp]: "fmimage m (fmdom m) = fmran m"
  by transfer' (auto simp: ran_def)

lemma fmimage_inter: "fmimage m (A |\<inter>| B) |\<subseteq>| fmimage m A |\<inter>| fmimage m B"
  by transfer' auto

lemma fimage_inter_dom[simp]:
  "fmimage m (fmdom m |\<inter>| A) = fmimage m A"
  "fmimage m (A |\<inter>| fmdom m) = fmimage m A"
  by (transfer'; auto)+

lemma fmimage_union[simp]: "fmimage m (A |\<union>| B) = fmimage m A |\<union>| fmimage m B"
  by transfer' auto

lemma fmimage_Union[simp]: "fmimage m (ffUnion A) = ffUnion (fmimage m |`| A)"
  by transfer' auto

lemma fmimage_filter[simp]: "fmimage (fmfilter P m) A = fmimage m (ffilter P A)"
  by transfer' (auto simp: map_filter_def)

lemma fmimage_drop[simp]: "fmimage (fmdrop a m) A = fmimage m (A - {|a|})"
  by (simp add: fmimage_alt_def)

lemma fmimage_drop_fset[simp]: "fmimage (fmdrop_fset B m) A = fmimage m (A - B)"
  by transfer' (auto simp: map_filter_def map_drop_set_def)

lemma fmimage_restrict_fset[simp]: "fmimage (fmrestrict_fset B m) A = fmimage m (A |\<inter>| B)"
  by transfer' (auto simp: map_filter_def map_restrict_set_def)

lemma fmfilter_ran[simp]: "fmran (fmfilter P m) = fmimage m (ffilter P (fmdom m))"
  by transfer' (auto simp: ran_def map_filter_def)

lemma fmran_drop[simp]: "fmran (fmdrop a m) = fmimage m (fmdom m - {|a|})"
  by transfer' (auto simp: ran_def map_drop_def map_filter_def)

lemma fmran_drop_fset[simp]: "fmran (fmdrop_fset A m) = fmimage m (fmdom m - A)"
  by transfer' (auto simp: ran_def map_drop_set_def map_filter_def)

lemma fmran_restrict_fset: "fmran (fmrestrict_fset A m) = fmimage m (fmdom m |\<inter>| A)"
  by transfer' (auto simp: ran_def map_restrict_set_def map_filter_def)

lemma fmlookup_image_iff: "y |\<in>| fmimage m A \<longleftrightarrow> (\<exists>x. fmlookup m x = Some y \<and> x |\<in>| A)"
  by transfer' (auto simp: ran_def)

lemma fmimageI: "fmlookup m x = Some y \<Longrightarrow> x |\<in>| A \<Longrightarrow> y |\<in>| fmimage m A"
  by (auto simp: fmlookup_image_iff)

lemma fmimageE[elim]:
  assumes "y |\<in>| fmimage m A"
  obtains x where "fmlookup m x = Some y" "x |\<in>| A"
  using assms by (auto simp: fmlookup_image_iff)

lift_definition fmcomp :: "('b, 'c) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap" (infixl \<open>\<circ>\<^sub>f\<close> 55)
  is map_comp
  parametric map_comp_transfer
  by (rule dom_comp_finite)

lemma fmlookup_comp[simp]: "fmlookup (m \<circ>\<^sub>f n) x = Option.bind (fmlookup n x) (fmlookup m)"
  by transfer' (auto simp: map_comp_def split: option.splits)

end


subsection \<open>BNF setup\<close>

lift_bnf ('a, fmran': 'b) fmap [wits: Map.empty]
  for map: fmmap
      rel: fmrel
  by auto

declare fmap.pred_mono[mono]


lemma fmran'_alt_def: "fmran' m = fset (fmran m)"
  including fset.lifting
  by transfer' (auto simp: ran_def fun_eq_iff)

lemma fmlookup_ran'_iff: "y \<in> fmran' m \<longleftrightarrow> (\<exists>x. fmlookup m x = Some y)"
  by transfer' (auto simp: ran_def)

lemma fmran'I: "fmlookup m x = Some y \<Longrightarrow> y \<in> fmran' m" 
  by (auto simp: fmlookup_ran'_iff)

lemma fmran'E[elim]:
  assumes "y \<in> fmran' m"
  obtains x where "fmlookup m x = Some y"
using assms by (auto simp: fmlookup_ran'_iff)

lemma fmrel_iff: "fmrel R m n \<longleftrightarrow> (\<forall>x. rel_option R (fmlookup m x) (fmlookup n x))"
by transfer' (auto simp: rel_fun_def)

lemma fmrelI[intro]:
  assumes "\<And>x. rel_option R (fmlookup m x) (fmlookup n x)"
  shows "fmrel R m n"
  using assms
  by transfer' auto

lemma fmrel_upd[intro]: "fmrel P m n \<Longrightarrow> P x y \<Longrightarrow> fmrel P (fmupd k x m) (fmupd k y n)"
  by transfer' (auto simp: map_upd_def rel_fun_def)

lemma fmrelD[dest]: "fmrel P m n \<Longrightarrow> rel_option P (fmlookup m x) (fmlookup n x)"
  by transfer' (auto simp: rel_fun_def)

lemma fmrel_addI[intro]:
  assumes "fmrel P m n" "fmrel P a b"
  shows "fmrel P (m ++\<^sub>f a) (n ++\<^sub>f b)"
  by (smt (verit, del_insts) assms domIff fmdom.rep_eq fmlookup_add fmrel_iff option.rel_sel)

lemma fmrel_cases[consumes 1]:
  assumes "fmrel P m n"
  obtains (none) "fmlookup m x = None" "fmlookup n x = None"
        | (some) a b where "fmlookup m x = Some a" "fmlookup n x = Some b" "P a b"
proof -
  from assms have "rel_option P (fmlookup m x) (fmlookup n x)"
    by auto
  then show thesis
    using none some
    by (cases rule: option.rel_cases) auto
qed

lemma fmrel_filter[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmfilter Q m) (fmfilter Q n)"
unfolding fmrel_iff by auto

lemma fmrel_drop[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmdrop a m) (fmdrop a n)"
unfolding fmfilter_alt_defs by blast

lemma fmrel_drop_set[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmdrop_set A m) (fmdrop_set A n)"
unfolding fmfilter_alt_defs by blast

lemma fmrel_drop_fset[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmdrop_fset A m) (fmdrop_fset A n)"
unfolding fmfilter_alt_defs by blast

lemma fmrel_restrict_set[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmrestrict_set A m) (fmrestrict_set A n)"
unfolding fmfilter_alt_defs by blast

lemma fmrel_restrict_fset[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmrestrict_fset A m) (fmrestrict_fset A n)"
unfolding fmfilter_alt_defs by blast

lemma fmrel_on_fset_fmrel_restrict:
  "fmrel_on_fset S P m n \<longleftrightarrow> fmrel P (fmrestrict_fset S m) (fmrestrict_fset S n)"
unfolding fmrel_on_fset_alt_def fmrel_iff
by auto

lemma fmrel_on_fset_refl_strong:
  assumes "\<And>x y. x |\<in>| S \<Longrightarrow> fmlookup m x = Some y \<Longrightarrow> P y y"
  shows "fmrel_on_fset S P m m"
unfolding fmrel_on_fset_fmrel_restrict fmrel_iff
using assms
by (simp add: option.rel_sel)

lemma fmrel_on_fset_addI:
  assumes "fmrel_on_fset S P m n" "fmrel_on_fset S P a b"
  shows "fmrel_on_fset S P (m ++\<^sub>f a) (n ++\<^sub>f b)"
using assms
unfolding fmrel_on_fset_fmrel_restrict
by auto

lemma fmrel_fmdom_eq:
  assumes "fmrel P x y"
  shows "fmdom x = fmdom y"
proof -
  have "a |\<in>| fmdom x \<longleftrightarrow> a |\<in>| fmdom y" for a
    proof -
      have "rel_option P (fmlookup x a) (fmlookup y a)"
        using assms by (simp add: fmrel_iff)
      thus ?thesis
        by cases (auto intro: fmdomI)
    qed
  thus ?thesis
    by auto
qed

lemma fmrel_fmdom'_eq: "fmrel P x y \<Longrightarrow> fmdom' x = fmdom' y"
unfolding fmdom'_alt_def
by (metis fmrel_fmdom_eq)

lemma fmrel_rel_fmran:
  assumes "fmrel P x y"
  shows "rel_fset P (fmran x) (fmran y)"
proof -
  {
    fix b
    assume "b |\<in>| fmran x"
    then obtain a where "fmlookup x a = Some b"
      by auto
    moreover have "rel_option P (fmlookup x a) (fmlookup y a)"
      using assms by auto
    ultimately have "\<exists>b'. b' |\<in>| fmran y \<and> P b b'"
      by (metis option_rel_Some1 fmranI)
  }
  moreover
  {
    fix b
    assume "b |\<in>| fmran y"
    then obtain a where "fmlookup y a = Some b"
      by auto
    moreover have "rel_option P (fmlookup x a) (fmlookup y a)"
      using assms by auto
    ultimately have "\<exists>b'. b' |\<in>| fmran x \<and> P b' b"
      by (metis option_rel_Some2 fmranI)
  }
  ultimately show ?thesis
    unfolding rel_fset_alt_def
    by auto
qed

lemma fmrel_rel_fmran': "fmrel P x y \<Longrightarrow> rel_set P (fmran' x) (fmran' y)"
  unfolding fmran'_alt_def
  by (metis fmrel_rel_fmran rel_fset_fset)

lemma pred_fmap_fmpred[simp]: "pred_fmap P = fmpred (\<lambda>_. P)"
  unfolding fmap.pred_set fmran'_alt_def
  using fmranI by fastforce

lemma pred_fmap_id[simp]: "pred_fmap id (fmmap f m) \<longleftrightarrow> pred_fmap f m"
  unfolding fmap.pred_set fmap.set_map
  by simp

lemma pred_fmapD: "pred_fmap P m \<Longrightarrow> x |\<in>| fmran m \<Longrightarrow> P x"
  by auto

lemma fmlookup_map[simp]: "fmlookup (fmmap f m) x = map_option f (fmlookup m x)"
  by transfer' auto

lemma fmpred_map[simp]: "fmpred P (fmmap f m) \<longleftrightarrow> fmpred (\<lambda>k v. P k (f v)) m"
  unfolding fmpred_iff pred_fmap_def fmap.set_map
  by auto

lemma fmpred_id[simp]: "fmpred (\<lambda>_. id) (fmmap f m) \<longleftrightarrow> fmpred (\<lambda>_. f) m"
  by simp

lemma fmmap_add[simp]: "fmmap f (m ++\<^sub>f n) = fmmap f m ++\<^sub>f fmmap f n"
  by transfer' (auto simp: map_add_def fun_eq_iff split: option.splits)

lemma fmmap_empty[simp]: "fmmap f fmempty = fmempty"
  by transfer auto

lemma fmdom_map[simp]: "fmdom (fmmap f m) = fmdom m"
  including fset.lifting
  by transfer' simp

lemma fmdom'_map[simp]: "fmdom' (fmmap f m) = fmdom' m"
  by transfer' simp

lemma fmran_fmmap[simp]: "fmran (fmmap f m) = f |`| fmran m"
  including fset.lifting
  by transfer' (auto simp: ran_def)

lemma fmran'_fmmap[simp]: "fmran' (fmmap f m) = f ` fmran' m"
  by transfer' (auto simp: ran_def)

lemma fmfilter_fmmap[simp]: "fmfilter P (fmmap f m) = fmmap f (fmfilter P m)"
  by transfer' (auto simp: map_filter_def)

lemma fmdrop_fmmap[simp]: "fmdrop a (fmmap f m) = fmmap f (fmdrop a m)" 
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_fmmap[simp]: "fmdrop_set A (fmmap f m) = fmmap f (fmdrop_set A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_fmmap[simp]: "fmdrop_fset A (fmmap f m) = fmmap f (fmdrop_fset A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_fmmap[simp]: "fmrestrict_set A (fmmap f m) = fmmap f (fmrestrict_set A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_fmmap[simp]: "fmrestrict_fset A (fmmap f m) = fmmap f (fmrestrict_fset A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmmap_subset[intro]: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmmap f m \<subseteq>\<^sub>f fmmap f n"
  by transfer' (auto simp: map_le_def)

lemma fmmap_fset_of_fmap: "fset_of_fmap (fmmap f m) = (\<lambda>(k, v). (k, f v)) |`| fset_of_fmap m"
  including fset.lifting
  by transfer' (auto simp: set_of_map_def)

lemma fmmap_fmupd: "fmmap f (fmupd x y m) = fmupd x (f y) (fmmap f m)"
  by transfer' (auto simp: fun_eq_iff map_upd_def)

subsection \<open>\<^const>\<open>size\<close> setup\<close>

definition size_fmap :: "('a \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> nat" where
[simp]: "size_fmap f g m = size_fset (\<lambda>(a, b). f a + g b) (fset_of_fmap m)"

instantiation fmap :: (type, type) size begin

definition size_fmap where
size_fmap_overloaded_def: "size_fmap = Finite_Map.size_fmap (\<lambda>_. 0) (\<lambda>_. 0)"

instance ..

end

lemma size_fmap_overloaded_simps[simp]: "size x = size (fset_of_fmap x)"
  unfolding size_fmap_overloaded_def
  by simp

lemma fmap_size_o_map: "size_fmap f g \<circ> fmmap h = size_fmap f (g \<circ> h)"
proof -
  have inj: "inj_on (\<lambda>(k, v). (k, h v)) (fset (fset_of_fmap m))" for m
    using inj_on_def by force
  show ?thesis
  unfolding size_fmap_def
  apply (clarsimp simp: fun_eq_iff fmmap_fset_of_fmap sum.reindex [OF inj])
  by (rule sum.cong) (auto split: prod.splits)
qed

setup \<open>
BNF_LFP_Size.register_size_global \<^type_name>\<open>fmap\<close> \<^const_name>\<open>size_fmap\<close>
  @{thm size_fmap_overloaded_def} @{thms size_fmap_def size_fmap_overloaded_simps}
  @{thms fmap_size_o_map}
\<close>


subsection \<open>Additional operations\<close>

lift_definition fmmap_keys :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap" is
  "\<lambda>f m a. map_option (f a) (m a)"
  unfolding dom_def
  by simp

lemma fmpred_fmmap_keys[simp]: "fmpred P (fmmap_keys f m) = fmpred (\<lambda>a b. P a (f a b)) m"
  by transfer' (auto simp: map_pred_def split: option.splits)

lemma fmdom_fmmap_keys[simp]: "fmdom (fmmap_keys f m) = fmdom m"
  including fset.lifting
  by transfer' auto

lemma fmlookup_fmmap_keys[simp]: "fmlookup (fmmap_keys f m) x = map_option (f x) (fmlookup m x)"
  by transfer' simp

lemma fmfilter_fmmap_keys[simp]: "fmfilter P (fmmap_keys f m) = fmmap_keys f (fmfilter P m)"
  by transfer' (auto simp: map_filter_def)

lemma fmdrop_fmmap_keys[simp]: "fmdrop a (fmmap_keys f m) = fmmap_keys f (fmdrop a m)"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_fmmap_keys[simp]: "fmdrop_set A (fmmap_keys f m) = fmmap_keys f (fmdrop_set A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_fmmap_keys[simp]: "fmdrop_fset A (fmmap_keys f m) = fmmap_keys f (fmdrop_fset A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_fmmap_keys[simp]: "fmrestrict_set A (fmmap_keys f m) = fmmap_keys f (fmrestrict_set A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_fmmap_keys[simp]: "fmrestrict_fset A (fmmap_keys f m) = fmmap_keys f (fmrestrict_fset A m)"
  unfolding fmfilter_alt_defs by simp

lemma fmmap_keys_subset[intro]: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmmap_keys f m \<subseteq>\<^sub>f fmmap_keys f n"
  by transfer' (auto simp: map_le_def dom_def)

definition sorted_list_of_fmap :: "('a::linorder, 'b) fmap \<Rightarrow> ('a \<times> 'b) list" where
  "sorted_list_of_fmap m = map (\<lambda>k. (k, the (fmlookup m k))) (sorted_list_of_fset (fmdom m))"

lemma list_all_sorted_list[simp]: "list_all P (sorted_list_of_fmap m) = fmpred (curry P) m"
unfolding sorted_list_of_fmap_def curry_def list.pred_map
  by (smt (verit, best) Ball_set comp_def fmpred_alt_def sorted_list_of_fset_simps(1))

lemma map_of_sorted_list[simp]: "map_of (sorted_list_of_fmap m) = fmlookup m"
  unfolding sorted_list_of_fmap_def
  including fset.lifting
  by transfer (simp add: map_of_map_keys)


subsection \<open>Additional properties\<close>

lemma fmchoice':
  assumes "finite S" "\<forall>x \<in> S. \<exists>y. Q x y"
  shows "\<exists>m. fmdom' m = S \<and> fmpred Q m"
proof -
  obtain f where f: "Q x (f x)" if "x \<in> S" for x
    using assms by metis
  define f' where "f' x = (if x \<in> S then Some (f x) else None)" for x

  have "eq_onp (\<lambda>m. finite (dom m)) f' f'"
    unfolding eq_onp_def f'_def dom_def using assms by auto

  show ?thesis
    apply (rule exI[where x = "Abs_fmap f'"])
    apply (subst fmpred.abs_eq, fact)
    apply (subst fmdom'.abs_eq, fact)
    unfolding f'_def dom_def map_pred_def using f
    by auto
qed

subsection \<open>Lifting/transfer setup\<close>

context includes lifting_syntax begin

lemma fmempty_transfer[simp, intro, transfer_rule]: "fmrel P fmempty fmempty"
  by transfer auto

lemma fmadd_transfer[transfer_rule]:
  "(fmrel P ===> fmrel P ===> fmrel P) fmadd fmadd"
  by (intro fmrel_addI rel_funI)

lemma fmupd_transfer[transfer_rule]:
  "((=) ===> P ===> fmrel P ===> fmrel P) fmupd fmupd"
  by auto

end

lemma Quotient_fmap_bnf[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (fmrel R) (fmmap Abs) (fmmap Rep) (fmrel T)"
unfolding Quotient_alt_def4 proof safe
  fix m n
  assume "fmrel T m n"
  then have "fmlookup (fmmap Abs m) x = fmlookup n x" for x
    using assms unfolding Quotient_alt_def 
      by (cases rule: fmrel_cases[where x = x]) auto
  then show "fmmap Abs m = n"
    by (rule fmap_ext)
next
  fix m
  show "fmrel T (fmmap Rep m) m"
    unfolding fmap.rel_map
    by (metis (mono_tags) Quotient_alt_def assms fmap.rel_refl)
next
  from assms have "R = T OO T\<inverse>\<inverse>"
    unfolding Quotient_alt_def4 by simp
  then show "fmrel R = fmrel T OO (fmrel T)\<inverse>\<inverse>"
    by (simp add: fmap.rel_compp fmap.rel_conversep)
qed


subsection \<open>View as datatype\<close>

lemma fmap_distinct[simp]:
  "fmempty \<noteq> fmupd k v m"
  "fmupd k v m \<noteq> fmempty"
  by (transfer'; auto simp: map_upd_def fun_eq_iff)+

lifting_update fmap.lifting

lemma fmap_exhaust[cases type: fmap]:
  obtains (fmempty) "m = fmempty"
        | (fmupd) x y m' where "m = fmupd x y m'" "x |\<notin>| fmdom m'"
using that including fmap.lifting fset.lifting
proof transfer
  fix m P
  assume "finite (dom m)"
  assume empty: P if "m = Map.empty"
  assume map_upd: P if "finite (dom m')" "m = map_upd x y m'" "x \<notin> dom m'" for x y m'

  show P
    proof (cases "m = Map.empty")
      case True thus ?thesis using empty by simp
    next
      case False
      hence "dom m \<noteq> {}" by simp
      then obtain x where "x \<in> dom m" by blast

      let ?m' = "map_drop x m"

      show ?thesis
        proof (rule map_upd)
          show "finite (dom ?m')"
            using \<open>finite (dom m)\<close>
            unfolding map_drop_def
            by auto
        next
          show "m = map_upd x (the (m x)) ?m'"
            using \<open>x \<in> dom m\<close> unfolding map_drop_def map_filter_def map_upd_def
            by auto
        next
          show "x \<notin> dom ?m'"
            unfolding map_drop_def map_filter_def
            by auto
        qed
    qed
qed

lemma fmap_induct[case_names fmempty fmupd, induct type: fmap]:
  assumes "P fmempty"
  assumes "(\<And>x y m. P m \<Longrightarrow> fmlookup m x = None \<Longrightarrow> P (fmupd x y m))"
  shows "P m"
proof (induction "fmdom m" arbitrary: m rule: fset_induct_stronger)
  case empty
  hence "m = fmempty"
    by (metis fmrestrict_fset_dom fmrestrict_fset_null)
  with assms show ?case
    by simp
next
  case (insert x S)
  hence "S = fmdom (fmdrop x m)"
    by auto
  with insert have "P (fmdrop x m)"
    by auto
  moreover
  obtain y where "fmlookup m x = Some y"
    using insert.hyps by force
  hence "m = fmupd x y (fmdrop x m)"
    by (auto intro: fmap_ext)
  ultimately show ?case
    by (metis assms(2) fmdrop_lookup)
qed


subsection \<open>Code setup\<close>

instantiation fmap :: (type, equal) equal begin

definition "equal_fmap \<equiv> fmrel HOL.equal"

instance proof
  fix m n :: "('a, 'b) fmap"
  have "fmrel (=) m n \<longleftrightarrow> (m = n)"
    by transfer' (simp add: option.rel_eq rel_fun_eq)
  then show "equal_class.equal m n \<longleftrightarrow> (m = n)"
    unfolding equal_fmap_def
    by (simp add: equal_eq[abs_def])
qed

end

lemma fBall_alt_def: "fBall S P \<longleftrightarrow> (\<forall>x. x |\<in>| S \<longrightarrow> P x)"
by force

lemma fmrel_code:
  "fmrel R m n \<longleftrightarrow>
    fBall (fmdom m) (\<lambda>x. rel_option R (fmlookup m x) (fmlookup n x)) \<and>
    fBall (fmdom n) (\<lambda>x. rel_option R (fmlookup m x) (fmlookup n x))"
unfolding fmrel_iff fmlookup_dom_iff fBall_alt_def
by (metis option.collapse option.rel_sel)

lemmas [code] =
  fmrel_code
  fmran'_alt_def
  fmdom'_alt_def
  fmfilter_alt_defs
  pred_fmap_fmpred
  fmsubset_alt_def
  fmupd_alt_def
  fmrel_on_fset_alt_def
  fmpred_alt_def


code_datatype fmap_of_list
quickcheck_generator fmap constructors: fmap_of_list

context includes fset.lifting begin

lemma fmlookup_of_list[code]: "fmlookup (fmap_of_list m) = map_of m"
by transfer simp

lemma fmempty_of_list[code]: "fmempty = fmap_of_list []"
by transfer simp

lemma fmran_of_list[code]: "fmran (fmap_of_list m) = snd |`| fset_of_list (AList.clearjunk m)"
by transfer (auto simp: ran_map_of)

lemma fmdom_of_list[code]: "fmdom (fmap_of_list m) = fst |`| fset_of_list m"
by transfer (auto simp: dom_map_of_conv_image_fst)

lemma fmfilter_of_list[code]: "fmfilter P (fmap_of_list m) = fmap_of_list (filter (\<lambda>(k, _). P k) m)"
by transfer' auto

lemma fmadd_of_list[code]: "fmap_of_list m ++\<^sub>f fmap_of_list n = fmap_of_list (AList.merge m n)"
by transfer (simp add: merge_conv')

lemma fmmap_of_list[code]: "fmmap f (fmap_of_list m) = fmap_of_list (map (apsnd f) m)"
  apply transfer
  by (metis (no_types, lifting) apsnd_conv map_eq_conv map_of_map old.prod.case old.prod.exhaust)

lemma fmmap_keys_of_list[code]:
  "fmmap_keys f (fmap_of_list m) = fmap_of_list (map (\<lambda>(a, b). (a, f a b)) m)"
  apply transfer
  subgoal for f m by (induction m) (auto simp: apsnd_def map_prod_def fun_eq_iff)
  done

lemma fmimage_of_list[code]:
  "fmimage (fmap_of_list m) A = fset_of_list (map snd (filter (\<lambda>(k, _). k |\<in>| A) (AList.clearjunk m)))"
  apply (subst fmimage_alt_def)
  apply (subst fmfilter_alt_defs)
  apply (subst fmfilter_of_list)
  apply (subst fmran_of_list)
  apply transfer'
  by (metis AList.restrict_eq clearjunk_restrict list.set_map)

lemma fmcomp_list[code]:
  "fmap_of_list m \<circ>\<^sub>f fmap_of_list n = fmap_of_list (AList.compose n m)"
  by (rule fmap_ext) (simp add: fmlookup_of_list compose_conv map_comp_def split: option.splits)

end


subsection \<open>Instances\<close>

lemma exists_map_of:
  assumes "finite (dom m)" shows "\<exists>xs. map_of xs = m"
  using assms
proof (induction "dom m" arbitrary: m)
  case empty
  hence "m = Map.empty"
    by auto
  moreover have "map_of [] = Map.empty"
    by simp
  ultimately show ?case
    by blast
next
  case (insert x F)
  hence "F = dom (map_drop x m)"
    unfolding map_drop_def map_filter_def dom_def by auto
  with insert have "\<exists>xs'. map_of xs' = map_drop x m"
    by auto
  then obtain xs' where "map_of xs' = map_drop x m"
    ..
  moreover obtain y where "m x = Some y"
    using insert unfolding dom_def by blast
  ultimately have "map_of ((x, y) # xs') = m"
    using \<open>insert x F = dom m\<close>
    unfolding map_drop_def map_filter_def
    by auto
  thus ?case
    ..
qed

lemma exists_fmap_of_list: "\<exists>xs. fmap_of_list xs = m"
by transfer (rule exists_map_of)

lemma fmap_of_list_surj[simp, intro]: "surj fmap_of_list"
proof -
  have "x \<in> range fmap_of_list" for x :: "('a, 'b) fmap"
    unfolding image_iff
    using exists_fmap_of_list by (metis UNIV_I)
  thus ?thesis by auto
qed

instance fmap :: (countable, countable) countable
proof
  obtain to_nat :: "('a \<times> 'b) list \<Rightarrow> nat" where "inj to_nat"
    by (metis ex_inj)
  moreover have "inj (inv fmap_of_list)"
    using fmap_of_list_surj by (rule surj_imp_inj_inv)
  ultimately have "inj (to_nat \<circ> inv fmap_of_list)"
    by (rule inj_compose)
  thus "\<exists>to_nat::('a, 'b) fmap \<Rightarrow> nat. inj to_nat"
    by auto
qed

instance fmap :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a, 'b) fmap set)"
    by (rule finite_imageD) auto
qed

lifting_update fmap.lifting
lifting_forget fmap.lifting


subsection \<open>Tests\<close>

\<comment> \<open>Code generation\<close>

export_code
  Ball fset fmrel fmran fmran' fmdom fmdom' fmpred pred_fmap fmsubset fmupd fmrel_on_fset
  fmdrop fmdrop_set fmdrop_fset fmrestrict_set fmrestrict_fset fmimage fmlookup fmempty
  fmfilter fmadd fmmap fmmap_keys fmcomp
  checking SML Scala Haskell? OCaml?

\<comment> \<open>\<open>lifting\<close> through \<^type>\<open>fmap\<close>\<close>

experiment begin

context includes fset.lifting begin

lift_definition test1 :: "('a, 'b fset) fmap" is "fmempty :: ('a, 'b set) fmap"
  by auto

lift_definition test2 :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b fset) fmap" is "\<lambda>a b. fmupd a {b} fmempty"
  by auto

end

end

end