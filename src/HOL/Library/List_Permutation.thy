(*  Title:      HOL/Library/List_Permutation.thy
    Author:     Lawrence C Paulson and Thomas M Rasmussen and Norbert Voelker
*)

section \<open>Permuted Lists\<close>

theory List_Permutation
imports Multiset
begin

subsection \<open>An inductive definition\<dots>\<close>

inductive perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixr \<open><~~>\<close> 50)
where
  Nil [intro!]: "[] <~~> []"
| swap [intro!]: "y # x # l <~~> x # y # l"
| Cons [intro!]: "xs <~~> ys \<Longrightarrow> z # xs <~~> z # ys"
| trans [intro]: "xs <~~> ys \<Longrightarrow> ys <~~> zs \<Longrightarrow> xs <~~> zs"

proposition perm_refl [iff]: "l <~~> l"
  by (induct l) auto

text \<open>\<dots>that is equivalent to an already existing notion:\<close>

lemma perm_iff_eq_mset:
  \<open>xs <~~> ys \<longleftrightarrow> mset xs = mset ys\<close>
proof
  assume \<open>mset xs = mset ys\<close>
  then show \<open>xs <~~> ys\<close>
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    from Cons.prems [symmetric] have \<open>mset xs = mset (remove1 x ys)\<close>
      by simp
    then have \<open>xs <~~> remove1 x ys\<close>
      by (rule Cons.IH)
    then have \<open>x # xs <~~> x # remove1 x ys\<close>
      by (rule perm.Cons)
    moreover from Cons.prems have \<open>x \<in> set ys\<close>
      by (auto dest: union_single_eq_member)
    then have \<open>x # remove1 x ys <~~> ys\<close>
      by (induction ys) auto
    ultimately show \<open>x # xs <~~> ys\<close>
      by (rule perm.trans)
  qed
next
  assume \<open>xs <~~> ys\<close>
  then show \<open>mset xs = mset ys\<close>
    by induction simp_all
qed

lemma list_permuted_induct [consumes 1, case_names Nil swap Cons trans]:
  \<open>P xs ys\<close>
  if \<open>mset xs = mset ys\<close>
  \<open>P [] []\<close>
  \<open>\<And>y x zs. P (y # x # zs) (x # y # zs)\<close>
  \<open>\<And>xs ys z. mset xs = mset ys \<Longrightarrow> P xs ys \<Longrightarrow> P (z # xs) (z # ys)\<close>
  \<open>\<And>xs ys zs. mset xs = mset ys \<Longrightarrow> mset ys = mset zs \<Longrightarrow> P xs ys \<Longrightarrow> P ys zs \<Longrightarrow> P xs zs\<close>
proof -
  from \<open>mset xs = mset ys\<close> have \<open>xs <~~> ys\<close>
    by (simp add: perm_iff_eq_mset)
  then show ?thesis
    using that(2-3) apply (rule perm.induct)
     apply (simp_all add: perm_iff_eq_mset)
     apply (fact that(4))
    subgoal for xs ys zs
      apply (rule that(5) [of xs ys zs])
         apply simp_all
      done
    done
qed


subsection \<open>\<dots>that is equivalent to an already existing notion:\<close>

theorem mset_eq_perm: \<open>mset xs = mset ys \<longleftrightarrow> xs <~~> ys\<close>
  by (simp add: perm_iff_eq_mset)


subsection \<open>Nontrivial conclusions\<close>

proposition perm_swap:
  \<open>xs[i := xs ! j, j := xs ! i] <~~> xs\<close>
  if \<open>i < length xs\<close> \<open>j < length xs\<close>
  using that by (cases \<open>i = j\<close>) (simp_all add: perm_iff_eq_mset mset_update)

proposition mset_le_perm_append: "mset xs \<subseteq># mset ys \<longleftrightarrow> (\<exists>zs. xs @ zs <~~> ys)"
  by (auto simp add: perm_iff_eq_mset mset_subset_eq_exists_conv ex_mset dest: sym)

proposition perm_set_eq: "xs <~~> ys \<Longrightarrow> set xs = set ys"
  by (rule mset_eq_setD) (simp add: perm_iff_eq_mset)

proposition perm_distinct_iff: "xs <~~> ys \<Longrightarrow> distinct xs = distinct ys"
  by (auto simp add: perm_iff_eq_mset distinct_count_atmost_1 dest: mset_eq_setD)

theorem eq_set_perm_remdups: "set xs = set ys \<Longrightarrow> remdups xs <~~> remdups ys"
  by (simp add: perm_iff_eq_mset set_eq_iff_mset_remdups_eq)

proposition perm_remdups_iff_eq_set: "remdups x <~~> remdups y \<longleftrightarrow> set x = set y"
  by (simp add: perm_iff_eq_mset set_eq_iff_mset_remdups_eq)

theorem permutation_Ex_bij:
  assumes "xs <~~> ys"
  shows "\<exists>f. bij_betw f {..<length xs} {..<length ys} \<and> (\<forall>i<length xs. xs ! i = ys ! (f i))"
  using assms
proof induct
  case Nil
  then show ?case
    unfolding bij_betw_def by simp
next
  case (swap y x l)
  show ?case
  proof (intro exI[of _ "Fun.swap 0 1 id"] conjI allI impI)
    show "bij_betw (Fun.swap 0 1 id) {..<length (y # x # l)} {..<length (x # y # l)}"
      by (auto simp: bij_betw_def)
    fix i
    assume "i < length (y # x # l)"
    show "(y # x # l) ! i = (x # y # l) ! (Fun.swap 0 1 id) i"
      by (cases i) (auto simp: Fun.swap_def gr0_conv_Suc)
  qed
next
  case (Cons xs ys z)
  then obtain f where bij: "bij_betw f {..<length xs} {..<length ys}"
    and perm: "\<forall>i<length xs. xs ! i = ys ! (f i)"
    by blast
  let ?f = "\<lambda>i. case i of Suc n \<Rightarrow> Suc (f n) | 0 \<Rightarrow> 0"
  show ?case
  proof (intro exI[of _ ?f] allI conjI impI)
    have *: "{..<length (z#xs)} = {0} \<union> Suc ` {..<length xs}"
            "{..<length (z#ys)} = {0} \<union> Suc ` {..<length ys}"
      by (simp_all add: lessThan_Suc_eq_insert_0)
    show "bij_betw ?f {..<length (z#xs)} {..<length (z#ys)}"
      unfolding *
    proof (rule bij_betw_combine)
      show "bij_betw ?f (Suc ` {..<length xs}) (Suc ` {..<length ys})"
        using bij unfolding bij_betw_def
        by (auto intro!: inj_onI imageI dest: inj_onD simp: image_comp comp_def)
    qed (auto simp: bij_betw_def)
    fix i
    assume "i < length (z # xs)"
    then show "(z # xs) ! i = (z # ys) ! (?f i)"
      using perm by (cases i) auto
  qed
next
  case (trans xs ys zs)
  then obtain f g
    where bij: "bij_betw f {..<length xs} {..<length ys}" "bij_betw g {..<length ys} {..<length zs}"
    and perm: "\<forall>i<length xs. xs ! i = ys ! (f i)" "\<forall>i<length ys. ys ! i = zs ! (g i)"
    by blast
  show ?case
  proof (intro exI[of _ "g \<circ> f"] conjI allI impI)
    show "bij_betw (g \<circ> f) {..<length xs} {..<length zs}"
      using bij by (rule bij_betw_trans)
    fix i
    assume "i < length xs"
    with bij have "f i < length ys"
      unfolding bij_betw_def by force
    with \<open>i < length xs\<close> show "xs ! i = zs ! (g \<circ> f) i"
      using trans(1,3) perm by auto
  qed
qed

proposition perm_finite: "finite {B. B <~~> A}"
proof (rule finite_subset [where B="{xs. set xs \<subseteq> set A \<and> length xs \<le> length A}"])
  show "finite {xs. set xs \<subseteq> set A \<and> length xs \<le> length A}"
    using finite_lists_length_le by blast
next
  show "{B. B <~~> A} \<subseteq> {xs. set xs \<subseteq> set A \<and> length xs \<le> length A}"
    by (auto simp add: perm_iff_eq_mset dest: mset_eq_setD mset_eq_length)
qed


subsection \<open>Trivial conclusions:\<close>

proposition perm_empty_imp: "[] <~~> ys \<Longrightarrow> ys = []"
  by (simp add: perm_iff_eq_mset)


text \<open>\medskip This more general theorem is easier to understand!\<close>

proposition perm_length: "xs <~~> ys \<Longrightarrow> length xs = length ys"
  by (rule mset_eq_length) (simp add: perm_iff_eq_mset)

proposition perm_sym: "xs <~~> ys \<Longrightarrow> ys <~~> xs"
  by (simp add: perm_iff_eq_mset)


text \<open>We can insert the head anywhere in the list.\<close>

proposition perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append_swap: "xs @ ys <~~> ys @ xs"
  by (simp add: perm_iff_eq_mset)

proposition perm_append_single: "a # xs <~~> xs @ [a]"
  by (simp add: perm_iff_eq_mset)

proposition perm_rev: "rev xs <~~> xs"
  by (simp add: perm_iff_eq_mset)

proposition perm_append1: "xs <~~> ys \<Longrightarrow> l @ xs <~~> l @ ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append2: "xs <~~> ys \<Longrightarrow> xs @ l <~~> ys @ l"
  by (simp add: perm_iff_eq_mset)

proposition perm_empty [iff]: "[] <~~> xs \<longleftrightarrow> xs = []"
  by (simp add: perm_iff_eq_mset)

proposition perm_empty2 [iff]: "xs <~~> [] \<longleftrightarrow> xs = []"
  by (simp add: perm_iff_eq_mset)

proposition perm_sing_imp: "ys <~~> xs \<Longrightarrow> xs = [y] \<Longrightarrow> ys = [y]"
  by (simp add: perm_iff_eq_mset)

proposition perm_sing_eq [iff]: "ys <~~> [y] \<longleftrightarrow> ys = [y]"
  by (simp add: perm_iff_eq_mset)

proposition perm_sing_eq2 [iff]: "[y] <~~> ys \<longleftrightarrow> ys = [y]"
  by (simp add: perm_iff_eq_mset)

proposition perm_remove: "x \<in> set ys \<Longrightarrow> ys <~~> x # remove1 x ys"
  by (simp add: perm_iff_eq_mset)


text \<open>\medskip Congruence rule\<close>

proposition perm_remove_perm: "xs <~~> ys \<Longrightarrow> remove1 z xs <~~> remove1 z ys"
  by (simp add: perm_iff_eq_mset)

proposition remove_hd [simp]: "remove1 z (z # xs) = xs"
  by (simp add: perm_iff_eq_mset)

proposition cons_perm_imp_perm: "z # xs <~~> z # ys \<Longrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition cons_perm_eq [simp]: "z#xs <~~> z#ys \<longleftrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition append_perm_imp_perm: "zs @ xs <~~> zs @ ys \<Longrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append1_eq [iff]: "zs @ xs <~~> zs @ ys \<longleftrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append2_eq [iff]: "xs @ zs <~~> ys @ zs \<longleftrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

end
