(*  Title:      HOL/Library/Permutation.thy
    Author:     Lawrence C Paulson and Thomas M Rasmussen and Norbert Voelker
*)

section \<open>Permutations\<close>

theory Permutation
imports Multiset
begin

inductive perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (\<open>_ <~~> _\<close>  [50, 50] 50)  (* FIXME proper infix, without ambiguity!? *)
where
  Nil [intro!]: "[] <~~> []"
| swap [intro!]: "y # x # l <~~> x # y # l"
| Cons [intro!]: "xs <~~> ys \<Longrightarrow> z # xs <~~> z # ys"
| trans [intro]: "xs <~~> ys \<Longrightarrow> ys <~~> zs \<Longrightarrow> xs <~~> zs"

proposition perm_refl [iff]: "l <~~> l"
  by (induct l) auto


subsection \<open>Some examples of rule induction on permutations\<close>

proposition xperm_empty_imp: "[] <~~> ys \<Longrightarrow> ys = []"
  by (induct xs == "[] :: 'a list" ys pred: perm) simp_all


text \<open>\medskip This more general theorem is easier to understand!\<close>

proposition perm_length: "xs <~~> ys \<Longrightarrow> length xs = length ys"
  by (induct pred: perm) simp_all

proposition perm_empty_imp: "[] <~~> xs \<Longrightarrow> xs = []"
  by (drule perm_length) auto

proposition perm_sym: "xs <~~> ys \<Longrightarrow> ys <~~> xs"
  by (induct pred: perm) auto


subsection \<open>Ways of making new permutations\<close>

text \<open>We can insert the head anywhere in the list.\<close>

proposition perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by (induct xs) auto

proposition perm_append_swap: "xs @ ys <~~> ys @ xs"
  by (induct xs) (auto intro: perm_append_Cons)

proposition perm_append_single: "a # xs <~~> xs @ [a]"
  by (rule perm.trans [OF _ perm_append_swap]) simp

proposition perm_rev: "rev xs <~~> xs"
  by (induct xs) (auto intro!: perm_append_single intro: perm_sym)

proposition perm_append1: "xs <~~> ys \<Longrightarrow> l @ xs <~~> l @ ys"
  by (induct l) auto

proposition perm_append2: "xs <~~> ys \<Longrightarrow> xs @ l <~~> ys @ l"
  by (blast intro!: perm_append_swap perm_append1)


subsection \<open>Further results\<close>

proposition perm_empty [iff]: "[] <~~> xs \<longleftrightarrow> xs = []"
  by (blast intro: perm_empty_imp)

proposition perm_empty2 [iff]: "xs <~~> [] \<longleftrightarrow> xs = []"
  apply auto
  apply (erule perm_sym [THEN perm_empty_imp])
  done

proposition perm_sing_imp: "ys <~~> xs \<Longrightarrow> xs = [y] \<Longrightarrow> ys = [y]"
  by (induct pred: perm) auto

proposition perm_sing_eq [iff]: "ys <~~> [y] \<longleftrightarrow> ys = [y]"
  by (blast intro: perm_sing_imp)

proposition perm_sing_eq2 [iff]: "[y] <~~> ys \<longleftrightarrow> ys = [y]"
  by (blast dest: perm_sym)


subsection \<open>Removing elements\<close>

proposition perm_remove: "x \<in> set ys \<Longrightarrow> ys <~~> x # remove1 x ys"
  by (induct ys) auto


text \<open>\medskip Congruence rule\<close>

proposition perm_remove_perm: "xs <~~> ys \<Longrightarrow> remove1 z xs <~~> remove1 z ys"
  by (induct pred: perm) auto

proposition remove_hd [simp]: "remove1 z (z # xs) = xs"
  by auto

proposition cons_perm_imp_perm: "z # xs <~~> z # ys \<Longrightarrow> xs <~~> ys"
  by (drule perm_remove_perm [where z = z]) auto

proposition cons_perm_eq [iff]: "z#xs <~~> z#ys \<longleftrightarrow> xs <~~> ys"
  by (blast intro: cons_perm_imp_perm)

proposition append_perm_imp_perm: "zs @ xs <~~> zs @ ys \<Longrightarrow> xs <~~> ys"
  by (induct zs arbitrary: xs ys rule: rev_induct) auto

proposition perm_append1_eq [iff]: "zs @ xs <~~> zs @ ys \<longleftrightarrow> xs <~~> ys"
  by (blast intro: append_perm_imp_perm perm_append1)

proposition perm_append2_eq [iff]: "xs @ zs <~~> ys @ zs \<longleftrightarrow> xs <~~> ys"
  apply (safe intro!: perm_append2)
  apply (rule append_perm_imp_perm)
  apply (rule perm_append_swap [THEN perm.trans])
    \<comment> \<open>the previous step helps this \<open>blast\<close> call succeed quickly\<close>
  apply (blast intro: perm_append_swap)
  done

theorem mset_eq_perm: "mset xs = mset ys \<longleftrightarrow> xs <~~> ys"
  apply (rule iffI)
  apply (erule_tac [2] perm.induct)
  apply (simp_all add: union_ac)
  apply (erule rev_mp)
  apply (rule_tac x=ys in spec)
  apply (induct_tac xs)
  apply auto
  apply (erule_tac x = "remove1 a x" in allE)
  apply (drule sym)
  apply simp
  apply (subgoal_tac "a \<in> set x")
  apply (drule_tac z = a in perm.Cons)
  apply (erule perm.trans)
  apply (rule perm_sym)
  apply (erule perm_remove)
  apply (drule_tac f=set_mset in arg_cong)
  apply simp
  done

proposition mset_le_perm_append: "mset xs \<subseteq># mset ys \<longleftrightarrow> (\<exists>zs. xs @ zs <~~> ys)"
  apply (auto simp: mset_eq_perm[THEN sym] mset_subset_eq_exists_conv)
  apply (insert surj_mset)
  apply (drule surjD)
  apply (blast intro: sym)+
  done

proposition perm_set_eq: "xs <~~> ys \<Longrightarrow> set xs = set ys"
  by (metis mset_eq_perm mset_eq_setD)

proposition perm_distinct_iff: "xs <~~> ys \<Longrightarrow> distinct xs = distinct ys"
  apply (induct pred: perm)
     apply simp_all
   apply fastforce
  apply (metis perm_set_eq)
  done

theorem eq_set_perm_remdups: "set xs = set ys \<Longrightarrow> remdups xs <~~> remdups ys"
  apply (induct xs arbitrary: ys rule: length_induct)
  apply (case_tac "remdups xs")
   apply simp_all
  apply (subgoal_tac "a \<in> set (remdups ys)")
   prefer 2 apply (metis list.set(2) insert_iff set_remdups)
  apply (drule split_list) apply (elim exE conjE)
  apply (drule_tac x = list in spec) apply (erule impE) prefer 2
   apply (drule_tac x = "ysa @ zs" in spec) apply (erule impE) prefer 2
    apply simp
    apply (subgoal_tac "a # list <~~> a # ysa @ zs")
     apply (metis Cons_eq_appendI perm_append_Cons trans)
    apply (metis Cons Cons_eq_appendI distinct.simps(2)
      distinct_remdups distinct_remdups_id perm_append_swap perm_distinct_iff)
   apply (subgoal_tac "set (a # list) =
      set (ysa @ a # zs) \<and> distinct (a # list) \<and> distinct (ysa @ a # zs)")
    apply (fastforce simp add: insert_ident)
   apply (metis distinct_remdups set_remdups)
   apply (subgoal_tac "length (remdups xs) < Suc (length xs)")
   apply simp
   apply (subgoal_tac "length (remdups xs) \<le> length xs")
   apply simp
   apply (rule length_remdups_leq)
  done

proposition perm_remdups_iff_eq_set: "remdups x <~~> remdups y \<longleftrightarrow> set x = set y"
  by (metis List.set_remdups perm_set_eq eq_set_perm_remdups)

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
      using trans(1,3)[THEN perm_length] perm by auto
  qed
qed

proposition perm_finite: "finite {B. B <~~> A}"
proof (rule finite_subset[where B="{xs. set xs \<subseteq> set A \<and> length xs \<le> length A}"])
 show "finite {xs. set xs \<subseteq> set A \<and> length xs \<le> length A}"
   apply (cases A, simp)
   apply (rule card_ge_0_finite)
   apply (auto simp: card_lists_length_le)
   done
next
 show "{B. B <~~> A} \<subseteq> {xs. set xs \<subseteq> set A \<and> length xs \<le> length A}"
   by (clarsimp simp add: perm_length perm_set_eq)
qed

proposition perm_swap:
    assumes "i < length xs" "j < length xs"
    shows "xs[i := xs ! j, j := xs ! i] <~~> xs"
  using assms by (simp add: mset_eq_perm[symmetric] mset_swap)

end
