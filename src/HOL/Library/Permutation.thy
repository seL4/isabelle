(*  Title:      HOL/Library/Permutation.thy
    Author:     Lawrence C Paulson and Thomas M Rasmussen and Norbert Voelker
*)

header {* Permutations *}

theory Permutation
imports Main Multiset
begin

inductive
  perm :: "'a list => 'a list => bool"  ("_ <~~> _"  [50, 50] 50)
  where
    Nil  [intro!]: "[] <~~> []"
  | swap [intro!]: "y # x # l <~~> x # y # l"
  | Cons [intro!]: "xs <~~> ys ==> z # xs <~~> z # ys"
  | trans [intro]: "xs <~~> ys ==> ys <~~> zs ==> xs <~~> zs"

lemma perm_refl [iff]: "l <~~> l"
  by (induct l) auto


subsection {* Some examples of rule induction on permutations *}

lemma xperm_empty_imp: "[] <~~> ys ==> ys = []"
  by (induct xs == "[]::'a list" ys pred: perm) simp_all


text {*
  \medskip This more general theorem is easier to understand!
  *}

lemma perm_length: "xs <~~> ys ==> length xs = length ys"
  by (induct pred: perm) simp_all

lemma perm_empty_imp: "[] <~~> xs ==> xs = []"
  by (drule perm_length) auto

lemma perm_sym: "xs <~~> ys ==> ys <~~> xs"
  by (induct pred: perm) auto


subsection {* Ways of making new permutations *}

text {*
  We can insert the head anywhere in the list.
*}

lemma perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by (induct xs) auto

lemma perm_append_swap: "xs @ ys <~~> ys @ xs"
  apply (induct xs)
    apply simp_all
  apply (blast intro: perm_append_Cons)
  done

lemma perm_append_single: "a # xs <~~> xs @ [a]"
  by (rule perm.trans [OF _ perm_append_swap]) simp

lemma perm_rev: "rev xs <~~> xs"
  apply (induct xs)
   apply simp_all
  apply (blast intro!: perm_append_single intro: perm_sym)
  done

lemma perm_append1: "xs <~~> ys ==> l @ xs <~~> l @ ys"
  by (induct l) auto

lemma perm_append2: "xs <~~> ys ==> xs @ l <~~> ys @ l"
  by (blast intro!: perm_append_swap perm_append1)


subsection {* Further results *}

lemma perm_empty [iff]: "([] <~~> xs) = (xs = [])"
  by (blast intro: perm_empty_imp)

lemma perm_empty2 [iff]: "(xs <~~> []) = (xs = [])"
  apply auto
  apply (erule perm_sym [THEN perm_empty_imp])
  done

lemma perm_sing_imp: "ys <~~> xs ==> xs = [y] ==> ys = [y]"
  by (induct pred: perm) auto

lemma perm_sing_eq [iff]: "(ys <~~> [y]) = (ys = [y])"
  by (blast intro: perm_sing_imp)

lemma perm_sing_eq2 [iff]: "([y] <~~> ys) = (ys = [y])"
  by (blast dest: perm_sym)


subsection {* Removing elements *}

consts
  remove :: "'a => 'a list => 'a list"
primrec
  "remove x [] = []"
  "remove x (y # ys) = (if x = y then ys else y # remove x ys)"

lemma perm_remove: "x \<in> set ys ==> ys <~~> x # remove x ys"
  by (induct ys) auto

lemma remove_commute: "remove x (remove y l) = remove y (remove x l)"
  by (induct l) auto

lemma multiset_of_remove [simp]:
    "multiset_of (remove a x) = multiset_of x - {#a#}"
  apply (induct x)
   apply (auto simp: multiset_eq_conv_count_eq)
  done


text {* \medskip Congruence rule *}

lemma perm_remove_perm: "xs <~~> ys ==> remove z xs <~~> remove z ys"
  by (induct pred: perm) auto

lemma remove_hd [simp]: "remove z (z # xs) = xs"
  by auto

lemma cons_perm_imp_perm: "z # xs <~~> z # ys ==> xs <~~> ys"
  by (drule_tac z = z in perm_remove_perm) auto

lemma cons_perm_eq [iff]: "(z#xs <~~> z#ys) = (xs <~~> ys)"
  by (blast intro: cons_perm_imp_perm)

lemma append_perm_imp_perm: "zs @ xs <~~> zs @ ys ==> xs <~~> ys"
  apply (induct zs arbitrary: xs ys rule: rev_induct)
   apply (simp_all (no_asm_use))
  apply blast
  done

lemma perm_append1_eq [iff]: "(zs @ xs <~~> zs @ ys) = (xs <~~> ys)"
  by (blast intro: append_perm_imp_perm perm_append1)

lemma perm_append2_eq [iff]: "(xs @ zs <~~> ys @ zs) = (xs <~~> ys)"
  apply (safe intro!: perm_append2)
  apply (rule append_perm_imp_perm)
  apply (rule perm_append_swap [THEN perm.trans])
    -- {* the previous step helps this @{text blast} call succeed quickly *}
  apply (blast intro: perm_append_swap)
  done

lemma multiset_of_eq_perm: "(multiset_of xs = multiset_of ys) = (xs <~~> ys) "
  apply (rule iffI)
  apply (erule_tac [2] perm.induct, simp_all add: union_ac)
  apply (erule rev_mp, rule_tac x=ys in spec)
  apply (induct_tac xs, auto)
  apply (erule_tac x = "remove a x" in allE, drule sym, simp)
  apply (subgoal_tac "a \<in> set x")
  apply (drule_tac z=a in perm.Cons)
  apply (erule perm.trans, rule perm_sym, erule perm_remove)
  apply (drule_tac f=set_of in arg_cong, simp)
  done

lemma multiset_of_le_perm_append:
    "(multiset_of xs \<le># multiset_of ys) = (\<exists>zs. xs @ zs <~~> ys)";
  apply (auto simp: multiset_of_eq_perm[THEN sym] mset_le_exists_conv)
  apply (insert surj_multiset_of, drule surjD)
  apply (blast intro: sym)+
  done

lemma perm_set_eq: "xs <~~> ys ==> set xs = set ys"
  by (metis multiset_of_eq_perm multiset_of_eq_setD)

lemma perm_distinct_iff: "xs <~~> ys ==> distinct xs = distinct ys"
  apply (induct pred: perm)
     apply simp_all
   apply fastsimp
  apply (metis perm_set_eq)
  done

lemma eq_set_perm_remdups: "set xs = set ys ==> remdups xs <~~> remdups ys"
  apply (induct xs arbitrary: ys rule: length_induct)
  apply (case_tac "remdups xs", simp, simp)
  apply (subgoal_tac "a : set (remdups ys)")
   prefer 2 apply (metis set.simps(2) insert_iff set_remdups)
  apply (drule split_list) apply(elim exE conjE)
  apply (drule_tac x=list in spec) apply(erule impE) prefer 2
   apply (drule_tac x="ysa@zs" in spec) apply(erule impE) prefer 2
    apply simp
    apply (subgoal_tac "a#list <~~> a#ysa@zs")
     apply (metis Cons_eq_appendI perm_append_Cons trans)
    apply (metis Cons Cons_eq_appendI distinct.simps(2)
      distinct_remdups distinct_remdups_id perm_append_swap perm_distinct_iff)
   apply (subgoal_tac "set (a#list) = set (ysa@a#zs) & distinct (a#list) & distinct (ysa@a#zs)")
    apply (fastsimp simp add: insert_ident)
   apply (metis distinct_remdups set_remdups)
   apply (subgoal_tac "length (remdups xs) < Suc (length xs)")
   apply simp
   apply (subgoal_tac "length (remdups xs) \<le> length xs")
   apply simp
   apply (rule length_remdups_leq)
  done

lemma perm_remdups_iff_eq_set: "remdups x <~~> remdups y = (set x = set y)"
  by (metis List.set_remdups perm_set_eq eq_set_perm_remdups)

end
