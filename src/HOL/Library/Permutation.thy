(*  Title:      HOL/Library/Permutation.thy
    Author:     Lawrence C Paulson and Thomas M Rasmussen and Norbert Voelker
*)

header {* Permutations *}

theory Permutation = Multiset:

consts
  perm :: "('a list * 'a list) set"

syntax
  "_perm" :: "'a list => 'a list => bool"    ("_ <~~> _"  [50, 50] 50)
translations
  "x <~~> y" == "(x, y) \<in> perm"

inductive perm
  intros
    Nil  [intro!]: "[] <~~> []"
    swap [intro!]: "y # x # l <~~> x # y # l"
    Cons [intro!]: "xs <~~> ys ==> z # xs <~~> z # ys"
    trans [intro]: "xs <~~> ys ==> ys <~~> zs ==> xs <~~> zs"

lemma perm_refl [iff]: "l <~~> l"
by (induct l, auto)


subsection {* Some examples of rule induction on permutations *}

lemma xperm_empty_imp_aux: "xs <~~> ys ==> xs = [] --> ys = []"
    -- {* the form of the premise lets the induction bind @{term xs} and @{term ys} *}
  apply (erule perm.induct)
     apply (simp_all (no_asm_simp))
  done

lemma xperm_empty_imp: "[] <~~> ys ==> ys = []"
by (insert xperm_empty_imp_aux, blast)


text {*
  \medskip This more general theorem is easier to understand!
  *}

lemma perm_length: "xs <~~> ys ==> length xs = length ys"
by (erule perm.induct, simp_all)

lemma perm_empty_imp: "[] <~~> xs ==> xs = []"
by (drule perm_length, auto)

lemma perm_sym: "xs <~~> ys ==> ys <~~> xs"
by (erule perm.induct, auto)

lemma perm_mem [rule_format]: "xs <~~> ys ==> x mem xs --> x mem ys"
by (erule perm.induct, auto)


subsection {* Ways of making new permutations *}

text {*
  We can insert the head anywhere in the list.
*}

lemma perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
by (induct xs, auto)

lemma perm_append_swap: "xs @ ys <~~> ys @ xs"
  apply (induct xs, simp_all)
  apply (blast intro: perm_append_Cons)
  done

lemma perm_append_single: "a # xs <~~> xs @ [a]"
  apply (rule perm.trans)
   prefer 2
   apply (rule perm_append_swap, simp)
  done

lemma perm_rev: "rev xs <~~> xs"
  apply (induct xs, simp_all)
  apply (blast intro!: perm_append_single intro: perm_sym)
  done

lemma perm_append1: "xs <~~> ys ==> l @ xs <~~> l @ ys"
by (induct l, auto)

lemma perm_append2: "xs <~~> ys ==> xs @ l <~~> ys @ l"
by (blast intro!: perm_append_swap perm_append1)


subsection {* Further results *}

lemma perm_empty [iff]: "([] <~~> xs) = (xs = [])"
by (blast intro: perm_empty_imp)

lemma perm_empty2 [iff]: "(xs <~~> []) = (xs = [])"
  apply auto
  apply (erule perm_sym [THEN perm_empty_imp])
  done

lemma perm_sing_imp [rule_format]: "ys <~~> xs ==> xs = [y] --> ys = [y]"
by (erule perm.induct, auto)

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
by (induct ys, auto)

lemma remove_commute: "remove x (remove y l) = remove y (remove x l)"
by (induct l, auto)


text {* \medskip Congruence rule *}

lemma perm_remove_perm: "xs <~~> ys ==> remove z xs <~~> remove z ys"
by (erule perm.induct, auto)

lemma remove_hd [simp]: "remove z (z # xs) = xs"
  apply auto
  done

lemma cons_perm_imp_perm: "z # xs <~~> z # ys ==> xs <~~> ys"
by (drule_tac z = z in perm_remove_perm, auto)

lemma cons_perm_eq [iff]: "(z#xs <~~> z#ys) = (xs <~~> ys)"
by (blast intro: cons_perm_imp_perm)

lemma append_perm_imp_perm: "!!xs ys. zs @ xs <~~> zs @ ys ==> xs <~~> ys"
  apply (induct zs rule: rev_induct)
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

(****************** Norbert Voelker 17 June 2004 **************) 

consts 
  multiset_of :: "'a list \<Rightarrow> 'a multiset"
primrec
  "multiset_of [] = {#}"
  "multiset_of (a # x) = multiset_of x + {# a #}"

lemma multiset_of_zero_iff[simp]: "(multiset_of x = {#}) = (x = [])"
  by (induct_tac x, auto) 

lemma multiset_of_zero_iff_right[simp]: "({#} = multiset_of x) = (x = [])"
  by (induct_tac x, auto)

lemma set_of_multiset_of[simp]: "set_of(multiset_of x) = set x"
 by (induct_tac x, auto) 

lemma multiset_of_remove[simp]: 
  "multiset_of (remove a x) = multiset_of x - {#a#}"
  by (induct_tac x, auto simp: multiset_eq_conv_count_eq) 

lemma multiset_of_eq_perm:  "(multiset_of xs = multiset_of ys) = (xs <~~> ys) "
  apply (rule iffI) 
  apply (erule_tac [2] perm.induct, simp_all add: union_ac) 
  apply (erule rev_mp, rule_tac x=ys in spec, induct_tac xs, auto) 
  apply (erule_tac x = "remove a x" in allE, drule sym, simp) 
  apply (subgoal_tac "a \<in> set x") 
  apply (drule_tac z=a in perm.Cons) 
  apply (erule perm.trans, rule perm_sym, erule perm_remove) 
  apply (drule_tac f=set_of in arg_cong, simp)
  done

lemma set_count_multiset_of: "set x = {a. 0 < count (multiset_of x) a}"
  by (induct_tac x, auto)  

lemma distinct_count_multiset_of: 
   "distinct x \<Longrightarrow> count (multiset_of x) a = (if a \<in> set x then 1 else 0)"
  by (erule rev_mp, induct_tac x, auto) 

lemma distinct_set_eq_iff_multiset_of_eq: 
  "\<lbrakk>distinct x; distinct y\<rbrakk> \<Longrightarrow> (set x = set y) = (multiset_of x = multiset_of y)"
  by (auto simp: multiset_eq_conv_count_eq distinct_count_multiset_of) 

end
