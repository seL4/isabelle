(*  Title:      HOL/Library/Permutation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Thomas M Rasmussen
    Copyright   1995  University of Cambridge

TODO: it would be nice to prove (for "multiset", defined on
HOL/ex/Sorting.thy) xs <~~> ys = (\<forall>x. multiset xs x = multiset ys x)
*)

header {* Permutations *}

theory Permutation = Main:

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
  apply (induct l)
   apply auto
  done


subsection {* Some examples of rule induction on permutations *}

lemma xperm_empty_imp_aux: "xs <~~> ys ==> xs = [] --> ys = []"
    -- {* the form of the premise lets the induction bind @{term xs} and @{term ys} *}
  apply (erule perm.induct)
     apply (simp_all (no_asm_simp))
  done

lemma xperm_empty_imp: "[] <~~> ys ==> ys = []"
  apply (insert xperm_empty_imp_aux)
  apply blast
  done


text {*
  \medskip This more general theorem is easier to understand!
  *}

lemma perm_length: "xs <~~> ys ==> length xs = length ys"
  apply (erule perm.induct)
     apply simp_all
  done

lemma perm_empty_imp: "[] <~~> xs ==> xs = []"
  apply (drule perm_length)
  apply auto
  done

lemma perm_sym: "xs <~~> ys ==> ys <~~> xs"
  apply (erule perm.induct)
     apply auto
  done

lemma perm_mem [rule_format]: "xs <~~> ys ==> x mem xs --> x mem ys"
  apply (erule perm.induct)
     apply auto
  done


subsection {* Ways of making new permutations *}

text {*
  We can insert the head anywhere in the list.
*}

lemma perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  apply (induct xs)
   apply auto
  done

lemma perm_append_swap: "xs @ ys <~~> ys @ xs"
  apply (induct xs)
    apply simp_all
  apply (blast intro: perm_append_Cons)
  done

lemma perm_append_single: "a # xs <~~> xs @ [a]"
  apply (rule perm.trans)
   prefer 2
   apply (rule perm_append_swap)
  apply simp
  done

lemma perm_rev: "rev xs <~~> xs"
  apply (induct xs)
   apply simp_all
  apply (blast intro!: perm_append_single intro: perm_sym)
  done

lemma perm_append1: "xs <~~> ys ==> l @ xs <~~> l @ ys"
  apply (induct l)
   apply auto
  done

lemma perm_append2: "xs <~~> ys ==> xs @ l <~~> ys @ l"
  apply (blast intro!: perm_append_swap perm_append1)
  done


subsection {* Further results *}

lemma perm_empty [iff]: "([] <~~> xs) = (xs = [])"
  apply (blast intro: perm_empty_imp)
  done

lemma perm_empty2 [iff]: "(xs <~~> []) = (xs = [])"
  apply auto
  apply (erule perm_sym [THEN perm_empty_imp])
  done

lemma perm_sing_imp [rule_format]: "ys <~~> xs ==> xs = [y] --> ys = [y]"
  apply (erule perm.induct)
     apply auto
  done

lemma perm_sing_eq [iff]: "(ys <~~> [y]) = (ys = [y])"
  apply (blast intro: perm_sing_imp)
  done

lemma perm_sing_eq2 [iff]: "([y] <~~> ys) = (ys = [y])"
  apply (blast dest: perm_sym)
  done


subsection {* Removing elements *}

consts
  remove :: "'a => 'a list => 'a list"
primrec
  "remove x [] = []"
  "remove x (y # ys) = (if x = y then ys else y # remove x ys)"

lemma perm_remove: "x \<in> set ys ==> ys <~~> x # remove x ys"
  apply (induct ys)
   apply auto
  done

lemma remove_commute: "remove x (remove y l) = remove y (remove x l)"
  apply (induct l)
   apply auto
  done


text {* \medskip Congruence rule *}

lemma perm_remove_perm: "xs <~~> ys ==> remove z xs <~~> remove z ys"
  apply (erule perm.induct)
     apply auto
  done

lemma remove_hd [simp]: "remove z (z # xs) = xs"
  apply auto
  done

lemma cons_perm_imp_perm: "z # xs <~~> z # ys ==> xs <~~> ys"
  apply (drule_tac z = z in perm_remove_perm)
  apply auto
  done

lemma cons_perm_eq [iff]: "(z#xs <~~> z#ys) = (xs <~~> ys)"
  apply (blast intro: cons_perm_imp_perm)
  done

lemma append_perm_imp_perm: "!!xs ys. zs @ xs <~~> zs @ ys ==> xs <~~> ys"
  apply (induct zs rule: rev_induct)
   apply (simp_all (no_asm_use))
  apply blast
  done

lemma perm_append1_eq [iff]: "(zs @ xs <~~> zs @ ys) = (xs <~~> ys)"
  apply (blast intro: append_perm_imp_perm perm_append1)
  done

lemma perm_append2_eq [iff]: "(xs @ zs <~~> ys @ zs) = (xs <~~> ys)"
  apply (safe intro!: perm_append2)
  apply (rule append_perm_imp_perm)
  apply (rule perm_append_swap [THEN perm.trans])
    -- {* the previous step helps this @{text blast} call succeed quickly *}
  apply (blast intro: perm_append_swap)
  done

end
