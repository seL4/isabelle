(*  Title:      HOL/LList.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

header {*The "filter" functional for coinductive lists
  --defined by a combination of induction and coinduction*}

theory LFilter = LList:

consts
  findRel	:: "('a => bool) => ('a llist * 'a llist)set"

inductive "findRel p"
  intros
    found:  "p x ==> (LCons x l, LCons x l) \<in> findRel p"
    seek:   "[| ~p x;  (l,l') \<in> findRel p |] ==> (LCons x l, l') \<in> findRel p"

declare findRel.intros [intro]

constdefs
  find    :: "['a => bool, 'a llist] => 'a llist"
    "find p l == @l'. (l,l'): findRel p | (l' = LNil & l ~: Domain(findRel p))"

  lfilter :: "['a => bool, 'a llist] => 'a llist"
    "lfilter p l == llist_corec l (%l. case find p l of
                                            LNil => None
                                          | LCons y z => Some(y,z))"


subsection {* @{text findRel}: basic laws *}

inductive_cases
  findRel_LConsE [elim!]: "(LCons x l, l'') \<in> findRel p"


lemma findRel_functional [rule_format]:
     "(l,l'): findRel p ==> (l,l''): findRel p --> l'' = l'"
by (erule findRel.induct, auto)

lemma findRel_imp_LCons [rule_format]:
     "(l,l'): findRel p ==> \<exists>x l''. l' = LCons x l'' & p x"
by (erule findRel.induct, auto)

lemma findRel_LNil [elim!]: "(LNil,l): findRel p ==> R"
by (blast elim: findRel.cases)


subsection {* Properties of @{text "Domain (findRel p)"} *}

lemma LCons_Domain_findRel [simp]:
     "LCons x l \<in> Domain(findRel p) = (p x | l \<in> Domain(findRel p))"
by auto

lemma Domain_findRel_iff:
     "(l \<in> Domain (findRel p)) = (\<exists>x l'. (l, LCons x l') \<in> findRel p &  p x)" 
by (blast dest: findRel_imp_LCons) 

lemma Domain_findRel_mono:
    "[| !!x. p x ==> q x |] ==> Domain (findRel p) <= Domain (findRel q)"
apply clarify
apply (erule findRel.induct, blast+)
done


subsection {* @{text find}: basic equations *}

lemma find_LNil [simp]: "find p LNil = LNil"
by (unfold find_def, blast)

lemma findRel_imp_find [simp]: "(l,l') \<in> findRel p ==> find p l = l'"
apply (unfold find_def)
apply (blast dest: findRel_functional)
done

lemma find_LCons_found: "p x ==> find p (LCons x l) = LCons x l"
by (blast intro: findRel_imp_find)

lemma diverge_find_LNil [simp]: "l ~: Domain(findRel p) ==> find p l = LNil"
by (unfold find_def, blast)

lemma find_LCons_seek: "~ (p x) ==> find p (LCons x l) = find p l"
apply (case_tac "LCons x l \<in> Domain (findRel p) ")
 apply auto 
apply (blast intro: findRel_imp_find)
done

lemma find_LCons [simp]:
     "find p (LCons x l) = (if p x then LCons x l else find p l)"
by (simp add: find_LCons_seek find_LCons_found)



subsection {* @{text lfilter}: basic equations *}

lemma lfilter_LNil [simp]: "lfilter p LNil = LNil"
by (rule lfilter_def [THEN def_llist_corec, THEN trans], simp)

lemma diverge_lfilter_LNil [simp]:
     "l ~: Domain(findRel p) ==> lfilter p l = LNil"
by (rule lfilter_def [THEN def_llist_corec, THEN trans], simp)

lemma lfilter_LCons_found:
     "p x ==> lfilter p (LCons x l) = LCons x (lfilter p l)"
by (rule lfilter_def [THEN def_llist_corec, THEN trans], simp)

lemma findRel_imp_lfilter [simp]:
     "(l, LCons x l') \<in> findRel p ==> lfilter p l = LCons x (lfilter p l')"
by (rule lfilter_def [THEN def_llist_corec, THEN trans], simp)

lemma lfilter_LCons_seek: "~ (p x) ==> lfilter p (LCons x l) = lfilter p l"
apply (rule lfilter_def [THEN def_llist_corec, THEN trans], simp)
apply (case_tac "LCons x l \<in> Domain (findRel p) ")
 apply (simp add: Domain_findRel_iff, auto) 
done

lemma lfilter_LCons [simp]:
     "lfilter p (LCons x l) =  
          (if p x then LCons x (lfilter p l) else lfilter p l)"
by (simp add: lfilter_LCons_found lfilter_LCons_seek)

declare llistD_Fun_LNil_I [intro!] llistD_Fun_LCons_I [intro!]


lemma lfilter_eq_LNil: "lfilter p l = LNil ==> l ~: Domain(findRel p)" 
apply (auto iff: Domain_findRel_iff)
apply (rotate_tac 1, simp) 
done

lemma lfilter_eq_LCons [rule_format]:
     "lfilter p l = LCons x l' -->      
               (\<exists>l''. l' = lfilter p l'' & (l, LCons x l'') \<in> findRel p)"
apply (subst lfilter_def [THEN def_llist_corec])
apply (case_tac "l \<in> Domain (findRel p) ")
 apply (auto iff: Domain_findRel_iff)
done


lemma lfilter_cases: "lfilter p l = LNil  |   
          (\<exists>y l'. lfilter p l = LCons y (lfilter p l') & p y)"
apply (case_tac "l \<in> Domain (findRel p) ")
apply (auto iff: Domain_findRel_iff)
done


subsection {* @{text lfilter}: simple facts by coinduction *}

lemma lfilter_K_True: "lfilter (%x. True) l = l"
by (rule_tac l = "l" in llist_fun_equalityI, simp_all)

lemma lfilter_idem: "lfilter p (lfilter p l) = lfilter p l"
apply (rule_tac l = "l" in llist_fun_equalityI, simp_all)
apply safe
txt{*Cases: @{text "p x"} is true or false*}
apply (rule lfilter_cases [THEN disjE])
 apply (erule ssubst, auto)
done


subsection {* Numerous lemmas required to prove @{text lfilter_conj} *}

lemma findRel_conj_lemma [rule_format]:
     "(l,l') \<in> findRel q  
      ==> l' = LCons x l'' --> p x --> (l,l') \<in> findRel (%x. p x & q x)"
by (erule findRel.induct, auto)

lemmas findRel_conj = findRel_conj_lemma [OF _ refl]

lemma findRel_not_conj_Domain [rule_format]:
     "(l,l'') \<in> findRel (%x. p x & q x)  
      ==> (l, LCons x l') \<in> findRel q --> ~ p x --> 
          l' \<in> Domain (findRel (%x. p x & q x))"
by (erule findRel.induct, auto)

lemma findRel_conj2 [rule_format]:
     "(l,lxx) \<in> findRel q 
      ==> lxx = LCons x lx --> (lx,lz) \<in> findRel(%x. p x & q x) --> ~ p x  
          --> (l,lz) \<in> findRel (%x. p x & q x)"
by (erule findRel.induct, auto)

lemma findRel_lfilter_Domain_conj [rule_format]:
     "(lx,ly) \<in> findRel p  
      ==> \<forall>l. lx = lfilter q l --> l \<in> Domain (findRel(%x. p x & q x))"
apply (erule findRel.induct)
 apply (blast dest!: sym [THEN lfilter_eq_LCons] intro: findRel_conj, auto)
apply (drule sym [THEN lfilter_eq_LCons], auto)
apply (drule spec)
apply (drule refl [THEN rev_mp])
apply (blast intro: findRel_conj2)
done


lemma findRel_conj_lfilter [rule_format]:
     "(l,l'') \<in> findRel(%x. p x & q x)  
      ==> l'' = LCons y l' --> 
          (lfilter q l, LCons y (lfilter q l')) \<in> findRel p"
by (erule findRel.induct, auto)

lemma lfilter_conj_lemma:
     "(lfilter p (lfilter q l), lfilter (%x. p x & q x) l)   
      \<in> llistD_Fun (range (%u. (lfilter p (lfilter q u),           
                                lfilter (%x. p x & q x) u)))"
apply (case_tac "l \<in> Domain (findRel q)")
 apply (subgoal_tac [2] "l ~: Domain (findRel (%x. p x & q x))")
  prefer 3 apply (blast intro: rev_subsetD [OF _ Domain_findRel_mono])
 txt{*There are no @{text qs} in @{text l}: both lists are @{text LNil}*}
 apply (simp_all add: Domain_findRel_iff, clarify) 
txt{*case @{text "q x"}*}
apply (case_tac "p x")
 apply (simp_all add: findRel_conj [THEN findRel_imp_lfilter])
 txt{*case @{text "q x"} and @{text "~(p x)"} *}
apply (case_tac "l' \<in> Domain (findRel (%x. p x & q x))")
 txt{*subcase: there is no @{text "p & q"} in @{text l'} and therefore none in @{text l}*}
 apply (subgoal_tac [2] "l ~: Domain (findRel (%x. p x & q x))")
  prefer 3 apply (blast intro: findRel_not_conj_Domain)
 apply (subgoal_tac [2] "lfilter q l' ~: Domain (findRel p) ")
  prefer 3 apply (blast intro: findRel_lfilter_Domain_conj)
 txt{*    {\dots} and therefore too, no @{text p} in @{text "lfilter q l'"}.
   Both results are @{text LNil}*}
 apply (simp_all add: Domain_findRel_iff, clarify) 
txt{*subcase: there is a @{text "p & q"} in @{text l'} and therefore also one in @{text l} *}
apply (subgoal_tac " (l, LCons xa l'a) \<in> findRel (%x. p x & q x) ")
 prefer 2 apply (blast intro: findRel_conj2)
apply (subgoal_tac " (lfilter q l', LCons xa (lfilter q l'a)) \<in> findRel p")
 apply simp 
apply (blast intro: findRel_conj_lfilter)
done


lemma lfilter_conj: "lfilter p (lfilter q l) = lfilter (%x. p x & q x) l"
apply (rule_tac l = "l" in llist_fun_equalityI, simp_all)
apply (blast intro: lfilter_conj_lemma rev_subsetD [OF _ llistD_Fun_mono])
done


subsection {* Numerous lemmas required to prove ??:
     @{text "lfilter p (lmap f l) = lmap f (lfilter (%x. p(f x)) l)"}
 *}

lemma findRel_lmap_Domain:
     "(l,l') \<in> findRel(%x. p (f x)) ==> lmap f l \<in> Domain(findRel p)"
by (erule findRel.induct, auto)

lemma lmap_eq_LCons [rule_format]: "lmap f l = LCons x l' -->      
               (\<exists>y l''. x = f y & l' = lmap f l'' & l = LCons y l'')"
apply (subst lmap_def [THEN def_llist_corec])
apply (rule_tac l = "l" in llistE, auto)
done


lemma lmap_LCons_findRel_lemma [rule_format]:
     "(lx,ly) \<in> findRel p
      ==> \<forall>l. lmap f l = lx --> ly = LCons x l' -->  
          (\<exists>y l''. x = f y & l' = lmap f l'' &        
          (l, LCons y l'') \<in> findRel(%x. p(f x)))"
apply (erule findRel.induct, simp_all)
apply (blast dest!: lmap_eq_LCons)+
done

lemmas lmap_LCons_findRel = lmap_LCons_findRel_lemma [OF _ refl refl]

lemma lfilter_lmap: "lfilter p (lmap f l) = lmap f (lfilter (p o f) l)"
apply (rule_tac l = "l" in llist_fun_equalityI, simp_all)
apply safe
apply (case_tac "lmap f l \<in> Domain (findRel p)")
 apply (simp add: Domain_findRel_iff, clarify)
 apply (frule lmap_LCons_findRel, force) 
apply (subgoal_tac "l ~: Domain (findRel (%x. p (f x)))", simp)
apply (blast intro: findRel_lmap_Domain)
done

end
