(*  Title:      HOL/ex/LFilter
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

The "filter" functional for coinductive lists
  --defined by a combination of induction and coinduction
*)

open LFilter;


(*** findRel: basic laws ****)

val findRel_LConsE = 
    findRel.mk_cases [LCons_LCons_eq] "(LCons x l, l'') : findRel p";

AddSEs [findRel_LConsE];


goal thy "!!p. (l,l'): findRel p ==> (l,l''): findRel p --> l'' = l'";
be findRel.induct 1;
by (Blast_tac 1);
by (Blast_tac 1);
qed_spec_mp "findRel_functional";

goal thy "!!p. (l,l'): findRel p ==> EX x l''. l' = LCons x l'' & p x";
be findRel.induct 1;
by (Blast_tac 1);
by (Blast_tac 1);
qed_spec_mp "findRel_imp_LCons";

goal thy "!!p. (LNil,l): findRel p ==> R";
by (blast_tac (!claset addEs [findRel.elim]) 1);
qed "findRel_LNil";

AddSEs [findRel_LNil];


(*** Properties of Domain (findRel p) ***)

goal thy "!!p. LCons x l : Domain(findRel p) = (p x | l : Domain(findRel p))";
by (case_tac "p x" 1);
by (ALLGOALS (blast_tac (!claset addIs findRel.intrs)));
qed "LCons_Domain_findRel";

Addsimps [LCons_Domain_findRel];

val major::prems = 
goal thy "[| l: Domain (findRel p);                                   \
\            !!x l'. [| (l, LCons x l') : findRel p;  p x |] ==> Q    \
\         |] ==> Q";
br (major RS DomainE) 1;
by (forward_tac [findRel_imp_LCons] 1);
by (REPEAT (eresolve_tac [exE,conjE] 1));
by (hyp_subst_tac 1);
by (REPEAT (ares_tac prems 1));
qed "Domain_findRelE";

val prems = goal thy
    "[| !!x. p x ==> q x |] ==> Domain (findRel p) <= Domain (findRel q)";
by (Step_tac 1);
be findRel.induct 1;
by (blast_tac (!claset addIs (findRel.intrs@prems)) 1);
by (blast_tac (!claset addIs findRel.intrs) 1);
qed "Domain_findRel_mono";


(*** find: basic equations ***)

goalw thy [find_def] "find p LNil = LNil";
by (blast_tac (!claset addIs [select_equality]) 1);
qed "find_LNil";

goalw thy [find_def] "!!p. (l,l') : findRel p ==> find p l = l'";
by (blast_tac (!claset addIs [select_equality] addDs [findRel_functional]) 1);
qed "findRel_imp_find";

goal thy "!!p. p x ==> find p (LCons x l) = LCons x l";
by (blast_tac (!claset addIs (findRel_imp_find::findRel.intrs)) 1);
qed "find_LCons_found";

goalw thy [find_def] "!!p. l ~: Domain(findRel p) ==> find p l = LNil";
by (blast_tac (!claset addIs [select_equality]) 1);
qed "diverge_find_LNil";

Addsimps [diverge_find_LNil];

goal thy "!!p. ~ (p x) ==> find p (LCons x l) = find p l";
by (case_tac "LCons x l : Domain(findRel p)" 1);
by (Asm_full_simp_tac 2);
by (Step_tac 1);
by (asm_simp_tac (!simpset addsimps [findRel_imp_find]) 1);
by (blast_tac (!claset addIs (findRel_imp_find::findRel.intrs)) 1);
qed "find_LCons_seek";

goal thy "find p (LCons x l) = (if p x then LCons x l else find p l)";
by (asm_simp_tac (!simpset addsimps [find_LCons_found, find_LCons_seek]
		           setloop split_tac[expand_if]) 1);
qed "find_LCons";



(*** lfilter: basic equations ***)

goal thy "lfilter p LNil = LNil";
by (rtac (lfilter_def RS def_llist_corec RS trans) 1);
by (simp_tac (!simpset addsimps [find_LNil]) 1);
qed "lfilter_LNil";

goal thy "!!p. l ~: Domain(findRel p) ==> lfilter p l = LNil";
by (rtac (lfilter_def RS def_llist_corec RS trans) 1);
by (Asm_simp_tac 1);
qed "diverge_lfilter_LNil";


goal thy "!!p. p x ==> lfilter p (LCons x l) = LCons x (lfilter p l)";
by (rtac (lfilter_def RS def_llist_corec RS trans) 1);
by (asm_simp_tac (!simpset addsimps [find_LCons_found]) 1);
qed "lfilter_LCons_found";


goal thy "!!p. (l, LCons x l') : findRel p \
\              ==> lfilter p l = LCons x (lfilter p l')";
by (rtac (lfilter_def RS def_llist_corec RS trans) 1);
by (asm_simp_tac (!simpset addsimps [findRel_imp_find]) 1);
qed "findRel_imp_lfilter";

goal thy "!!p. ~ (p x) ==> lfilter p (LCons x l) = lfilter p l";
by (rtac (lfilter_def RS def_llist_corec RS trans) 1);
by (case_tac "LCons x l : Domain(findRel p)" 1);
by (asm_full_simp_tac (!simpset addsimps [diverge_lfilter_LNil]) 2);
be Domain_findRelE 1;
by (safe_tac (!claset delrules [conjI]));
by (asm_full_simp_tac 
    (!simpset addsimps [findRel_imp_lfilter, findRel_imp_find,
			find_LCons_seek]) 1);
qed "lfilter_LCons_seek";


goal thy "lfilter p (LCons x l) = \
\         (if p x then LCons x (lfilter p l) else lfilter p l)";
by (asm_simp_tac (!simpset addsimps [lfilter_LCons_found, lfilter_LCons_seek]
		           setloop split_tac[expand_if]) 1);
qed "lfilter_LCons";

AddSIs [llistD_Fun_LNil_I, llistD_Fun_LCons_I];
Addsimps [lfilter_LNil, lfilter_LCons];


goal thy "!!p. lfilter p l = LNil ==> l ~: Domain(findRel p)";
br notI 1;
be Domain_findRelE 1;
be rev_mp 1;
by (asm_simp_tac (!simpset addsimps [findRel_imp_lfilter]) 1);
qed "lfilter_eq_LNil";


goal thy "!!p. lfilter p l = LCons x l' -->     \
\              (EX l''. l' = lfilter p l'' & (l, LCons x l'') : findRel p)";
by (stac (lfilter_def RS def_llist_corec) 1);
by (case_tac "l : Domain(findRel p)" 1);
be Domain_findRelE 1;
by (Asm_simp_tac 2);
by (asm_simp_tac (!simpset addsimps [findRel_imp_find]) 1);
by (Blast_tac 1);
qed_spec_mp "lfilter_eq_LCons";


goal thy "lfilter p l = LNil  |  \
\         (EX y l'. lfilter p l = LCons y (lfilter p l') & p y)";
by (case_tac "l : Domain(findRel p)" 1);
by (asm_simp_tac (!simpset addsimps [diverge_lfilter_LNil]) 2);
by (blast_tac (!claset addSEs [Domain_findRelE] 
                       addIs [findRel_imp_lfilter]) 1);
qed "lfilter_cases";


(*** lfilter: simple facts by coinduction ***)

goal thy "lfilter (%x.True) l = l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS Simp_tac);
by (Blast_tac 1);
qed "lfilter_K_True";

goal thy "lfilter p (lfilter p l) = lfilter p l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS (simp_tac (!simpset setloop split_tac[expand_if])));
by (Step_tac 1);
(*Cases: p x is true or false*)
by (Blast_tac 1);
br (lfilter_cases RS disjE) 1;
be ssubst 1;
by (Auto_tac());
qed "lfilter_idem";


(*** Numerous lemmas required to prove lfilter_conj:
     lfilter p (lfilter q l) = lfilter (%x. p x & q x) l
 ***)

goal thy "!!p. (l,l') : findRel q \
\           ==> l' = LCons x l'' --> p x --> (l,l') : findRel (%x. p x & q x)";
be findRel.induct 1;
by (blast_tac (!claset addIs findRel.intrs) 1);
by (blast_tac (!claset addIs findRel.intrs) 1);
qed_spec_mp "findRel_conj_lemma";

val findRel_conj = refl RSN (2, findRel_conj_lemma);

goal thy "!!p. (l,l'') : findRel (%x. p x & q x) \
\              ==> (l, LCons x l') : findRel q --> ~ p x     \
\                  --> l' : Domain (findRel (%x. p x & q x))";
be findRel.induct 1;
by (Auto_tac());
qed_spec_mp "findRel_not_conj_Domain";


goal thy "!!p. (l,lxx) : findRel q ==> \
\            lxx = LCons x lx --> (lx,lz) : findRel(%x. p x & q x) --> ~ p x \
\            --> (l,lz) : findRel (%x. p x & q x)";
be findRel.induct 1;
by (ALLGOALS (blast_tac (!claset addIs findRel.intrs)));
qed_spec_mp "findRel_conj2";


goal thy "!!p. (lx,ly) : findRel p \
\              ==> ALL l. lx = lfilter q l \
\                  --> l : Domain (findRel(%x. p x & q x))";
be findRel.induct 1;
by (blast_tac (!claset addSDs [sym RS lfilter_eq_LCons]
	               addIs  [findRel_conj]) 1);
by (Auto_tac());
bd (sym RS lfilter_eq_LCons) 1;
by (Auto_tac());
bd spec 1;
bd (refl RS rev_mp) 1;
by (blast_tac (!claset addIs [findRel_conj2]) 1);
qed_spec_mp "findRel_lfilter_Domain_conj";


goal thy "!!p. (l,l'') : findRel(%x. p x & q x) \
\              ==> l'' = LCons y l' --> \
\                  (lfilter q l, LCons y (lfilter q l')) : findRel p";
be findRel.induct 1;
by (ALLGOALS (asm_simp_tac (!simpset setloop split_tac[expand_if])));
by (ALLGOALS (blast_tac (!claset addIs findRel.intrs)));
qed_spec_mp "findRel_conj_lfilter";



goal thy "(lfilter p (lfilter q l), lfilter (%x. p x & q x) l)  \
\         : llistD_Fun (range                                   \
\                       (%u. (lfilter p (lfilter q u),          \
\                             lfilter (%x. p x & q x) u)))";
by (case_tac "l : Domain(findRel q)" 1);
by (subgoal_tac "l ~: Domain (findRel (%x. p x & q x))" 2);
by (blast_tac (!claset addIs [impOfSubs Domain_findRel_mono]) 3);
(*There are no qs in l: both lists are LNil*)
by (asm_simp_tac (!simpset addsimps [diverge_lfilter_LNil]) 2);
by (etac Domain_findRelE 1);
(*case q x*)
by (case_tac "p x" 1);
by (asm_simp_tac (!simpset addsimps [findRel_imp_lfilter,
				     findRel_conj RS findRel_imp_lfilter]) 1);
by (Blast_tac 1);
(*case q x and ~(p x) *)
by (asm_simp_tac (!simpset addsimps [findRel_imp_lfilter]) 1);
by (case_tac "l' : Domain (findRel (%x. p x & q x))" 1);
(*subcase: there is no p&q in l' and therefore none in l*)
by (subgoal_tac "l ~: Domain (findRel (%x. p x & q x))" 2);
by (blast_tac (!claset addIs [findRel_not_conj_Domain]) 3);
by (subgoal_tac "lfilter q l' ~: Domain(findRel p)" 2);
by (blast_tac (!claset addIs [findRel_lfilter_Domain_conj]) 3);
(*    ...and therefore too, no p in lfilter q l'.  Both results are Lnil*)
by (asm_simp_tac (!simpset addsimps [diverge_lfilter_LNil]) 2);
(*subcase: there is a p&q in l' and therefore also one in l*)
be Domain_findRelE 1;
by (subgoal_tac "(l, LCons xa l'a) : findRel(%x. p x & q x)" 1);
by (blast_tac (!claset addIs [findRel_conj2]) 2);
by (subgoal_tac "(lfilter q l', LCons xa (lfilter q l'a)) : findRel p" 1);
by (blast_tac (!claset addIs [findRel_conj_lfilter]) 2);
by (asm_simp_tac (!simpset addsimps [findRel_imp_lfilter]) 1);
by (Blast_tac 1);
val lemma = result();


goal thy "lfilter p (lfilter q l) = lfilter (%x. p x & q x) l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS (simp_tac (!simpset setloop split_tac[expand_if])));
by (blast_tac (!claset addIs [lemma, impOfSubs llistD_Fun_mono]) 1);
qed "lfilter_conj";


(*** Numerous lemmas required to prove ??:
     lfilter p (lmap f l) = lmap f (lfilter (%x. p(f x)) l)
 ***)

goal thy "!!p. (l,l') : findRel(%x. p (f x)) ==> lmap f l : Domain(findRel p)";
be findRel.induct 1;
by (ALLGOALS Asm_full_simp_tac);
qed "findRel_lmap_Domain";


goal thy "!!p. lmap f l = LCons x l' -->     \
\              (EX y l''. x = f y & l' = lmap f l'' & l = LCons y l'')";
by (stac (lmap_def RS def_llist_corec) 1);
by (res_inst_tac [("l", "l")] llistE 1);
by (Auto_tac());
qed_spec_mp "lmap_eq_LCons";


goal thy "!!p. (lx,ly) : findRel p ==>  \
\    ALL l. lmap f l = lx --> ly = LCons x l' --> \
\    (EX y l''. x = f y & l' = lmap f l'' &       \
\    (l, LCons y l'') : findRel(%x. p(f x)))";
be findRel.induct 1;
by (ALLGOALS Asm_simp_tac);
by (safe_tac (!claset addSDs [lmap_eq_LCons]));
by (blast_tac (!claset addIs findRel.intrs) 1);
by (blast_tac (!claset addIs findRel.intrs) 1);
qed_spec_mp "lmap_LCons_findRel_lemma";

val lmap_LCons_findRel = refl RSN (2, refl RSN (2, lmap_LCons_findRel_lemma));

goal thy "lfilter p (lmap f l) = lmap f (lfilter (p o f) l)";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS (simp_tac (!simpset setloop split_tac[expand_if])));
by (Step_tac 1);
by (Blast_tac 1);
by (case_tac "lmap f l : Domain (findRel p)" 1);
by (subgoal_tac "l ~: Domain (findRel(%x. p (f x)))" 2);
by (blast_tac (!claset addIs [findRel_lmap_Domain]) 3);
by (asm_simp_tac (!simpset addsimps [diverge_lfilter_LNil]) 2);
be Domain_findRelE 1;
by (forward_tac [lmap_LCons_findRel] 1);
by (Step_tac 1);
by (asm_simp_tac (!simpset addsimps [findRel_imp_lfilter]) 1);
by (Blast_tac 1);
qed "lfilter_lmap";
