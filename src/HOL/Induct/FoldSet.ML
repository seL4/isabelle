(*  Title:      HOL/FoldSet
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1998  University of Cambridge

A "fold" functional for finite sets
*)

val empty_foldSetE = foldSet.mk_cases [] "({}, x) : foldSet f e";

AddSEs [empty_foldSetE];
AddIs foldSet.intrs;

Goal "[| (A-{x},y) : foldSet f e;  x: A |] ==> (A, f x y) : foldSet f e";
by (etac (insert_Diff RS subst) 1 THEN resolve_tac foldSet.intrs 1);
by Auto_tac;
qed "Diff_foldSet";

Goal "(A, x) : foldSet f e ==> finite(A)";
by (eresolve_tac [foldSet.induct] 1);
by Auto_tac;
qed "foldSet_imp_finite";

Addsimps [foldSet_imp_finite];


Goal "finite(A) ==> EX x. (A, x) : foldSet f e";
by (etac finite_induct 1);
by Auto_tac;
qed "finite_imp_foldSet";


Open_locale "ACI"; 

(*Strip meta-quantifiers: perhaps the locale should do this?*)
val f_ident   = forall_elim_vars 0 (thm "ident");
val f_commute = forall_elim_vars 0 (thm "commute");
val f_assoc   = forall_elim_vars 0 (thm "assoc");


Goal "f x (f y z) = f y (f x z)";
by (rtac (f_commute RS trans) 1);
by (rtac (f_assoc RS trans) 1);
by (rtac (f_commute RS arg_cong) 1);
qed "f_left_commute";

(*Addition is an AC-operator*)
val f_ac = [f_assoc, f_commute, f_left_commute];

Goal "f e x = x";
by (stac f_commute 1);
by (rtac f_ident 1);
qed "f_left_ident";

Addsimps [f_left_ident, f_ident];


Goal "ALL A x. card(A) < n --> (A, x) : foldSet f e --> \
\            (ALL y. (A, y) : foldSet f e --> y=x)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq]));
by (etac foldSet.elim 1);
by (Blast_tac 1);
by (etac foldSet.elim 1);
by (Blast_tac 1);
by (Clarify_tac 1);
(*force simplification of "card A < card (insert ...)"*)
by (etac rev_mp 1);
by (asm_simp_tac (simpset() addsimps [less_Suc_eq_le]) 1);
by (rtac impI 1);
(** LEVEL 10 **)
by (rename_tac "Aa xa ya Ab xb yb" 1);
 by (case_tac "xa=xb" 1);
 by (subgoal_tac "Aa = Ab" 1);
 by (blast_tac (claset() addEs [equalityE]) 2);
 by (Blast_tac 1);
(*case xa ~= xb*)
by (subgoal_tac "Aa-{xb} = Ab-{xa} & xb : Aa & xa : Ab" 1);
 by (blast_tac (claset() addEs [equalityE]) 2);
by (Clarify_tac 1);
by (subgoal_tac "Aa = insert xb Ab - {xa}" 1);
 by (blast_tac (claset() addEs [equalityE]) 2);
(** LEVEL 20 **)
by (subgoal_tac "card Aa <= card Ab" 1);
 by (rtac (Suc_le_mono RS subst) 2);
 by (asm_simp_tac (simpset() addsimps [card_Suc_Diff]) 2);
by (res_inst_tac [("A1", "Aa-{xb}"), ("f1","f")] 
    (finite_imp_foldSet RS exE) 1);
by (blast_tac (claset() addIs [foldSet_imp_finite, finite_Diff]) 1);
by (forward_tac [Diff_foldSet] 1 THEN assume_tac 1);
by (subgoal_tac "ya = f xb x" 1);
 by (Blast_tac 2);
by (subgoal_tac "(Ab - {xa}, x) : foldSet f e" 1);
 by (Asm_full_simp_tac 2);
by (subgoal_tac "yb = f xa x" 1);
 by (blast_tac (claset() addDs [Diff_foldSet]) 2);
by (asm_simp_tac (simpset() addsimps f_ac) 1);
val lemma = result();


Goal "[| (A, x) : foldSet f e;  (A, y) : foldSet f e |] ==> y=x";
by (blast_tac (claset() addIs [normalize_thm [RSspec, RSmp] lemma]) 1);
qed "foldSet_determ";

Goalw [fold_def] "(A,y) : foldSet f e ==> fold f e A = y";
by (blast_tac (claset() addIs [foldSet_determ]) 1);
qed "fold_equality";

Goalw [fold_def] "fold f e {} = e";
by (Blast_tac 1);
qed "fold_empty";
Addsimps [fold_empty];

Goal "x ~: A ==> \
\     ((insert x A, v) : foldSet f e) =  \
\     (EX y. (A, y) : foldSet f e & v = f x y)";
by Auto_tac;
by (res_inst_tac [("A1", "A"), ("f1","f")] (finite_imp_foldSet RS exE) 1);
by (force_tac (claset() addDs [foldSet_imp_finite], simpset()) 1);
by (blast_tac (claset() addIs [foldSet_determ]) 1);
val lemma = result();


Goalw [fold_def]
     "[| finite A; x ~: A |] ==> fold f e (insert x A) = f x (fold f e A)";
by (asm_simp_tac (simpset() addsimps [lemma]) 1);
by (rtac select_equality 1);
by (auto_tac (claset() addIs [finite_imp_foldSet],
	      simpset() addcongs [conj_cong]
		        addsimps [symmetric fold_def,
				  fold_equality]));
qed "fold_insert";
Addsimps [fold_insert];

Goal "[| finite A; finite B |] \
\     ==> f (fold f e A) (fold f e B) =  \
\         f (fold f e (A Un B)) (fold f e (A Int B))";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_simp_tac
    (simpset() addsimps f_ac @ [insert_absorb, Int_insert_left]) 1);
by (rtac impI 1);
by (stac f_commute 1 THEN rtac refl 1);
qed "fold_Un_Int";

Goal "[| finite A; finite B; A Int B = {} |] \
\     ==> fold f e (A Un B) = f (fold f e A) (fold f e B)";
by (asm_simp_tac (simpset() addsimps [fold_Un_Int]) 1);
qed "fold_Un_disjoint";


Close_locale();

