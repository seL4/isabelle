(*  Title:      HOL/Finite.ML
    ID:         $Id$
    Author:     Lawrence C Paulson & Tobias Nipkow
    Copyright   1995  University of Cambridge & TU Muenchen

Finite sets and their cardinality.
*)

section "finite";

(*Discharging ~ x:y entails extra work*)
val major::prems = Goal 
    "[| finite F;  P({}); \
\       !!F x. [| finite F;  x ~: F;  P(F) |] ==> P(insert x F) \
\    |] ==> P(F)";
by (rtac (major RS Finites.induct) 1);
by (excluded_middle_tac "a:A" 2);
by (etac (insert_absorb RS ssubst) 3 THEN assume_tac 3);   (*backtracking!*)
by (REPEAT (ares_tac prems 1));
qed "finite_induct";

val major::subs::prems = Goal 
    "[| finite F;  F <= A; \
\       P({}); \
\       !!F a. [| finite F; a:A; a ~: F;  P(F) |] ==> P(insert a F) \
\    |] ==> P(F)";
by (rtac (subs RS rev_mp) 1);
by (rtac (major RS finite_induct) 1);
by (ALLGOALS (blast_tac (claset() addIs prems)));
qed "finite_subset_induct";

Addsimps Finites.intrs;
AddSIs Finites.intrs;

(*The union of two finite sets is finite*)
Goal "[| finite F;  finite G |] ==> finite(F Un G)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "finite_UnI";

(*Every subset of a finite set is finite*)
Goal "finite B ==> ALL A. A<=B --> finite A";
by (etac finite_induct 1);
by (ALLGOALS (simp_tac (simpset() addsimps [subset_insert_iff])));
by Safe_tac;
 by (eres_inst_tac [("t","A")] (insert_Diff RS subst) 1);
 by (ALLGOALS Blast_tac);
val lemma = result();

Goal "[| A<=B;  finite B |] ==> finite A";
by (dtac lemma 1);
by (Blast_tac 1);
qed "finite_subset";

Goal "finite(F Un G) = (finite F & finite G)";
by (blast_tac (claset() 
	         addIs [inst "B" "?X Un ?Y" finite_subset, finite_UnI]) 1);
qed "finite_Un";
AddIffs[finite_Un];

(*The converse obviously fails*)
Goal "finite F | finite G ==> finite(F Int G)";
by (blast_tac (claset() addIs [finite_subset]) 1);
qed "finite_Int";

Addsimps [finite_Int];
AddIs [finite_Int];

Goal "finite(insert a A) = finite A";
by (stac insert_is_Un 1);
by (simp_tac (HOL_ss addsimps [finite_Un]) 1);
by (Blast_tac 1);
qed "finite_insert";
Addsimps[finite_insert];

(*The image of a finite set is finite *)
Goal  "finite F ==> finite(h`F)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "finite_imageI";

Goal "finite (range g) ==> finite (range (%x. f (g x)))";
by (Simp_tac 1);
by (etac finite_imageI 1);
qed "finite_range_imageI";

val major::prems = Goal 
    "[| finite c;  finite b;                                  \
\       P(b);                                                   \
\       !!x y. [| finite y;  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> c<=b --> P(b-c)";
by (rtac (major RS finite_induct) 1);
by (stac Diff_insert 2);
by (ALLGOALS (asm_simp_tac
                (simpset() addsimps prems@[Diff_subset RS finite_subset])));
val lemma = result();

val prems = Goal 
    "[| finite A;                                       \
\       P(A);                                           \
\       !!a A. [| finite A;  a:A;  P(A) |] ==> P(A-{a}) \
\    |] ==> P({})";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (lemma RS mp) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
qed "finite_empty_induct";


(* finite B ==> finite (B - Ba) *)
bind_thm ("finite_Diff", Diff_subset RS finite_subset);
Addsimps [finite_Diff];

Goal "finite(A - insert a B) = finite(A-B)";
by (stac Diff_insert 1);
by (case_tac "a : A-B" 1);
by (rtac (finite_insert RS sym RS trans) 1);
by (stac insert_Diff 1);
by (ALLGOALS Asm_full_simp_tac);
qed "finite_Diff_insert";
AddIffs [finite_Diff_insert];

(*lemma merely for classical reasoner in the proof below: force_tac can't
  prove it.*)
Goal "finite(A-{}) = finite A";
by (Simp_tac 1);
val lemma = result();

(*Lemma for proving finite_imageD*)
Goal "finite B ==> ALL A. f`A = B --> inj_on f A --> finite A";
by (etac finite_induct 1);
 by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (subgoal_tac "EX y:A. f y = x & F = f`(A-{y})" 1);
 by (Clarify_tac 1);
 by (full_simp_tac (simpset() addsimps [inj_on_def]) 1);
 by (blast_tac (claset() addSDs [lemma RS iffD1]) 1);
by (thin_tac "ALL A. ?PP(A)" 1);
by (forward_tac [[equalityD2, insertI1] MRS subsetD] 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","xa")] bexI 1);
by (ALLGOALS 
    (asm_full_simp_tac (simpset() addsimps [inj_on_image_set_diff])));
val lemma = result();

Goal "[| finite(f`A);  inj_on f A |] ==> finite A";
by (dtac lemma 1);
by (Blast_tac 1);
qed "finite_imageD";

(** The finite UNION of finite sets **)

Goal "finite A ==> (ALL a:A. finite(B a)) --> finite(UN a:A. B a)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
bind_thm("finite_UN_I", ballI RSN (2, result() RS mp));

(*strengthen RHS to 
    ((ALL x:A. finite (B x)) & finite {x. x:A & B x ~= {}})  ?  
  we'd need to prove
    finite C ==> ALL A B. (UNION A B) <= C --> finite {x. x:A & B x ~= {}}
  by induction*)
Goal "finite A ==> finite (UNION A B) = (ALL x:A. finite (B x))";
by (blast_tac (claset() addIs [finite_UN_I, finite_subset]) 1);
qed "finite_UN";
Addsimps [finite_UN];

(** Sigma of finite sets **)

Goalw [Sigma_def]
 "[| finite A; ALL a:A. finite(B a) |] ==> finite(SIGMA a:A. B a)";
by (blast_tac (claset() addSIs [finite_UN_I]) 1);
bind_thm("finite_SigmaI", ballI RSN (2,result()));
Addsimps [finite_SigmaI];

Goal "[| finite (UNIV::'a set); finite (UNIV::'b set)|] ==> finite (UNIV::('a * 'b) set)"; 
by (subgoal_tac "(UNIV::('a * 'b) set) = Sigma UNIV (%x. UNIV)" 1);
by  (etac ssubst 1);
by  (etac finite_SigmaI 1);
by  Auto_tac;
qed "finite_Prod_UNIV";

Goal "finite (UNIV :: ('a::finite * 'b::finite) set)";
by (rtac (finite_Prod_UNIV) 1);
by (rtac finite 1);
by (rtac finite 1);
qed "finite_Prod";

Goal "finite (UNIV :: unit set)";
by (subgoal_tac "UNIV = {()}" 1);
by (etac ssubst 1);
by Auto_tac;
qed "finite_unit";

(** The powerset of a finite set **)

Goal "finite(Pow A) ==> finite A";
by (subgoal_tac "finite ((%x.{x})`A)" 1);
by (rtac finite_subset 2);
by (assume_tac 3);
by (ALLGOALS
    (fast_tac (claset() addSDs [rewrite_rule [inj_on_def] finite_imageD])));
val lemma = result();

Goal "finite(Pow A) = finite A";
by (rtac iffI 1);
by (etac lemma 1);
(*Opposite inclusion: finite A ==> finite (Pow A) *)
by (etac finite_induct 1);
by (ALLGOALS 
    (asm_simp_tac
     (simpset() addsimps [finite_UnI, finite_imageI, Pow_insert])));
qed "finite_Pow_iff";
AddIffs [finite_Pow_iff];

Goal "finite(r^-1) = finite r";
by (subgoal_tac "r^-1 = (%(x,y).(y,x))`r" 1);
 by (Asm_simp_tac 1);
 by (rtac iffI 1);
  by (etac (rewrite_rule [inj_on_def] finite_imageD) 1);
  by (simp_tac (simpset() addsplits [split_split]) 1);
 by (etac finite_imageI 1);
by (simp_tac (simpset() addsimps [converse_def,image_def]) 1);
by Auto_tac;
by (rtac bexI 1);
by  (assume_tac 2);
by (Simp_tac 1);
qed "finite_converse";
AddIffs [finite_converse];

Goal "finite (lessThan (k::nat))";
by (induct_tac "k" 1);
by (simp_tac (simpset() addsimps [lessThan_Suc]) 2);
by Auto_tac;
qed "finite_lessThan";

Goal "finite (atMost (k::nat))";
by (induct_tac "k" 1);
by (simp_tac (simpset() addsimps [atMost_Suc]) 2);
by Auto_tac;
qed "finite_atMost";
AddIffs [finite_lessThan, finite_atMost];

(* A bounded set of natural numbers is finite *)
Goal "(ALL i:N. i<(n::nat)) ==> finite N";
by (rtac finite_subset 1);
 by (rtac finite_lessThan 2);
by Auto_tac;
qed "bounded_nat_set_is_finite";

(** Finiteness of transitive closure (thanks to Sidi Ehmety) **)

(*A finite relation has a finite field ( = domain U range) *)
Goal "finite r ==> finite (Field r)";
by (etac finite_induct 1);
by (auto_tac (claset(), 
              simpset() addsimps [Field_def, Domain_insert, Range_insert]));
qed "finite_Field";

Goal "r^+ <= Field r <*> Field r";
by (Clarify_tac 1);
by (etac trancl_induct 1);
by (auto_tac (claset(), simpset() addsimps [Field_def]));  
qed "trancl_subset_Field2";

Goal "finite (r^+) = finite r";
by Auto_tac;
by (rtac (trancl_subset_Field2 RS finite_subset) 2);
by (rtac finite_SigmaI 2);
by (blast_tac (claset() addIs [r_into_trancl, finite_subset]) 1);
by (auto_tac (claset(), simpset() addsimps [finite_Field]));  
qed "finite_trancl";


section "Finite cardinality -- 'card'";

bind_thm ("cardR_emptyE", cardR.mk_cases "({},n) : cardR");
bind_thm ("cardR_insertE", cardR.mk_cases "(insert a A,n) : cardR");

AddSEs [cardR_emptyE];
AddSIs cardR.intrs;

Goal "[| (A,n) : cardR |] ==> a : A --> (EX m. n = Suc m)";
by (etac cardR.induct 1);
 by (Blast_tac 1);
by (Blast_tac 1);
qed "cardR_SucD";

Goal "(A,m): cardR ==> (ALL n a. m = Suc n --> a:A --> (A-{a},n) : cardR)";
by (etac cardR.induct 1);
 by Auto_tac;
by (asm_simp_tac (simpset() addsimps [insert_Diff_if]) 1);
by Auto_tac;
by (ftac cardR_SucD 1);
by (Blast_tac 1);
val lemma = result();

Goal "[| (insert a A, Suc m) : cardR; a ~: A |] ==> (A,m) : cardR";
by (dtac lemma 1);
by (Asm_full_simp_tac 1);
val lemma = result();

Goal "(A,m): cardR ==> (ALL n. (A,n) : cardR --> n=m)";
by (etac cardR.induct 1);
 by (safe_tac (claset() addSEs [cardR_insertE]));
by (rename_tac "B b m" 1 THEN case_tac "a = b" 1);
 by (subgoal_tac "A = B" 1);
  by (blast_tac (claset() addEs [equalityE]) 2);
 by (Blast_tac 1);
by (subgoal_tac "EX C. A = insert b C & B = insert a C" 1);
 by (res_inst_tac [("x","A Int B")] exI 2);
 by (blast_tac (claset() addEs [equalityE]) 2);
by (forw_inst_tac [("A","B")] cardR_SucD 1);
by (blast_tac (claset() addDs [lemma]) 1);
qed_spec_mp "cardR_determ";

Goal "(A,n) : cardR ==> finite(A)";
by (etac cardR.induct 1);
by Auto_tac;
qed "cardR_imp_finite";

Goal "finite(A) ==> EX n. (A, n) : cardR";
by (etac finite_induct 1);
by Auto_tac;
qed "finite_imp_cardR";

Goalw [card_def] "(A,n) : cardR ==> card A = n";
by (blast_tac (claset() addIs [cardR_determ]) 1);
qed "card_equality";

Goalw [card_def] "card {} = 0";
by (Blast_tac 1);
qed "card_empty";
Addsimps [card_empty];

Goal "x ~: A \
\     ==> ((insert x A, n) : cardR)  =  (EX m. (A, m) : cardR & n = Suc m)";
by Auto_tac;
by (res_inst_tac [("A1", "A")] (finite_imp_cardR RS exE) 1);
by (force_tac (claset() addDs [cardR_imp_finite], simpset()) 1);
by (blast_tac (claset() addIs [cardR_determ]) 1);
val lemma = result();

Goalw [card_def]
     "[| finite A; x ~: A |] ==> card (insert x A) = Suc(card A)";
by (asm_simp_tac (simpset() addsimps [lemma]) 1);
by (rtac the_equality 1);
by (auto_tac (claset() addIs [finite_imp_cardR],
	      simpset() addcongs [conj_cong]
		        addsimps [symmetric card_def,
				  card_equality]));
qed "card_insert_disjoint";
Addsimps [card_insert_disjoint];

(* Delete rules to do with cardR relation: obsolete *)
Delrules [cardR_emptyE];
Delrules cardR.intrs;

Goal "finite A ==> (card A = 0) = (A = {})";
by Auto_tac;
by (dres_inst_tac [("a","x")] mk_disjoint_insert 1);
by (Clarify_tac 1);
by (rotate_tac ~1 1);
by Auto_tac;
qed "card_0_eq";
Addsimps[card_0_eq];

Goal "finite A ==> card(insert x A) = (if x:A then card A else Suc(card(A)))";
by (asm_simp_tac (simpset() addsimps [insert_absorb]) 1);
qed "card_insert_if";

Goal "[| finite A; x: A |] ==> Suc (card (A-{x})) = card A";
by (res_inst_tac [("t", "A")] (insert_Diff RS subst) 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
qed "card_Suc_Diff1";

Goal "[| finite A; x: A |] ==> card (A-{x}) = card A - 1";
by (asm_simp_tac (simpset() addsimps [card_Suc_Diff1 RS sym]) 1);
qed "card_Diff_singleton";

Goal "finite A ==> card (A-{x}) = (if x:A then card A - 1 else card A)";
by (asm_simp_tac (simpset() addsimps [card_Diff_singleton]) 1);
qed "card_Diff_singleton_if";

Goal "finite A ==> card(insert x A) = Suc(card(A-{x}))";
by (asm_simp_tac (simpset() addsimps [card_insert_if,card_Suc_Diff1]) 1);
qed "card_insert";

Goal "finite A ==> card A <= card (insert x A)";
by (asm_simp_tac (simpset() addsimps [card_insert_if]) 1);
qed "card_insert_le";

Goal "finite B ==> ALL A. A <= B --> card B <= card A --> A = B";
by (etac finite_induct 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "finite A & A-{x} <= F" 1);
 by (blast_tac (claset() addIs [finite_subset]) 2); 
by (dres_inst_tac [("x","A-{x}")] spec 1); 
by (asm_full_simp_tac (simpset() addsimps [card_Diff_singleton_if]
                                 addsplits [split_if_asm]) 1); 
by (case_tac "card A" 1);
by Auto_tac; 
qed_spec_mp "card_seteq";

Goalw [psubset_def] "[| finite B;  A < B |] ==> card A < card B";
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (blast_tac (claset() addDs [card_seteq]) 1); 
qed "psubset_card_mono" ;

Goal "[| finite B;  A <= B |] ==> card A <= card B";
by (case_tac "A=B" 1);
 by (Asm_simp_tac 1); 
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
by (blast_tac (claset() addDs [card_seteq] addIs [order_less_imp_le]) 1); 
qed "card_mono" ;

Goal "[| finite A; finite B |] \
\     ==> card A + card B = card (A Un B) + card (A Int B)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [insert_absorb, Int_insert_left]) 1);
qed "card_Un_Int";

Goal "[| finite A; finite B; A Int B = {} |] \
\     ==> card (A Un B) = card A + card B";
by (asm_simp_tac (simpset() addsimps [card_Un_Int]) 1);
qed "card_Un_disjoint";

Goal "[| finite A; B<=A |] ==> card A - card B = card (A - B)";
by (subgoal_tac "(A-B) Un B = A" 1);
by (Blast_tac 2);
by (rtac (add_right_cancel RS iffD1) 1);
by (rtac (card_Un_disjoint RS subst) 1);
by (etac ssubst 4);
by (Blast_tac 3);
by (ALLGOALS 
    (asm_simp_tac
     (simpset() addsimps [add_commute, not_less_iff_le, 
			  add_diff_inverse, card_mono, finite_subset])));
qed "card_Diff_subset";

Goal "[| finite A; x: A |] ==> card(A-{x}) < card A";
by (rtac Suc_less_SucD 1);
by (asm_simp_tac (simpset() addsimps [card_Suc_Diff1]) 1);
qed "card_Diff1_less";

Goal "[| finite A; x: A; y: A |] ==> card(A-{x}-{y}) < card A"; 
by (case_tac "x=y" 1);
by (asm_simp_tac (simpset() addsimps [card_Diff1_less]) 1);
by (rtac less_trans 1);
by (ALLGOALS (force_tac (claset() addSIs [card_Diff1_less], simpset())));
qed "card_Diff2_less";

Goal "finite A ==> card(A-{x}) <= card A";
by (case_tac "x: A" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [card_Diff1_less, less_imp_le])));
qed "card_Diff1_le";

Goal "[| finite B; A <= B; card A < card B |] ==> A < B";
by (etac psubsetI 1);
by (Blast_tac 1);
qed "card_psubset";

(*** Cardinality of image ***)

Goal "finite A ==> card (f ` A) <= card A";
by (etac finite_induct 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [le_SucI, finite_imageI, 
				      card_insert_if]) 1);
qed "card_image_le";

Goal "finite(A) ==> inj_on f A --> card (f ` A) = card A";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by Safe_tac;
by (rewtac inj_on_def);
by (Blast_tac 1);
by (stac card_insert_disjoint 1);
by (etac finite_imageI 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed_spec_mp "card_image";

Goal "[| finite A; f`A <= A; inj_on f A |] ==> f`A = A";
by (asm_simp_tac (simpset() addsimps [card_seteq, card_image]) 1);
qed "endo_inj_surj";

(*** Cardinality of the Powerset ***)

Goal "finite A ==> card (Pow A) = Suc (Suc 0) ^ card A";  (* FIXME numeral 2 (!?) *)
by (etac finite_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Pow_insert])));
by (stac card_Un_disjoint 1);
by (EVERY (map (blast_tac (claset() addIs [finite_imageI])) [3,2,1]));
by (subgoal_tac "inj_on (insert x) (Pow F)" 1);
by (asm_simp_tac (simpset() addsimps [card_image, Pow_insert]) 1);
by (rewtac inj_on_def);
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "card_Pow";


(*Relates to equivalence classes.   Based on a theorem of F. Kammueller's.
  The "finite C" premise is redundant*)
Goal "finite C ==> finite (Union C) --> \
\          (ALL c : C. k dvd card c) -->  \
\          (ALL c1: C. ALL c2: C. c1 ~= c2 --> c1 Int c2 = {}) \
\          --> k dvd card(Union C)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (stac card_Un_disjoint 1);
by (ALLGOALS
    (asm_full_simp_tac (simpset()
			 addsimps [dvd_add, disjoint_eq_subset_Compl])));
by (thin_tac "ALL c:F. ?PP(c)" 1);
by (thin_tac "ALL c:F. ?PP(c) & ?QQ(c)" 1);
by (Clarify_tac 1);
by (ball_tac 1);
by (Blast_tac 1);
qed_spec_mp "dvd_partition";


(*** foldSet ***)

bind_thm ("empty_foldSetE", foldSet.mk_cases "({}, x) : foldSet f e");

AddSEs [empty_foldSetE];
AddIs foldSet.intrs;

Goal "[| (A-{x},y) : foldSet f e;  x: A |] ==> (A, f x y) : foldSet f e";
by (etac (insert_Diff RS subst) 1 THEN resolve_tac foldSet.intrs 1);
by Auto_tac;
qed "Diff1_foldSet";

Goal "(A, x) : foldSet f e ==> finite(A)";
by (eresolve_tac [foldSet.induct] 1);
by Auto_tac;
qed "foldSet_imp_finite";

Addsimps [foldSet_imp_finite];


Goal "finite(A) ==> EX x. (A, x) : foldSet f e";
by (etac finite_induct 1);
by Auto_tac;
qed "finite_imp_foldSet";


Open_locale "LC"; 

val f_lcomm = thm "lcomm";


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
by (rename_tac "Aa xa ya Ab xb yb" 1 THEN case_tac "xa=xb" 1);
 by (subgoal_tac "Aa = Ab" 1);
 by (blast_tac (claset() addSEs [equalityE]) 2);
 by (Blast_tac 1);
(*case xa ~= xb*)
by (subgoal_tac "Aa-{xb} = Ab-{xa} & xb : Aa & xa : Ab" 1);
 by (blast_tac (claset() addSEs [equalityE]) 2);
by (Clarify_tac 1);
by (subgoal_tac "Aa = insert xb Ab - {xa}" 1);
 by (Blast_tac 2);
(** LEVEL 20 **)
by (subgoal_tac "card Aa <= card Ab" 1);
 by (rtac (Suc_le_mono RS subst) 2);
 by (asm_simp_tac (simpset() addsimps [card_Suc_Diff1]) 2);
by (res_inst_tac [("A1", "Aa-{xb}"), ("f1","f")] 
    (finite_imp_foldSet RS exE) 1);
by (blast_tac (claset() addIs [foldSet_imp_finite, finite_Diff]) 1);
by (ftac Diff1_foldSet 1 THEN assume_tac 1);
by (subgoal_tac "ya = f xb x" 1);
 by (blast_tac (claset() delrules [equalityCE]) 2);
by (subgoal_tac "(Ab - {xa}, x) : foldSet f e" 1);
 by (Asm_full_simp_tac 2);
by (subgoal_tac "yb = f xa x" 1);
 by (blast_tac (claset() delrules [equalityCE]
			addDs [Diff1_foldSet]) 2);
by (asm_simp_tac (simpset() addsimps [f_lcomm]) 1);
val lemma = result();


Goal "[| (A, x) : foldSet f e;  (A, y) : foldSet f e |] ==> y=x";
by (blast_tac (claset() addIs [ObjectLogic.rulify lemma]) 1);
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
by (rtac the_equality 1);
by (auto_tac (claset() addIs [finite_imp_foldSet],
	      simpset() addcongs [conj_cong]
		        addsimps [symmetric fold_def,
				  fold_equality]));
qed "fold_insert";

Goal "finite A ==> ALL e. f x (fold f e A) = fold f (f x e) A";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [f_lcomm, fold_insert]) 1);
qed_spec_mp "fold_commute";

Goal "[| finite A; finite B |] \
\     ==> fold f (fold f e B) A  =  fold f (fold f e (A Int B)) (A Un B)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [fold_insert, fold_commute, 
	                              Int_insert_left, insert_absorb]) 1);
qed "fold_nest_Un_Int";

Goal "[| finite A; finite B; A Int B = {} |] \
\     ==> fold f e (A Un B)  =  fold f (fold f e B) A";
by (asm_simp_tac (simpset() addsimps [fold_nest_Un_Int]) 1);
qed "fold_nest_Un_disjoint";

(* Delete rules to do with foldSet relation: obsolete *)
Delsimps [foldSet_imp_finite];
Delrules [empty_foldSetE];
Delrules foldSet.intrs;

Close_locale "LC";

Open_locale "ACe"; 

(*We enter a more restrictive framework, with f :: ['a,'a] => 'a
    instead of ['b,'a] => 'a 
  At present, none of these results are used!*)

val f_ident   = thm "ident";
val f_commute = thm "commute";
val f_assoc   = thm "assoc";


Goal "f x (f y z) = f y (f x z)";
by (rtac (f_commute RS trans) 1);
by (rtac (f_assoc RS trans) 1);
by (rtac (f_commute RS arg_cong) 1);
qed "f_left_commute";

val f_ac = [f_assoc, f_commute, f_left_commute];

Goal "f e x = x";
by (stac f_commute 1);
by (rtac f_ident 1);
qed "f_left_ident";

val f_idents = [f_left_ident, f_ident];

Goal "[| finite A; finite B |] \
\     ==> f (fold f e A) (fold f e B) =  \
\         f (fold f e (A Un B)) (fold f e (A Int B))";
by (etac finite_induct 1);
by (simp_tac (simpset() addsimps f_idents) 1);
by (asm_simp_tac (simpset() addsimps f_ac @ f_idents @
           [export fold_insert,insert_absorb, Int_insert_left]) 1);
qed "fold_Un_Int";

Goal "[| finite A; finite B; A Int B = {} |] \
\     ==> fold f e (A Un B) = f (fold f e A) (fold f e B)";
by (asm_simp_tac (simpset() addsimps fold_Un_Int::f_idents) 1);
qed "fold_Un_disjoint";

Goal
 "[| finite A; finite B |] ==> A Int B = {} --> \
\      fold (f o g) e (A Un B) = f (fold (f o g) e A) (fold (f o g) e B)";
by (etac finite_induct 1);
by (simp_tac (simpset() addsimps f_idents) 1);
by (asm_full_simp_tac (simpset() addsimps f_ac @ f_idents @
           [export fold_insert,insert_absorb, Int_insert_left]) 1);
qed "fold_Un_disjoint2";

Close_locale "ACe";


(*** setsum: generalized summation over a set ***)

Goalw [setsum_def] "setsum f {} = 0";
by (Simp_tac 1);
qed "setsum_empty";
Addsimps [setsum_empty];

Goalw [setsum_def]
 "!!f. [| finite F; a ~: F |] ==> \
\      setsum f (insert a F) = f a + setsum f F";
by (asm_simp_tac (simpset() addsimps [export fold_insert,
				      thm "plus_ac0_left_commute"]) 1);
qed "setsum_insert";
Addsimps [setsum_insert];

Goal "setsum (%i. 0) A = 0";
by (case_tac "finite A" 1);
 by (asm_simp_tac (simpset() addsimps [setsum_def]) 2); 
by (etac finite_induct 1);
by Auto_tac;
qed "setsum_0";

Goal "finite F ==> (setsum f F = 0) = (ALL a:F. f a = (0::nat))";
by (etac finite_induct 1);
by Auto_tac;
qed "setsum_eq_0_iff";
Addsimps [setsum_eq_0_iff];

Goal "setsum f A = Suc n ==> EX a:A. 0 < f a";
by (case_tac "finite A" 1);
 by (asm_full_simp_tac (simpset() addsimps [setsum_def]) 2); 
by (etac rev_mp 1);
by (etac finite_induct 1);
by Auto_tac;
qed "setsum_SucD";

(*Could allow many "card" proofs to be simplified*)
Goal "finite A ==> card A = setsum (%x. 1) A";
by (etac finite_induct 1);
by Auto_tac;
qed "card_eq_setsum";

(*The reversed orientation looks more natural, but LOOPS as a simprule!*)
Goal "!!g. [| finite A; finite B |] \
\     ==> setsum g (A Un B) + setsum g (A Int B) = setsum g A + setsum g B";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps (thms "plus_ac0") @ 
                                          [Int_insert_left, insert_absorb]) 1);
qed "setsum_Un_Int";

Goal "[| finite A; finite B; A Int B = {} |] \
\     ==> setsum g (A Un B) = setsum g A + setsum g B";
by (stac (setsum_Un_Int RS sym) 1);
by Auto_tac;
qed "setsum_Un_disjoint";

Goal "!!f::'a=>'b::plus_ac0. finite I \
\     ==> (ALL i:I. finite (A i)) --> \
\         (ALL i:I. ALL j:I. i~=j --> A i Int A j = {}) --> \
\         setsum f (UNION I A) = setsum (%i. setsum f (A i)) I"; 
by (etac finite_induct 1);
 by (Simp_tac 1);
by (Clarify_tac 1); 
by (subgoal_tac "ALL i:F. x ~= i" 1);
 by (Blast_tac 2); 
by (subgoal_tac "A x Int UNION F A = {}" 1);
 by (Blast_tac 2); 
by (asm_simp_tac (simpset() addsimps [setsum_Un_disjoint]) 1);
qed_spec_mp "setsum_UN_disjoint";

Goal "setsum (%x. f x + g x) A = (setsum f A + setsum g A)";
by (case_tac "finite A" 1);
 by (asm_full_simp_tac (simpset() addsimps [setsum_def]) 2); 
by (etac finite_induct 1);
by Auto_tac;
by (simp_tac (simpset() addsimps (thms "plus_ac0")) 1);
qed "setsum_addf";

(** For the natural numbers, we have subtraction **)

Goal "[| finite A; finite B |] \
\     ==> (setsum f (A Un B) :: nat) = \
\         setsum f A + setsum f B - setsum f (A Int B)";
by (stac (setsum_Un_Int RS sym) 1);
by Auto_tac;
qed "setsum_Un";

Goal "(setsum f (A-{a}) :: nat) = \
\     (if a:A then setsum f A - f a else setsum f A)";
by (case_tac "finite A" 1);
 by (asm_full_simp_tac (simpset() addsimps [setsum_def]) 2); 
by (etac finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [insert_Diff_if]));
by (dres_inst_tac [("a","a")] mk_disjoint_insert 1);
by Auto_tac;
qed_spec_mp "setsum_diff1";

val prems = Goal
    "[| A = B; !!x. x:B ==> f x = g x|] \
\    ==> setsum f A = setsum g B";
by (case_tac "finite B" 1);
 by (asm_simp_tac (simpset() addsimps [setsum_def]@prems) 2); 
by (simp_tac (simpset() addsimps prems) 1);
by (subgoal_tac 
    "ALL C. C <= B --> (ALL x:C. f x = g x) --> setsum f C = setsum g C" 1);
 by (asm_simp_tac (simpset() addsimps prems) 1); 
by (etac finite_induct 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps subset_insert_iff::prems) 1); 
by (Clarify_tac 1); 
by (subgoal_tac "finite C" 1);
 by (blast_tac (claset() addDs [rotate_prems 1 finite_subset]) 2); 
by (subgoal_tac "C = insert x (C-{x})" 1); 
 by (Blast_tac 2); 
by (etac ssubst 1); 
by (dtac spec 1); 
by (mp_tac 1);
by (asm_full_simp_tac (simpset() addsimps Ball_def::prems) 1); 
qed "setsum_cong";


(*** Basic theorem about "choose".  By Florian Kammueller, tidied by LCP ***)

Goal "finite A ==> card {B. B <= A & card B = 0} = 1";
by (asm_simp_tac (simpset() addcongs [conj_cong]
	 	            addsimps [finite_subset RS card_0_eq]) 1);
by (simp_tac (simpset() addcongs [rev_conj_cong]) 1);
qed "card_s_0_eq_empty";

Goal "[| finite M; x ~: M |] \
\  ==> {s. s <= insert x M & card(s) = Suc k} \
\      = {s. s <= M & card(s) = Suc k} Un \
\        {s. EX t. t <= M & card(t) = k & s = insert x t}";
by Safe_tac;
by (auto_tac (claset() addIs [finite_subset RS card_insert_disjoint], 
	      simpset()));
by (dres_inst_tac [("x","xa - {x}")] spec 1);
by (subgoal_tac ("x ~: xa") 1);
by Auto_tac;
by (etac rev_mp 1 THEN stac card_Diff_singleton 1);
by (auto_tac (claset() addIs [finite_subset], simpset()));
qed "choose_deconstruct";

Goal "[| finite(A); finite(B);  f`A <= B;  inj_on f A |] \
\     ==> card A <= card B";
by (auto_tac (claset() addIs [card_mono], 
	      simpset() addsimps [card_image RS sym]));
qed "card_inj_on_le";

Goal "[| finite A; finite B; \
\        f`A <= B; inj_on f A; g`B <= A; inj_on g B |] \
\     ==> card(A) = card(B)";
by (auto_tac (claset() addIs [le_anti_sym,card_inj_on_le], simpset()));
qed "card_bij_eq";

Goal "[| finite A; x ~: A |]  \
\     ==> card{B. EX C. C <= A & card(C) = k & B = insert x C} = \
\         card {B. B <= A & card(B) = k}";
by (res_inst_tac [("f", "%s. s - {x}"), ("g","insert x")] card_bij_eq 1);
by (res_inst_tac [("B","Pow(insert x A)")] finite_subset 1);
by (res_inst_tac [("B","Pow(A)")] finite_subset 3);
by (REPEAT(Fast_tac 1));
(* arity *)
by (auto_tac (claset() addSEs [equalityE], simpset() addsimps [inj_on_def]));
by (stac Diff_insert0 1);
by Auto_tac;
qed "constr_bij";

(* Main theorem: combinatorial theorem about number of subsets of a set *)
Goal "(ALL A. finite A --> card {B. B <= A & card B = k} = (card A choose k))";
by (induct_tac "k" 1);
 by (simp_tac (simpset() addsimps [card_s_0_eq_empty]) 1);
(* first 0 case finished *)
(* prepare finite set induction *)
by (rtac allI 1 THEN rtac impI 1);
(* second induction *)
by (etac finite_induct 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addcongs [conj_cong] 
                     addsimps [card_s_0_eq_empty, choose_deconstruct])));
by (stac card_Un_disjoint 1);
   by (force_tac (claset(), simpset() addsimps [constr_bij]) 4);
  by (Force_tac 3);
 by (blast_tac (claset() addIs [finite_Pow_iff RS iffD2, 
			 inst "B" "Pow (insert ?x ?F)" finite_subset]) 2);
by (blast_tac (claset() addIs [finite_Pow_iff RS iffD2 
			       RSN (2, finite_subset)]) 1);
qed "n_sub_lemma";

Goal "finite A ==> card {B. B <= A & card(B) = k} = ((card A) choose k)";
by (asm_simp_tac (simpset() addsimps [n_sub_lemma]) 1);
qed "n_subsets";
