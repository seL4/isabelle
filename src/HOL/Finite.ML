(*  Title:      HOL/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson & Tobias Nipkow
    Copyright   1995  University of Cambridge & TU Muenchen

Finite sets and their cardinality
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
by (Simp_tac 1);
by (safe_tac (claset() addSDs [subset_insert_iff RS iffD1]));
by (eres_inst_tac [("t","A")] (insert_Diff RS subst) 2);
by (ALLGOALS Asm_simp_tac);
val lemma = result();

Goal "[| A<=B;  finite B |] ==> finite A";
by (dtac lemma 1);
by (Blast_tac 1);
qed "finite_subset";

Goal "finite(F Un G) = (finite F & finite G)";
by (blast_tac (claset() 
	         addIs [read_instantiate [("B", "?X Un ?Y")] finite_subset, 
			finite_UnI]) 1);
qed "finite_Un";
AddIffs[finite_Un];

Goal "finite F ==> finite(F Int G)";
by (blast_tac (claset() addIs [finite_subset]) 1);
qed "finite_Int1";

Goal "finite G ==> finite(F Int G)";
by (blast_tac (claset() addIs [finite_subset]) 1);
qed "finite_Int2";

Addsimps[finite_Int1, finite_Int2];
AddIs[finite_Int1, finite_Int2];


Goal "finite(insert a A) = finite A";
by (stac insert_is_Un 1);
by (simp_tac (HOL_ss addsimps [finite_Un]) 1);
by (Blast_tac 1);
qed "finite_insert";
Addsimps[finite_insert];

(*The image of a finite set is finite *)
Goal  "finite F ==> finite(h``F)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "finite_imageI";

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
by(stac Diff_insert 1);
by (case_tac "a : A-B" 1);
by (rtac (finite_insert RS sym RS trans) 1);
by (stac insert_Diff 1);
by (ALLGOALS Asm_full_simp_tac);
qed "finite_Diff_insert";
AddIffs [finite_Diff_insert];

(* lemma merely for classical reasoner *)
Goal "finite(A-{}) = finite A";
by (Simp_tac 1);
val lemma = result();
AddSIs [lemma RS iffD2];
AddSDs [lemma RS iffD1];

(*Lemma for proving finite_imageD*)
Goal "finite B ==> !A. f``A = B --> inj_on f A --> finite A";
by (etac finite_induct 1);
 by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (subgoal_tac "EX y:A. f y = x & F = f``(A-{y})" 1);
 by (Clarify_tac 1);
 by (full_simp_tac (simpset() addsimps [inj_on_def]) 1);
 by (Blast_tac 1);
by (thin_tac "ALL A. ?PP(A)" 1);
by (forward_tac [[equalityD2, insertI1] MRS subsetD] 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","xa")] bexI 1);
by (ALLGOALS 
    (asm_full_simp_tac (simpset() addsimps [inj_on_image_set_diff])));
val lemma = result();

Goal "[| finite(f``A);  inj_on f A |] ==> finite A";
by (dtac lemma 1);
by (Blast_tac 1);
qed "finite_imageD";

(** The finite UNION of finite sets **)

Goal "finite A ==> (!a:A. finite(B a)) --> finite(UN a:A. B a)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
bind_thm("finite_UnionI", ballI RSN (2, result() RS mp));
Addsimps [finite_UnionI];

(** Sigma of finite sets **)

Goalw [Sigma_def]
 "[| finite A; !a:A. finite(B a) |] ==> finite(SIGMA a:A. B a)";
by (blast_tac (claset() addSIs [finite_UnionI]) 1);
bind_thm("finite_SigmaI", ballI RSN (2,result()));
Addsimps [finite_SigmaI];

(** The powerset of a finite set **)

Goal "finite(Pow A) ==> finite A";
by (subgoal_tac "finite ((%x.{x})``A)" 1);
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
by (subgoal_tac "r^-1 = (%(x,y).(y,x))``r" 1);
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

section "Finite cardinality -- 'card'";

(* Ugly proofs for the traditional definition 

Goal "{f i |i. (P i | i=n)} = insert (f n) {f i|i. P i}";
by (Blast_tac 1);
val Collect_conv_insert = result();

Goalw [card_def] "card {} = 0";
by (rtac Least_equality 1);
by (ALLGOALS Asm_full_simp_tac);
qed "card_empty";
Addsimps [card_empty];

Goal "finite A ==> ? (n::nat) f. A = {f i |i. i<n}";
by (etac finite_induct 1);
 by (res_inst_tac [("x","0")] exI 1);
 by (Simp_tac 1);
by (etac exE 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x","Suc n")] exI 1);
by (res_inst_tac [("x","%i. if i<n then f i else x")] exI 1);
by (asm_simp_tac (simpset() addsimps [Collect_conv_insert, less_Suc_eq]
                          addcongs [rev_conj_cong]) 1);
qed "finite_has_card";

Goal "[| x ~: A; insert x A = {f i|i. i<n} |]  \
\     ==> ? m::nat. m<n & (? g. A = {g i|i. i<m})";
by (exhaust_tac "n" 1);
 by (hyp_subst_tac 1);
 by (Asm_full_simp_tac 1);
by (rename_tac "m" 1);
by (hyp_subst_tac 1);
by (case_tac "? a. a:A" 1);
 by (res_inst_tac [("x","0")] exI 2);
 by (Simp_tac 2);
 by (Blast_tac 2);
by (etac exE 1);
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (rtac exI 1);
by (rtac (refl RS disjI2 RS conjI) 1);
by (etac equalityE 1);
by (asm_full_simp_tac
     (simpset() addsimps [subset_insert,Collect_conv_insert, less_Suc_eq]) 1);
by Safe_tac;
  by (Asm_full_simp_tac 1);
  by (res_inst_tac [("x","%i. if f i = f m then a else f i")] exI 1);
  by (SELECT_GOAL Safe_tac 1);
   by (subgoal_tac "x ~= f m" 1);
    by (Blast_tac 2);
   by (subgoal_tac "? k. f k = x & k<m" 1);
    by (Blast_tac 2);
   by (SELECT_GOAL Safe_tac 1);
   by (res_inst_tac [("x","k")] exI 1);
   by (Asm_simp_tac 1);
  by (Simp_tac 1);
  by (Blast_tac 1);
 by (dtac sym 1);
 by (rotate_tac ~1 1);
 by (Asm_full_simp_tac 1);
 by (res_inst_tac [("x","%i. if f i = f m then a else f i")] exI 1);
 by (SELECT_GOAL Safe_tac 1);
  by (subgoal_tac "x ~= f m" 1);
   by (Blast_tac 2);
  by (subgoal_tac "? k. f k = x & k<m" 1);
   by (Blast_tac 2);
  by (SELECT_GOAL Safe_tac 1);
  by (res_inst_tac [("x","k")] exI 1);
  by (Asm_simp_tac 1);
 by (Simp_tac 1);
 by (Blast_tac 1);
by (res_inst_tac [("x","%j. if f j = f i then f m else f j")] exI 1);
by (SELECT_GOAL Safe_tac 1);
 by (subgoal_tac "x ~= f i" 1);
  by (Blast_tac 2);
 by (case_tac "x = f m" 1);
  by (res_inst_tac [("x","i")] exI 1);
  by (Asm_simp_tac 1);
 by (subgoal_tac "? k. f k = x & k<m" 1);
  by (Blast_tac 2);
 by (SELECT_GOAL Safe_tac 1);
 by (res_inst_tac [("x","k")] exI 1);
 by (Asm_simp_tac 1);
by (Simp_tac 1);
by (Blast_tac 1);
val lemma = result();

Goal "[| finite A; x ~: A |] ==> \
\ (LEAST n. ? f. insert x A = {f i|i. i<n}) = Suc(LEAST n. ? f. A={f i|i. i<n})";
by (rtac Least_equality 1);
 by (dtac finite_has_card 1);
 by (etac exE 1);
 by (dres_inst_tac [("P","%n.? f. A={f i|i. i<n}")] LeastI 1);
 by (etac exE 1);
 by (res_inst_tac
   [("x","%i. if i<(LEAST n. ? f. A={f i |i. i < n}) then f i else x")] exI 1);
 by (simp_tac
    (simpset() addsimps [Collect_conv_insert, less_Suc_eq] 
              addcongs [rev_conj_cong]) 1);
 by (etac subst 1);
 by (rtac refl 1);
by (rtac notI 1);
by (etac exE 1);
by (dtac lemma 1);
 by (assume_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (dres_inst_tac [("P","%x. ? g. A = {g i |i. i < x}")] Least_le 1);
by (dtac le_less_trans 1 THEN atac 1);
by (asm_full_simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (etac disjE 1);
by (etac less_asym 1 THEN atac 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
val lemma = result();

Goalw [card_def] "[| finite A; x ~: A |] ==> card(insert x A) = Suc(card A)";
by (etac lemma 1);
by (assume_tac 1);
qed "card_insert_disjoint";
Addsimps [card_insert_disjoint];
*)

val cardR_emptyE = cardR.mk_cases "({},n) : cardR";
AddSEs [cardR_emptyE];
val cardR_insertE = cardR.mk_cases "(insert a A,n) : cardR";
AddSIs cardR.intrs;

Goal "[| (A,n) : cardR |] ==> a : A --> (? m. n = Suc m)";
be cardR.induct 1;
 by(Blast_tac 1);
by(Blast_tac 1);
qed "cardR_SucD";

Goal "(A,m): cardR ==> (!n a. m = Suc n --> a:A --> (A-{a},n) : cardR)";
be cardR.induct 1;
 by(Auto_tac);
by(asm_simp_tac (simpset() addsimps [insert_Diff_if]) 1);
by(Auto_tac);
by(forward_tac [cardR_SucD] 1);
by(Blast_tac 1);
val lemma = result();

Goal "[| (insert a A, Suc m) : cardR; a ~: A |] ==> (A,m) : cardR";
bd lemma 1;
by(Asm_full_simp_tac 1);
val lemma = result();

Goal "(A,m): cardR ==> (!n. (A,n) : cardR --> n=m)";
be cardR.induct 1;
 by(safe_tac (claset() addSEs [cardR_insertE]));
by(rename_tac "B b m" 1);
by(case_tac "a = b" 1);
 by(subgoal_tac "A = B" 1);
  by(blast_tac (claset() addEs [equalityE]) 2);
 by(Blast_tac 1);
by(subgoal_tac "? C. A = insert b C & B = insert a C" 1);
 by(res_inst_tac [("x","A Int B")] exI 2);
 by(blast_tac (claset() addEs [equalityE]) 2);
by(forw_inst_tac [("A","B")] cardR_SucD 1);
by(blast_tac (claset() addDs [lemma]) 1);
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

Goal "x ~: A ==> \
\     ((insert x A, n) : cardR) =  \
\     (EX m. (A, m) : cardR & n = Suc m)";
by Auto_tac;
by (res_inst_tac [("A1", "A")] (finite_imp_cardR RS exE) 1);
by (force_tac (claset() addDs [cardR_imp_finite], simpset()) 1);
by (blast_tac (claset() addIs [cardR_determ]) 1);
val lemma = result();

Goalw [card_def]
     "[| finite A; x ~: A |] ==> card (insert x A) = Suc(card A)";
by (asm_simp_tac (simpset() addsimps [lemma]) 1);
by (rtac select_equality 1);
by (auto_tac (claset() addIs [finite_imp_cardR],
	      simpset() addcongs [conj_cong]
		        addsimps [symmetric card_def,
				  card_equality]));
qed "card_insert_disjoint";
Addsimps [card_insert_disjoint];

(* Delete rules to do with cardR relation: obsolete *)
Delrules [cardR_emptyE];
Delrules cardR.intrs;

Goal "finite A ==> card(insert x A) = (if x:A then card A else Suc(card(A)))";
by (asm_simp_tac (simpset() addsimps [insert_absorb]) 1);
qed "card_insert_if";

Goal "[| finite A; x: A |] ==> Suc(card(A-{x})) = card A";
by (res_inst_tac [("t", "A")] (insert_Diff RS subst) 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
qed "card_Suc_Diff1";

Goal "finite A ==> card(insert x A) = Suc(card(A-{x}))";
by (asm_simp_tac (simpset() addsimps [card_insert_if,card_Suc_Diff1]) 1);
qed "card_insert";

Goal "finite A ==> card A <= card (insert x A)";
by (asm_simp_tac (simpset() addsimps [card_insert_if]) 1);
qed "card_insert_le";

Goal  "finite A ==> !B. B <= A --> card(B) <= card(A)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "x:B" 1);
 by (dres_inst_tac [("A","B")] mk_disjoint_insert 1);
 by (asm_full_simp_tac (simpset() addsimps [subset_insert_iff]) 2);
by (fast_tac (claset() addss
	      (simpset() addsimps [subset_insert_iff, finite_subset]
			 delsimps [insert_subset])) 1);
qed_spec_mp "card_mono";


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

Goal "finite A ==> card(A-{x}) <= card A";
by (case_tac "x: A" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [card_Diff1_less, less_imp_le])));
qed "card_Diff1_le";

Goalw [psubset_def] "finite B ==> !A. A < B --> card(A) < card(B)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "x:A" 1);
(*1*)
by (dres_inst_tac [("A","A")]mk_disjoint_insert 1);
by (Clarify_tac 1);
by (rotate_tac ~3 1);
by (asm_full_simp_tac (simpset() addsimps [finite_subset]) 1);
by (Blast_tac 1);
(*2*)
by (eres_inst_tac [("P","?a<?b")] notE 1);
by (asm_full_simp_tac (simpset() addsimps [subset_insert_iff]) 1);
by (case_tac "A=F" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "psubset_card" ;

Goal "[| finite B; A <= B; card A = card B |] ==> A = B";
by (case_tac "A < B" 1);
by ((dtac psubset_card 1) THEN (atac 1));
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [psubset_eq])));
qed "card_seteq";

Goal "[| finite B; A <= B; card A < card B |] ==> A < B";
by (etac psubsetI 1);
by (Blast_tac 1);
qed "card_psubset";

(*** Cardinality of image ***)

Goal "finite A ==> card (f `` A) <= card A";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [finite_imageI,card_insert_if]) 1);
qed "card_image_le";

Goal "finite(A) ==> inj_on f A --> card (f `` A) = card A";
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

Goal "[| finite A; f``A <= A; inj_on f A |] ==> f``A = A";
by (REPEAT (ares_tac [card_seteq,card_image] 1));
qed "endo_inj_surj";

(*** Cardinality of the Powerset ***)

Goal "finite A ==> card (Pow A) = 2 ^ card A";
by (etac finite_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Pow_insert])));
by (stac card_Un_disjoint 1);
by (EVERY (map (blast_tac (claset() addIs [finite_imageI])) [3,2,1]));
by (subgoal_tac "inj_on (insert x) (Pow F)" 1);
by (asm_simp_tac (simpset() addsimps [card_image, Pow_insert]) 1);
by (rewtac inj_on_def);
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "card_Pow";
Addsimps [card_Pow];


(*Relates to equivalence classes.   Based on a theorem of F. Kammueller's.
  The "finite C" premise is redundant*)
Goal "finite C ==> finite (Union C) --> \
\          (! c : C. k dvd card c) -->  \
\          (! c1: C. ! c2: C. c1 ~= c2 --> c1 Int c2 = {}) \
\          --> k dvd card(Union C)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (stac card_Un_disjoint 1);
by (ALLGOALS
    (asm_full_simp_tac (simpset()
			 addsimps [dvd_add, disjoint_eq_subset_Compl])));
by (thin_tac "!c:F. ?PP(c)" 1);
by (thin_tac "!c:F. ?PP(c) & ?QQ(c)" 1);
by (Clarify_tac 1);
by (ball_tac 1);
by (Blast_tac 1);
qed_spec_mp "dvd_partition";


(*** foldSet ***)

val empty_foldSetE = foldSet.mk_cases "({}, x) : foldSet f e";

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
 by (asm_simp_tac (simpset() addsimps [card_Suc_Diff1]) 2);
by (res_inst_tac [("A1", "Aa-{xb}"), ("f1","f")] 
    (finite_imp_foldSet RS exE) 1);
by (blast_tac (claset() addIs [foldSet_imp_finite, finite_Diff]) 1);
by (forward_tac [Diff1_foldSet] 1 THEN assume_tac 1);
by (subgoal_tac "ya = f xb x" 1);
 by (Blast_tac 2);
by (subgoal_tac "(Ab - {xa}, x) : foldSet f e" 1);
 by (Asm_full_simp_tac 2);
by (subgoal_tac "yb = f xa x" 1);
 by (blast_tac (claset() addDs [Diff1_foldSet]) 2);
by (asm_simp_tac (simpset() addsimps [f_lcomm]) 1);
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

(* Delete rules to do with foldSet relation: obsolete *)
Delsimps [foldSet_imp_finite];
Delrules [empty_foldSetE];
Delrules foldSet.intrs;

Close_locale "LC";

Open_locale "ACe"; 

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
\ fold (f o g) e (A Un B) = f (fold (f o g) e A) (fold (f o g) e B)";
by (etac finite_induct 1);
by (simp_tac (simpset() addsimps f_idents) 1);
by (asm_full_simp_tac (simpset() addsimps f_ac @ f_idents @
           [export fold_insert,insert_absorb, Int_insert_left]) 1);
qed "fold_Un_disjoint2";

Close_locale "ACe";

Delrules ([empty_foldSetE] @ foldSet.intrs);
Delsimps [foldSet_imp_finite];

(*** setsum ***)

Goalw [setsum_def] "setsum f {} = 0";
by(Simp_tac 1);
qed "setsum_empty";
Addsimps [setsum_empty];

Goalw [setsum_def]
 "[| finite F; a ~: F |] ==> setsum f (insert a F) = f(a) + setsum f F";
by(asm_simp_tac (simpset() addsimps [export fold_insert]) 1);
qed "setsum_insert";
Addsimps [setsum_insert];

Goalw [setsum_def]
 "[| finite A; finite B; A Int B = {} |] ==> \
\ setsum f (A Un B) = setsum f A + setsum f B";
by(asm_simp_tac (simpset() addsimps [export fold_Un_disjoint2]) 1);
qed_spec_mp "setsum_disj_Un";

Goal "[| finite F |] ==> \
\     setsum f (F-{a}) = (if a:F then setsum f F - f a else setsum f F)";
be finite_induct 1;
by(auto_tac (claset(), simpset() addsimps [insert_Diff_if]));
by(dres_inst_tac [("a","a")] mk_disjoint_insert 1);
by(Auto_tac);
qed_spec_mp "setsum_diff1";
