(*  Title:      HOL/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson & Tobias Nipkow
    Copyright   1995  University of Cambridge & TU Muenchen

Finite sets and their cardinality
*)

open Finite;

section "The finite powerset operator -- Fin";

goalw Finite.thy Fin.defs "!!A B. A<=B ==> Fin(A) <= Fin(B)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "Fin_mono";

goalw Finite.thy Fin.defs "Fin(A) <= Pow(A)";
by (fast_tac (!claset addSIs [lfp_lowerbound]) 1);
qed "Fin_subset_Pow";

(* A : Fin(B) ==> A <= B *)
val FinD = Fin_subset_Pow RS subsetD RS PowD;

(*Discharging ~ x:y entails extra work*)
val major::prems = goal Finite.thy 
    "[| F:Fin(A);  P({}); \
\       !!F x. [| x:A;  F:Fin(A);  x~:F;  P(F) |] ==> P(insert x F) \
\    |] ==> P(F)";
by (rtac (major RS Fin.induct) 1);
by (excluded_middle_tac "a:b" 2);
by (etac (insert_absorb RS ssubst) 3 THEN assume_tac 3);   (*backtracking!*)
by (REPEAT (ares_tac prems 1));
qed "Fin_induct";

Addsimps Fin.intrs;

(*The union of two finite sets is finite*)
val major::prems = goal Finite.thy
    "[| F: Fin(A);  G: Fin(A) |] ==> F Un G : Fin(A)";
by (rtac (major RS Fin_induct) 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps (prems @ [Un_insert_left]))));
qed "Fin_UnI";

(*Every subset of a finite set is finite*)
val [subs,fin] = goal Finite.thy "[| A<=B;  B: Fin(M) |] ==> A: Fin(M)";
by (EVERY1 [subgoal_tac "ALL C. C<=B --> C: Fin(M)",
            rtac mp, etac spec,
            rtac subs]);
by (rtac (fin RS Fin_induct) 1);
by (simp_tac (!simpset addsimps [subset_Un_eq]) 1);
by (safe_tac (!claset addSDs [subset_insert_iff RS iffD1]));
by (eres_inst_tac [("t","C")] (insert_Diff RS subst) 2);
by (ALLGOALS Asm_simp_tac);
qed "Fin_subset";

goal Finite.thy "(F Un G : Fin(A)) = (F: Fin(A) & G: Fin(A))";
by (fast_tac (!claset addIs [Fin_UnI] addDs
                [Un_upper1 RS Fin_subset, Un_upper2 RS Fin_subset]) 1);
qed "subset_Fin";
Addsimps[subset_Fin];

goal Finite.thy "(insert a A : Fin M) = (a:M & A : Fin M)";
by (stac insert_is_Un 1);
by (Simp_tac 1);
by (fast_tac (!claset addSIs Fin.intrs addDs [FinD]) 1);
qed "insert_Fin";
Addsimps[insert_Fin];

(*The image of a finite set is finite*)
val major::_ = goal Finite.thy
    "F: Fin(A) ==> h``F : Fin(h``A)";
by (rtac (major RS Fin_induct) 1);
by (Simp_tac 1);
by (asm_simp_tac
    (!simpset addsimps [image_eqI RS Fin.insertI, image_insert]
              delsimps [insert_Fin]) 1);
qed "Fin_imageI";

val major::prems = goal Finite.thy 
    "[| c: Fin(A);  b: Fin(A);                                  \
\       P(b);                                                   \
\       !!(x::'a) y. [| x:A; y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> c<=b --> P(b-c)";
by (rtac (major RS Fin_induct) 1);
by (stac Diff_insert 2);
by (ALLGOALS (asm_simp_tac
                (!simpset addsimps (prems@[Diff_subset RS Fin_subset]))));
val lemma = result();

val prems = goal Finite.thy 
    "[| b: Fin(A);                                              \
\       P(b);                                                   \
\       !!x y. [| x:A; y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> P({})";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (lemma RS mp) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
qed "Fin_empty_induct";


section "The predicate 'finite'";

val major::prems = goalw Finite.thy [finite_def]
    "[| finite F;  P({}); \
\       !!F x. [| finite F;  x~:F;  P(F) |] ==> P(insert x F) \
\    |] ==> P(F)";
by (rtac (major RS Fin_induct) 1);
by (REPEAT (ares_tac prems 1));
qed "finite_induct";


goalw Finite.thy [finite_def] "finite {}";
by (Simp_tac 1);
qed "finite_emptyI";
Addsimps [finite_emptyI];

goalw Finite.thy [finite_def] "!!A. finite A ==> finite(insert a A)";
by (Asm_simp_tac 1);
qed "finite_insertI";

(*The union of two finite sets is finite*)
goalw Finite.thy [finite_def]
    "!!F. [| finite F;  finite G |] ==> finite(F Un G)";
by (Asm_simp_tac 1);
qed "finite_UnI";

goalw Finite.thy [finite_def] "!!A. [| A<=B;  finite B |] ==> finite A";
by (etac Fin_subset 1);
by (assume_tac 1);
qed "finite_subset";

goalw Finite.thy [finite_def] "finite(F Un G) = (finite F & finite G)";
by (Simp_tac 1);
qed "subset_finite";
Addsimps[subset_finite];

goalw Finite.thy [finite_def] "finite(insert a A) = finite(A)";
by (Simp_tac 1);
qed "insert_finite";
Addsimps[insert_finite];

(* finite B ==> finite (B - Ba) *)
bind_thm ("finite_Diff", Diff_subset RS finite_subset);
Addsimps [finite_Diff];

(*The image of a finite set is finite*)
goal Finite.thy "!!F. finite F ==> finite(h``F)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "finite_imageI";

val major::prems = goalw Finite.thy [finite_def]
    "[| finite A;                                       \
\       P(A);                                           \
\       !!a A. [| finite A;  a:A;  P(A) |] ==> P(A-{a}) \
\    |] ==> P({})";
by (rtac (major RS Fin_empty_induct) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
qed "finite_empty_induct";


section "Finite cardinality -- 'card'";

goal Set.thy "{f i |i. P i | i=n} = insert (f n) {f i|i. P i}";
by (Fast_tac 1);
val Collect_conv_insert = result();

goalw Finite.thy [card_def] "card {} = 0";
by (rtac Least_equality 1);
by (ALLGOALS Asm_full_simp_tac);
qed "card_empty";
Addsimps [card_empty];

val [major] = goal Finite.thy
  "finite A ==> ? (n::nat) f. A = {f i |i. i<n}";
by (rtac (major RS finite_induct) 1);
 by (res_inst_tac [("x","0")] exI 1);
 by (Simp_tac 1);
by (etac exE 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x","Suc n")] exI 1);
by (res_inst_tac [("x","%i. if i<n then f i else x")] exI 1);
by (asm_simp_tac (!simpset addsimps [Collect_conv_insert, less_Suc_eq]
                          addcongs [rev_conj_cong]) 1);
qed "finite_has_card";

goal Finite.thy
  "!!A.[| x ~: A; insert x A = {f i|i.i<n} |] ==> \
\  ? m::nat. m<n & (? g. A = {g i|i.i<m})";
by (res_inst_tac [("n","n")] natE 1);
 by (hyp_subst_tac 1);
 by (Asm_full_simp_tac 1);
by (rename_tac "m" 1);
by (hyp_subst_tac 1);
by (case_tac "? a. a:A" 1);
 by (res_inst_tac [("x","0")] exI 2);
 by (Simp_tac 2);
 by (Fast_tac 2);
by (etac exE 1);
by (simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (rtac exI 1);
by (rtac (refl RS disjI2 RS conjI) 1);
by (etac equalityE 1);
by (asm_full_simp_tac
     (!simpset addsimps [subset_insert,Collect_conv_insert, less_Suc_eq]) 1);
by (SELECT_GOAL(safe_tac (!claset))1);
  by (Asm_full_simp_tac 1);
  by (res_inst_tac [("x","%i. if f i = f m then a else f i")] exI 1);
  by (SELECT_GOAL(safe_tac (!claset))1);
   by (subgoal_tac "x ~= f m" 1);
    by (Fast_tac 2);
   by (subgoal_tac "? k. f k = x & k<m" 1);
    by (best_tac (!claset) 2);
   by (SELECT_GOAL(safe_tac (!claset))1);
   by (res_inst_tac [("x","k")] exI 1);
   by (Asm_simp_tac 1);
  by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
  by (best_tac (!claset) 1);
 bd sym 1;
 by (rotate_tac ~1 1);
 by (Asm_full_simp_tac 1);
 by (res_inst_tac [("x","%i. if f i = f m then a else f i")] exI 1);
 by (SELECT_GOAL(safe_tac (!claset))1);
  by (subgoal_tac "x ~= f m" 1);
   by (Fast_tac 2);
  by (subgoal_tac "? k. f k = x & k<m" 1);
   by (best_tac (!claset) 2);
  by (SELECT_GOAL(safe_tac (!claset))1);
  by (res_inst_tac [("x","k")] exI 1);
  by (Asm_simp_tac 1);
 by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
 by (best_tac (!claset) 1);
by (res_inst_tac [("x","%j. if f j = f i then f m else f j")] exI 1);
by (SELECT_GOAL(safe_tac (!claset))1);
 by (subgoal_tac "x ~= f i" 1);
  by (Fast_tac 2);
 by (case_tac "x = f m" 1);
  by (res_inst_tac [("x","i")] exI 1);
  by (Asm_simp_tac 1);
 by (subgoal_tac "? k. f k = x & k<m" 1);
  by (best_tac (!claset) 2);
 by (SELECT_GOAL(safe_tac (!claset))1);
 by (res_inst_tac [("x","k")] exI 1);
 by (Asm_simp_tac 1);
by (simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by (best_tac (!claset) 1);
val lemma = result();

goal Finite.thy "!!A. [| finite A; x ~: A |] ==> \
\ (LEAST n. ? f. insert x A = {f i|i.i<n}) = Suc(LEAST n. ? f. A={f i|i.i<n})";
by (rtac Least_equality 1);
 bd finite_has_card 1;
 be exE 1;
 by (dres_inst_tac [("P","%n.? f. A={f i|i.i<n}")] LeastI 1);
 be exE 1;
 by (res_inst_tac
   [("x","%i. if i<(LEAST n. ? f. A={f i |i. i < n}) then f i else x")] exI 1);
 by (simp_tac
    (!simpset addsimps [Collect_conv_insert, less_Suc_eq] 
              addcongs [rev_conj_cong]) 1);
 be subst 1;
 br refl 1;
by (rtac notI 1);
by (etac exE 1);
by (dtac lemma 1);
 ba 1;
by (etac exE 1);
by (etac conjE 1);
by (dres_inst_tac [("P","%x. ? g. A = {g i |i. i < x}")] Least_le 1);
by (dtac le_less_trans 1 THEN atac 1);
by (asm_full_simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (etac disjE 1);
by (etac less_asym 1 THEN atac 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
val lemma = result();

goalw Finite.thy [card_def]
  "!!A. [| finite A; x ~: A |] ==> card(insert x A) = Suc(card A)";
by (etac lemma 1);
by (assume_tac 1);
qed "card_insert_disjoint";

goal Finite.thy "!!A. [| finite A; x: A |] ==> Suc(card(A-{x})) = card A";
by (res_inst_tac [("t", "A")] (insert_Diff RS subst) 1);
by (assume_tac 1);
by (asm_simp_tac (!simpset addsimps [card_insert_disjoint]) 1);
qed "card_Suc_Diff";

goal Finite.thy "!!A. [| finite A; x: A |] ==> card(A-{x}) < card A";
by (rtac Suc_less_SucD 1);
by (asm_simp_tac (!simpset addsimps [card_Suc_Diff]) 1);
qed "card_Diff";

val [major] = goal Finite.thy
  "finite A ==> card(insert x A) = Suc(card(A-{x}))";
by (case_tac "x:A" 1);
by (asm_simp_tac (!simpset addsimps [insert_absorb]) 1);
by (dtac mk_disjoint_insert 1);
by (etac exE 1);
by (Asm_simp_tac 1);
by (rtac card_insert_disjoint 1);
by (rtac (major RSN (2,finite_subset)) 1);
by (Fast_tac 1);
by (Fast_tac 1);
by (asm_simp_tac (!simpset addsimps [major RS card_insert_disjoint]) 1);
qed "card_insert";
Addsimps [card_insert];


goal Finite.thy  "!!A. finite A ==> !B. B <= A --> card(B) <= card(A)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (strip_tac 1);
by (case_tac "x:B" 1);
 by (dtac mk_disjoint_insert 1);
 by (SELECT_GOAL(safe_tac (!claset))1);
 by (rotate_tac ~1 1);
 by (asm_full_simp_tac (!simpset addsimps [subset_insert_iff,finite_subset]) 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (!simpset addsimps [subset_insert_iff,finite_subset]) 1);
qed_spec_mp "card_mono";
