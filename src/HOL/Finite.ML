(*  Title:      HOL/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson & Tobias Nipkow
    Copyright   1995  University of Cambridge & TU Muenchen

Finite sets and their cardinality
*)

open Finite;

(*** Fin ***)

goalw Finite.thy Fin.defs "!!A B. A<=B ==> Fin(A) <= Fin(B)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "Fin_mono";

goalw Finite.thy Fin.defs "Fin(A) <= Pow(A)";
by (fast_tac (set_cs addSIs [lfp_lowerbound]) 1);
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
by (safe_tac (set_cs addSDs [subset_insert_iff RS iffD1]));
by (eres_inst_tac [("t","C")] (insert_Diff RS subst) 2);
by (ALLGOALS Asm_simp_tac);
qed "Fin_subset";

goal Finite.thy "(F Un G : Fin(A)) = (F: Fin(A) & G: Fin(A))";
by(fast_tac (set_cs addIs [Fin_UnI] addDs
                [Un_upper1 RS Fin_subset, Un_upper2 RS Fin_subset]) 1);
qed "subset_Fin";
Addsimps[subset_Fin];

goal Finite.thy "(insert a A : Fin M) = (a:M & A : Fin M)";
by(stac insert_is_Un 1);
by(Simp_tac 1);
by(fast_tac (set_cs addSIs Fin.intrs addDs [FinD]) 1);
qed "insert_Fin";
Addsimps[insert_Fin];

(*The image of a finite set is finite*)
val major::_ = goal Finite.thy
    "F: Fin(A) ==> h``F : Fin(h``A)";
by (rtac (major RS Fin_induct) 1);
by (Simp_tac 1);
by (asm_simp_tac
    (!simpset addsimps [image_eqI RS Fin.insertI, image_insert]) 1);
qed "Fin_imageI";

val major::prems = goal Finite.thy 
    "[| c: Fin(A);  b: Fin(A);                                  \
\       P(b);                                                   \
\       !!(x::'a) y. [| x:A; y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> c<=b --> P(b-c)";
by (rtac (major RS Fin_induct) 1);
by (rtac (Diff_insert RS ssubst) 2);
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


(*** finite ***)

val major::prems = goalw Finite.thy [finite_def]
    "[| finite F;  P({}); \
\       !!F x. [| finite F;  x~:F;  P(F) |] ==> P(insert x F) \
\    |] ==> P(F)";
by (rtac (major RS Fin_induct) 1);
by (REPEAT (ares_tac prems 1));
qed "finite_induct";


goalw Finite.thy [finite_def] "finite {}";
by(Simp_tac 1);
qed "finite_emptyI";
Addsimps [finite_emptyI];

goalw Finite.thy [finite_def] "!!A. finite A ==> finite(insert a A)";
by(Asm_simp_tac 1);
qed "finite_insertI";

(*The union of two finite sets is finite*)
goalw Finite.thy [finite_def]
    "!!F. [| finite F;  finite G |] ==> finite(F Un G)";
by(Asm_simp_tac 1);
qed "finite_UnI";

goalw Finite.thy [finite_def] "!!A. [| A<=B;  finite B |] ==> finite A";
be Fin_subset 1;
ba 1;
qed "finite_subset";

goalw Finite.thy [finite_def] "finite(F Un G) = (finite F & finite G)";
by(Simp_tac 1);
qed "subset_finite";
Addsimps[subset_finite];

goalw Finite.thy [finite_def] "finite(insert a A) = finite(A)";
by(Simp_tac 1);
qed "insert_finite";
Addsimps[insert_finite];

goal Finite.thy "!!A. finite(A) ==> finite(A-B)";
be finite_induct 1;
by(Simp_tac 1);
by(asm_simp_tac (!simpset addsimps [insert_Diff_if]
                          setloop split_tac[expand_if]) 1);
qed "finite_Diff";
Addsimps [finite_Diff];

(*The image of a finite set is finite*)
goal Finite.thy "!!F. finite F ==> finite(h``F)";
be finite_induct 1;
by(ALLGOALS Asm_simp_tac);
qed "finite_imageI";

val major::prems = goalw Finite.thy [finite_def]
    "[| finite A;                                       \
\       P(A);                                           \
\       !!a A. [| finite A;  a:A;  P(A) |] ==> P(A-{a}) \
\    |] ==> P({})";
by (rtac (major RS Fin_empty_induct) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
qed "finite_empty_induct";


(*** Cardinality ***)

goal Set.thy "{f i |i. P i | i=n} = insert (f n) {f i|i. P i}";
by(fast_tac eq_cs 1);
val Collect_conv_insert = result();

goalw Finite.thy [card_def] "card {} = 0";
br Least_equality 1;
by(ALLGOALS Asm_full_simp_tac);
qed "card_empty";
Addsimps [card_empty];

(*Addsimps [Collect_conv_insert];*)

val [major] = goal Finite.thy
  "finite A ==> ? (n::nat) f. A = {f i |i. i<n}";
br (major RS finite_induct) 1;
 by(res_inst_tac [("x","0")] exI 1);
 by(Simp_tac 1);
be exE 1;
be exE 1;
by(hyp_subst_tac 1);
by(res_inst_tac [("x","Suc n")] exI 1);
by(res_inst_tac [("x","%i. if i<n then f i else x")] exI 1);
by(asm_simp_tac (!simpset addsimps [Collect_conv_insert]
                          addcongs [Collect_cong1]) 1);
qed "finite_has_card";

goal Finite.thy
  "!!A.[| x ~: A; insert x A = {f i|i.i<n} |] ==> \
\  ? m::nat. m<n & (? g. A = {g i|i.i<m})";
by(res_inst_tac [("n","n")] natE 1);
 by(hyp_subst_tac 1);
 by(Asm_full_simp_tac 1);
by(rename_tac "m" 1);
by(hyp_subst_tac 1);
by(case_tac "? a. a:A" 1);
 by(res_inst_tac [("x","0")] exI 2);
 by(Simp_tac 2);
 by(fast_tac eq_cs 2);
be exE 1;
by(Simp_tac 1);
br exI 1;
br conjI 1;
 br disjI2 1;
 br refl 1;
be equalityE 1;
by(asm_full_simp_tac
     (!simpset addsimps [subset_insert,Collect_conv_insert]) 1);
by(SELECT_GOAL(safe_tac eq_cs)1);
  by(Asm_full_simp_tac 1);
  by(res_inst_tac [("x","%i. if f i = f m then a else f i")] exI 1);
  by(SELECT_GOAL(safe_tac eq_cs)1);
   by(subgoal_tac "x ~= f m" 1);
    by(fast_tac set_cs 2);
   by(subgoal_tac "? k. f k = x & k<m" 1);
    by(best_tac set_cs 2);
   by(SELECT_GOAL(safe_tac HOL_cs)1);
   by(res_inst_tac [("x","k")] exI 1);
   by(Asm_simp_tac 1);
  by(simp_tac (!simpset setloop (split_tac [expand_if])) 1);
  by(best_tac set_cs 1);
 bd sym 1;
 by(rotate_tac ~1 1);
 by(Asm_full_simp_tac 1);
 by(res_inst_tac [("x","%i. if f i = f m then a else f i")] exI 1);
 by(SELECT_GOAL(safe_tac eq_cs)1);
  by(subgoal_tac "x ~= f m" 1);
   by(fast_tac set_cs 2);
  by(subgoal_tac "? k. f k = x & k<m" 1);
   by(best_tac set_cs 2);
  by(SELECT_GOAL(safe_tac HOL_cs)1);
  by(res_inst_tac [("x","k")] exI 1);
  by(Asm_simp_tac 1);
 by(simp_tac (!simpset setloop (split_tac [expand_if])) 1);
 by(best_tac set_cs 1);
by(res_inst_tac [("x","%j. if f j = f i then f m else f j")] exI 1);
by(SELECT_GOAL(safe_tac eq_cs)1);
 by(subgoal_tac "x ~= f i" 1);
  by(fast_tac set_cs 2);
 by(case_tac "x = f m" 1);
  by(res_inst_tac [("x","i")] exI 1);
  by(Asm_simp_tac 1);
 by(subgoal_tac "? k. f k = x & k<m" 1);
  by(best_tac set_cs 2);
 by(SELECT_GOAL(safe_tac HOL_cs)1);
 by(res_inst_tac [("x","k")] exI 1);
 by(Asm_simp_tac 1);
by(simp_tac (!simpset setloop (split_tac [expand_if])) 1);
by(best_tac set_cs 1);
val lemma = result();

goal Finite.thy "!!A. [| finite A; x ~: A |] ==> \
\ (LEAST n. ? f. insert x A = {f i|i.i<n}) = Suc(LEAST n. ? f. A={f i|i.i<n})";
br Least_equality 1;
 bd finite_has_card 1;
 be exE 1;
 by(dres_inst_tac [("P","%n.? f. A={f i|i.i<n}")] LeastI 1);
 be exE 1;
 by(res_inst_tac
   [("x","%i. if i<(LEAST n. ? f. A={f i |i. i < n}) then f i else x")] exI 1);
 by(simp_tac
    (!simpset addsimps [Collect_conv_insert] addcongs [Collect_cong1]) 1);
 be subst 1;
 br refl 1;
br notI 1;
be exE 1;
bd lemma 1;
 ba 1;
be exE 1;
be conjE 1;
by(dres_inst_tac [("P","%x. ? g. A = {g i |i. i < x}")] Least_le 1);
by(dtac le_less_trans 1 THEN atac 1);
by(Asm_full_simp_tac 1);
be disjE 1;
by(etac less_asym 1 THEN atac 1);
by(hyp_subst_tac 1);
by(Asm_full_simp_tac 1);
val lemma = result();

goalw Finite.thy [card_def]
  "!!A. [| finite A; x ~: A |] ==> card(insert x A) = Suc(card A)";
be lemma 1;
ba 1;
qed "card_insert_disjoint";

val [major] = goal Finite.thy
  "finite A ==> card(insert x A) = Suc(card(A-{x}))";
by(case_tac "x:A" 1);
by(asm_simp_tac (!simpset addsimps [insert_absorb]) 1);
bd mk_disjoint_insert 1;
be exE 1;
by(Asm_simp_tac 1);
br card_insert_disjoint 1;
br (major RSN (2,finite_subset)) 1;
by(fast_tac set_cs 1);
by(fast_tac HOL_cs 1);
by(asm_simp_tac (!simpset addsimps [major RS card_insert_disjoint]) 1);
qed "card_insert";
Addsimps [card_insert];


goal Finite.thy  "!!A. finite A ==> !B. B <= A --> card(B) <= card(A)";
be finite_induct 1;
by(Simp_tac 1);
by(strip_tac 1);
by(case_tac "x:B" 1);
 bd mk_disjoint_insert 1;
 by(SELECT_GOAL(safe_tac HOL_cs)1);
 by(rotate_tac ~1 1);
 by(asm_full_simp_tac (!simpset addsimps [subset_insert_iff,finite_subset]) 1);
by(rotate_tac ~1 1);
by(asm_full_simp_tac (!simpset addsimps [subset_insert_iff,finite_subset]) 1);
qed_spec_mp "card_mono";
