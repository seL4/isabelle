(*  Title:	BijectionRel.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

Inductive definitions of bijections between two different sets and
	between the same set. 
Theorem for relating the two definitions
*)


(***** bijR *****)

Addsimps [bijR.empty];

Goal "(A,B) : (bijR P) ==> finite A";
by (etac bijR.induct 1);
by Auto_tac;
qed "fin_bijRl";

Goal "(A,B) : (bijR P) ==> finite B";
by (etac bijR.induct 1);
by Auto_tac;
qed "fin_bijRr";

val major::subs::prems = 
Goal "[| finite F;  F <= A; P({}); \
\        !!F a. [| F <= A; a:A; a ~: F;  P(F) |] ==> P(insert a F) |] \
\     ==> P(F)";
by (rtac (subs RS rev_mp) 1);
by (rtac (major RS finite_induct) 1);
by (ALLGOALS (blast_tac (claset() addIs prems)));
val lemma_induct = result();

Goalw [inj_on_def] 
      "[| A <= B; a ~: A ; a : B; inj_on f B |] ==> (f a) ~: f`A";
by Auto_tac;
val lemma = result();

Goal "[| ALL a. a:A --> P a (f a); inj_on f A; finite A; F <= A |] \
\    ==> (F,f`F) : bijR P";
by (res_inst_tac [("F","F"),("A","A")] lemma_induct 1);
by (rtac finite_subset 1);
by Auto_tac;
by (rtac bijR.insert 1);
by (rtac lemma 3);
by Auto_tac;
val lemma = result();

Goal "[| ALL a. a:A --> P a (f a); inj_on f A; finite A |] \
\    ==> (A,f`A) : bijR P";
by (rtac lemma 1);
by Auto_tac;
qed "inj_func_bijR";


(***** bijER *****)

Addsimps [bijER.empty];

Goal "A : bijER P ==> finite A";
by (etac bijER.induct 1);
by Auto_tac;
qed "fin_bijER";

Goal "[| a ~: A; a ~: B; F <= insert a A; F <= insert a B; a : F |] \
\    ==> (EX C. F = insert a C & a ~: C & C <= A & C <= B)";
by (res_inst_tac [("x","F-{a}")] exI 1);
by Auto_tac;
val lemma1 = result();

Goal "[| a ~= b; a ~: A; b ~: B; a : F; b : F; \
\        F <= insert a A; F <= insert b B |] \
\    ==> (EX C. F = insert a (insert b C) & a ~: C & b ~: C & \
\         C <= A & C <= B)";
by (res_inst_tac [("x","F-{a,b}")] exI 1);
by Auto_tac;
val lemma2 = result();

Goalw [uniqP_def] "[| uniqP P; P a b; P c d |] ==> (a=c) = (b=d)";
by Auto_tac;
val lemma_uniq = result();

Goalw [symP_def] "symP P ==> (P a b) = (P b a)";
by Auto_tac;
val lemma_sym = result();

Goalw [bijP_def] 
      "[| uniqP P; b ~: C; P b b; bijP P (insert b C) |] ==> bijP P C";
by Auto_tac;
by (subgoal_tac "b~=a" 1);
by (Clarify_tac 2);
by (asm_full_simp_tac (simpset() addsimps [lemma_uniq]) 1);
by Auto_tac;
val lemma_in1 = result();

Goalw [bijP_def] 
      "[| symP P; uniqP P; a ~: C; b ~: C; a ~= b; P a b; \
\         bijP P (insert a (insert b C)) |] ==> bijP P C";
by Auto_tac;
by (subgoal_tac "aa~=a" 1);
by (Clarify_tac 2);
by (subgoal_tac "aa~=b" 1);
by (Clarify_tac 2);
by (asm_full_simp_tac (simpset() addsimps [lemma_uniq]) 1);
by (subgoal_tac "ba~=a" 1);
by Auto_tac;
by (subgoal_tac "P a aa" 1);
by (asm_simp_tac (simpset() addsimps [lemma_sym]) 2);
by (subgoal_tac "b=aa" 1);
by (rtac iffD1 2);
by (res_inst_tac [("a","a"),("c","a"),("P","P")] lemma_uniq 2);
by Auto_tac;
val lemma_in2 = result();

Goal "[| ALL a b. Q a & P a b --> R b; P a b; Q a |] ==> R b";
by Auto_tac;
val lemma = result();

Goalw [bijP_def] "[| bijP P F; symP P; P a b |] ==> (a:F) = (b:F)";
by (rtac iffI 1);
by (ALLGOALS (etac lemma));
by (ALLGOALS Asm_simp_tac);
by (rtac iffD2 1);
by (res_inst_tac [("P","P")] lemma_sym 1);
by (ALLGOALS Asm_simp_tac);
val lemma_bij = result();

Goal "[| (A,B) : bijR P; uniqP P; symP P |] \
\     ==> (ALL F. (bijP P F) & F<=A & F<=B --> F : bijER P)";
by (etac bijR.induct 1);
by (Simp_tac 1);
by (case_tac "a=b" 1);
by (Clarify_tac 1);
by (case_tac "b:F" 1);
by (rotate_tac ~1 2);
by (asm_full_simp_tac (simpset() addsimps [subset_insert]) 2);
by (cut_inst_tac [("F","F"),("a","b"),("A","A"),("B","B")] lemma1 1);
by (Clarify_tac 6);
by (rtac bijER.insert1 6);
by (ALLGOALS Asm_full_simp_tac);
by (subgoal_tac "bijP P C" 1);
by (Asm_full_simp_tac 1);
by (rtac lemma_in1 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (case_tac "a:F" 1);
by (ALLGOALS (case_tac "b:F"));
by (rotate_tac ~2 4);
by (asm_full_simp_tac (simpset() addsimps [subset_insert]) 4);
by (rotate_tac ~2 3);
by (asm_full_simp_tac (simpset() addsimps [subset_insert]) 3);
by (rotate_tac ~2 2);
by (asm_full_simp_tac (simpset() addsimps [subset_insert]) 2);
by (cut_inst_tac [("F","F"),("a","a"),("b","b"),("A","A"),("B","B")] 
                 lemma2 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (rtac bijER.insert2 1);
by (ALLGOALS Asm_simp_tac);
by (subgoal_tac "bijP P C" 1);
by (Asm_full_simp_tac 1);
by (rtac lemma_in2 1);
by (ALLGOALS Asm_simp_tac);
by (subgoal_tac "b:F" 1);
by (rtac iffD1 2);
by (res_inst_tac [("a","a"),("F","F"),("P","P")] lemma_bij 2);
by (ALLGOALS Asm_simp_tac);
by (subgoal_tac "a:F" 2);
by (rtac iffD2 3);
by (res_inst_tac [("b","b"),("F","F"),("P","P")] lemma_bij 3);
by Auto_tac;
val lemma_bijRER = result();

Goal "[| (A,A) : bijR P; (bijP P A); uniqP P; symP P |] ==> A : bijER P";
by (cut_inst_tac [("A","A"),("B","A"),("P","P")] lemma_bijRER 1);
by Auto_tac;
qed "bijR_bijER";




