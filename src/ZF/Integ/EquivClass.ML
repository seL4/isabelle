(*  Title:      ZF/EquivClass.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Equivalence relations in Zermelo-Fraenkel Set Theory 
*)

(*** Suppes, Theorem 70: r is an equiv relation iff converse(r) O r = r ***)

(** first half: equiv(A,r) ==> converse(r) O r = r **)

Goalw [trans_def,sym_def]
    "[| sym(r); trans(r) |] ==> converse(r) O r <= r";
by (Blast_tac 1);
qed "sym_trans_comp_subset";

Goalw [refl_def]
    "[| refl(A,r); r <= A*A |] ==> r <= converse(r) O r";
by (Blast_tac 1);
qed "refl_comp_subset";

Goalw [equiv_def]
    "equiv(A,r) ==> converse(r) O r = r";
by (blast_tac (subset_cs addSIs [sym_trans_comp_subset, refl_comp_subset]) 1);
qed "equiv_comp_eq";

(*second half*)
Goalw [equiv_def,refl_def,sym_def,trans_def]
    "[| converse(r) O r = r;  domain(r) = A |] ==> equiv(A,r)";
by (etac equalityE 1);
by (subgoal_tac "ALL x y. <x,y> : r --> <y,x> : r" 1);
by (ALLGOALS Fast_tac);
qed "comp_equivI";

(** Equivalence classes **)

(*Lemma for the next result*)
Goalw [trans_def,sym_def]
    "[| sym(r);  trans(r);  <a,b>: r |] ==> r``{a} <= r``{b}";
by (Blast_tac 1);
qed "equiv_class_subset";

Goalw [equiv_def]
    "[| equiv(A,r);  <a,b>: r |] ==> r``{a} = r``{b}";
by (safe_tac (subset_cs addSIs [equalityI, equiv_class_subset]));
by (rewtac sym_def);
by (Blast_tac 1);
qed "equiv_class_eq";

Goalw [equiv_def,refl_def]
    "[| equiv(A,r);  a: A |] ==> a: r``{a}";
by (Blast_tac 1);
qed "equiv_class_self";

(*Lemma for the next result*)
Goalw [equiv_def,refl_def]
    "[| equiv(A,r);  r``{b} <= r``{a};  b: A |] ==> <a,b>: r";
by (Blast_tac 1);
qed "subset_equiv_class";

Goal "[| r``{a} = r``{b};  equiv(A,r);  b: A |] ==> <a,b>: r";
by (REPEAT (ares_tac[equalityD2, subset_equiv_class] 1));
qed "eq_equiv_class";

(*thus r``{a} = r``{b} as well*)
Goalw [equiv_def,trans_def,sym_def]
    "[| equiv(A,r);  x: (r``{a} Int r``{b}) |] ==> <a,b>: r";
by (Blast_tac 1);
qed "equiv_class_nondisjoint";

Goalw [equiv_def] "equiv(A,r) ==> r <= A*A";
by (safe_tac subset_cs);
qed "equiv_type";

Goal "equiv(A,r) ==> <x,y>: r <-> r``{x} = r``{y} & x:A & y:A";
by (blast_tac (claset() addIs [eq_equiv_class, equiv_class_eq]
                      addDs [equiv_type]) 1);
qed "equiv_class_eq_iff";

Goal "[| equiv(A,r);  x: A;  y: A |] ==> r``{x} = r``{y} <-> <x,y>: r";
by (blast_tac (claset() addIs [eq_equiv_class, equiv_class_eq]
                      addDs [equiv_type]) 1);
qed "eq_equiv_class_iff";

(*** Quotients ***)

(** Introduction/elimination rules -- needed? **)

Goalw [quotient_def] "x:A ==> r``{x}: A//r";
by (etac RepFunI 1);
qed "quotientI";
AddTCs [quotientI];

val major::prems = Goalw [quotient_def]
    "[| X: A//r;  !!x. [| X = r``{x};  x:A |] ==> P |]   \
\    ==> P";
by (rtac (major RS RepFunE) 1);
by (eresolve_tac prems 1);
by (assume_tac 1);
qed "quotientE";

Goalw [equiv_def,refl_def,quotient_def]
    "equiv(A,r) ==> Union(A//r) = A";
by (Blast_tac 1);
qed "Union_quotient";

Goalw [quotient_def]
    "[| equiv(A,r);  X: A//r;  Y: A//r |] ==> X=Y | (X Int Y <= 0)";
by (safe_tac (claset() addSIs [equiv_class_eq]));
by (assume_tac 1);
by (rewrite_goals_tac [equiv_def,trans_def,sym_def]);
by (Blast_tac 1);
qed "quotient_disj";

(**** Defining unary operations upon equivalence classes ****)

(** These proofs really require as local premises
     equiv(A,r);  congruent(r,b)
**)

(*Conversion rule*)
val prems as [equivA,bcong,_] = goal (the_context ())
    "[| equiv(A,r);  congruent(r,b);  a: A |] ==> (UN x:r``{a}. b(x)) = b(a)";
by (cut_facts_tac prems 1);
by (rtac ([refl RS UN_cong, UN_constant] MRS trans) 1);
by (etac equiv_class_self 2);
by (assume_tac 2);
by (rewrite_goals_tac [equiv_def,sym_def,congruent_def]);
by (Blast_tac 1);
qed "UN_equiv_class";

(*type checking of  UN x:r``{a}. b(x) *)
val prems = Goalw [quotient_def]
    "[| equiv(A,r);  congruent(r,b);  X: A//r;   \
\       !!x.  x : A ==> b(x) : B |]     \
\    ==> (UN x:X. b(x)) : B";
by (cut_facts_tac prems 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps UN_equiv_class::prems) 1);
qed "UN_equiv_class_type";

(*Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be !!y. y:A ==> b(y):B
*)
val prems = Goalw [quotient_def]
    "[| equiv(A,r);   congruent(r,b);  \
\       (UN x:X. b(x))=(UN y:Y. b(y));  X: A//r;  Y: A//r;  \
\       !!x y. [| x:A; y:A; b(x)=b(y) |] ==> <x,y>:r |]         \
\    ==> X=Y";
by (cut_facts_tac prems 1);
by Safe_tac;
by (rtac equiv_class_eq 1);
by (REPEAT (ares_tac prems 1));
by (etac box_equals 1);
by (REPEAT (ares_tac [UN_equiv_class] 1));
qed "UN_equiv_class_inject";


(**** Defining binary operations upon equivalence classes ****)


Goalw [congruent_def,congruent2_def,equiv_def,refl_def]
    "[| equiv(A,r);  congruent2(r,b);  a: A |] ==> congruent(r,b(a))";
by (Blast_tac 1);
qed "congruent2_implies_congruent";

val equivA::prems = goalw (the_context ()) [congruent_def]
    "[| equiv(A,r);  congruent2(r,b);  a: A |] ==> \
\    congruent(r, %x1. UN x2:r``{a}. b(x1,x2))";
by (cut_facts_tac (equivA::prems) 1);
by Safe_tac;
by (rtac (equivA RS equiv_type RS subsetD RS SigmaE2) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [equivA RS UN_equiv_class,
                                     congruent2_implies_congruent]) 1);
by (rewrite_goals_tac [congruent2_def,equiv_def,refl_def]);
by (Blast_tac 1);
qed "congruent2_implies_congruent_UN";

val prems as equivA::_ = goal (the_context ())
    "[| equiv(A,r);  congruent2(r,b);  a1: A;  a2: A |]  \
\    ==> (UN x1:r``{a1}. UN x2:r``{a2}. b(x1,x2)) = b(a1,a2)";
by (cut_facts_tac prems 1);
by (asm_simp_tac (simpset() addsimps [equivA RS UN_equiv_class,
                                     congruent2_implies_congruent,
                                     congruent2_implies_congruent_UN]) 1);
qed "UN_equiv_class2";

(*type checking*)
val prems = Goalw [quotient_def]
    "[| equiv(A,r);  congruent2(r,b);                   \
\       X1: A//r;  X2: A//r;                            \
\       !!x1 x2.  [| x1: A; x2: A |] ==> b(x1,x2) : B   \
\    |] ==> (UN x1:X1. UN x2:X2. b(x1,x2)) : B";
by (cut_facts_tac prems 1);
by Safe_tac;
by (REPEAT (ares_tac (prems@[UN_equiv_class_type,
                             congruent2_implies_congruent_UN,
                             congruent2_implies_congruent, quotientI]) 1));
qed "UN_equiv_class_type2";


(*Suggested by John Harrison -- the two subproofs may be MUCH simpler
  than the direct proof*)
val prems = Goalw [congruent2_def,equiv_def,refl_def]
    "[| equiv(A,r);     \
\       !! y z w. [| w: A;  <y,z> : r |] ==> b(y,w) = b(z,w);      \
\       !! y z w. [| w: A;  <y,z> : r |] ==> b(w,y) = b(w,z)       \
\    |] ==> congruent2(r,b)";
by (cut_facts_tac prems 1);
by Safe_tac;
by (rtac trans 1);
by (REPEAT (ares_tac prems 1
     ORELSE etac (subsetD RS SigmaE2) 1 THEN assume_tac 2 THEN assume_tac 1));
qed "congruent2I";

val [equivA,commute,congt] = Goal
    "[| equiv(A,r);     \
\       !! y z. [| y: A;  z: A |] ==> b(y,z) = b(z,y);        \
\       !! y z w. [| w: A;  <y,z>: r |] ==> b(w,y) = b(w,z)     \
\    |] ==> congruent2(r,b)";
by (resolve_tac [equivA RS congruent2I] 1);
by (rtac (commute RS trans) 1);
by (rtac (commute RS trans RS sym) 3);
by (rtac sym 5);
by (REPEAT (ares_tac [congt] 1
     ORELSE etac (equivA RS equiv_type RS subsetD RS SigmaE2) 1));
qed "congruent2_commuteI";

(*Obsolete?*)
val [equivA,ZinA,congt,commute] = Goalw [quotient_def]
    "[| equiv(A,r);  Z: A//r;  \
\       !!w. [| w: A |] ==> congruent(r, %z. b(w,z));    \
\       !!x y. [| x: A;  y: A |] ==> b(y,x) = b(x,y)    \
\    |] ==> congruent(r, %w. UN z: Z. b(w,z))";
val congt' = rewrite_rule [congruent_def] congt;
by (cut_facts_tac [ZinA] 1);
by (rewtac congruent_def);
by Safe_tac;
by (rtac (equivA RS equiv_type RS subsetD RS SigmaE2) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [commute,
                                     [equivA, congt] MRS UN_equiv_class]) 1);
by (REPEAT (ares_tac [congt' RS spec RS spec RS mp] 1));
qed "congruent_commuteI";
