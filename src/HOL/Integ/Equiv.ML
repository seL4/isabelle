(*  Title: 	Equiv.ML
    ID:         $Id$
    Authors: 	Riccardo Mattolini, Dip. Sistemi e Informatica
        	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994 Universita' di Firenze
    Copyright   1993  University of Cambridge

Equivalence relations in HOL Set Theory 
*)

open Equiv;

(*** Suppes, Theorem 70: r is an equiv relation iff converse(r) O r = r ***)

(** first half: equiv A r ==> converse(r) O r = r **)

goalw Equiv.thy [trans_def,sym_def,converse_def]
    "!!r. [| sym(r); trans(r) |] ==> converse(r) O r <= r";
by (fast_tac (comp_cs addSEs [converseD]) 1);
qed "sym_trans_comp_subset";

val [major,minor]=goal Equiv.thy "[|<x,y>:r; z=<x,y>|] ==>  z:r";
by (simp_tac (prod_ss addsimps [minor]) 1);
by (rtac major 1);
qed "BreakPair";

val [major]=goal Equiv.thy "[|? x y. <x,y>:r & z=<x,y>|] ==>  z:r";
by (resolve_tac [major RS exE] 1);
by (etac exE 1);
by (etac conjE 1);
by (asm_simp_tac (prod_ss addsimps [minor]) 1);
qed "BreakPair1";

val [major,minor]=goal Equiv.thy "[|z:r; z=<x,y>|] ==> <x,y>:r";
by (simp_tac (prod_ss addsimps [minor RS sym]) 1);
by (rtac major 1);
qed "BuildPair";

val [major]=goal Equiv.thy "[|? z:r. <x,y>=z|] ==> <x,y>:r";
by (resolve_tac [major RS bexE] 1);
by (asm_simp_tac (prod_ss addsimps []) 1);
qed "BuildPair1";

val rel_pair_cs = rel_cs addIs [BuildPair1] 
                         addEs [BreakPair1];

goalw Equiv.thy [refl_def,converse_def]
    "!!A r. refl A r ==> r <= converse(r) O r";
by (step_tac comp_cs 1);
by (dtac subsetD 1);
by (assume_tac 1);
by (etac SigmaE 1);
by (rtac BreakPair1 1);
by (fast_tac comp_cs 1);
qed "refl_comp_subset";

goalw Equiv.thy [equiv_def]
    "!!A r. equiv A r ==> converse(r) O r = r";
by (rtac equalityI 1);
by (REPEAT (ares_tac [sym_trans_comp_subset, refl_comp_subset] 1
     ORELSE etac conjE 1));
qed "equiv_comp_eq";

(*second half*)
goalw Equiv.thy [equiv_def,refl_def,sym_def,trans_def]
    "!!A r. [| converse(r) O r = r;  Domain(r) = A |] ==> equiv A r";
by (etac equalityE 1);
by (subgoal_tac "ALL x y. <x,y> : r --> <y,x> : r" 1);
by (safe_tac set_cs);
by (fast_tac (set_cs addSIs [converseI] addIs [compI]) 3);
by (fast_tac (set_cs addSIs [converseI] addIs [compI] addSEs [DomainE]) 2);
by (fast_tac (rel_pair_cs addSEs [SigmaE] addSIs [SigmaI]) 1);
by (dtac subsetD 1);
by (dtac subsetD 1);
by (fast_tac rel_cs 1);
by (fast_tac rel_cs 1);
by flexflex_tac;
by (dtac subsetD 1);
by (fast_tac converse_cs 2);
by (fast_tac converse_cs 1);
qed "comp_equivI";

(** Equivalence classes **)

(*Lemma for the next result*)
goalw Equiv.thy [equiv_def,trans_def,sym_def]
    "!!A r. [| equiv A r;  <a,b>: r |] ==> r^^{a} <= r^^{b}";
by (safe_tac rel_cs);
by (rtac ImageI 1);
by (fast_tac rel_cs 2);
by (fast_tac rel_cs 1);
qed "equiv_class_subset";

goal Equiv.thy "!!A r. [| equiv A r;  <a,b>: r |] ==> r^^{a} = r^^{b}";
by (REPEAT (ares_tac [equalityI, equiv_class_subset] 1));
by (rewrite_goals_tac [equiv_def,sym_def]);
by (fast_tac rel_cs 1);
qed "equiv_class_eq";

val prems = goalw Equiv.thy [equiv_def,refl_def]
    "[| equiv A r;  a: A |] ==> a: r^^{a}";
by (cut_facts_tac prems 1);
by (fast_tac rel_cs 1);
qed "equiv_class_self";

(*Lemma for the next result*)
goalw Equiv.thy [equiv_def,refl_def]
    "!!A r. [| equiv A r;  r^^{b} <= r^^{a};  b: A |] ==> <a,b>: r";
by (fast_tac rel_cs 1);
qed "subset_equiv_class";

val prems = goal Equiv.thy
    "[| r^^{a} = r^^{b};  equiv A r;  b: A |] ==> <a,b>: r";
by (REPEAT (resolve_tac (prems @ [equalityD2, subset_equiv_class]) 1));
qed "eq_equiv_class";

(*thus r^^{a} = r^^{b} as well*)
goalw Equiv.thy [equiv_def,trans_def,sym_def]
    "!!A r. [| equiv A r;  x: (r^^{a} Int r^^{b}) |] ==> <a,b>: r";
by (fast_tac rel_cs 1);
qed "equiv_class_nondisjoint";

val [major] = goalw Equiv.thy [equiv_def,refl_def]
    "equiv A r ==> r <= Sigma A (%x.A)";
by (rtac (major RS conjunct1 RS conjunct1) 1);
qed "equiv_type";

goal Equiv.thy
    "!!A r. equiv A r ==> (<x,y>: r) = (r^^{x} = r^^{y} & x:A & y:A)";
by (safe_tac rel_cs);
by ((rtac equiv_class_eq 1) THEN (assume_tac 1) THEN (assume_tac 1));
by ((rtac eq_equiv_class 3) THEN 
    (assume_tac 4) THEN (assume_tac 4) THEN (assume_tac 3));
by ((dtac equiv_type 1) THEN (dtac rev_subsetD 1) THEN
    (assume_tac 1) THEN (dtac SigmaD1 1) THEN (assume_tac 1));
by ((dtac equiv_type 1) THEN (dtac rev_subsetD 1) THEN
    (assume_tac 1) THEN (dtac SigmaD2 1) THEN (assume_tac 1));
qed "equiv_class_eq_iff";

goal Equiv.thy
    "!!A r. [| equiv A r;  x: A;  y: A |] ==> (r^^{x} = r^^{y}) = (<x,y>: r)";
by (safe_tac rel_cs);
by ((rtac eq_equiv_class 1) THEN 
    (assume_tac 1) THEN (assume_tac 1) THEN (assume_tac 1));
by ((rtac equiv_class_eq 1) THEN 
    (assume_tac 1) THEN (assume_tac 1));
qed "eq_equiv_class_iff";

(*** Quotients ***)

(** Introduction/elimination rules -- needed? **)

val prems = goalw Equiv.thy [quotient_def] "x:A ==> r^^{x}: A/r";
by (rtac UN_I 1);
by (resolve_tac prems 1);
by (rtac singletonI 1);
qed "quotientI";

val [major,minor] = goalw Equiv.thy [quotient_def]
    "[| X:(A/r);  !!x. [| X = r^^{x};  x:A |] ==> P |] 	\
\    ==> P";
by (resolve_tac [major RS UN_E] 1);
by (rtac minor 1);
by (assume_tac 2);
by (fast_tac rel_cs 1);
qed "quotientE";

(** Not needed by Theory Integ --> bypassed **)
(**goalw Equiv.thy [equiv_def,refl_def,quotient_def]
    "!!A r. equiv A r ==> Union(A/r) = A";
by (fast_tac eq_cs 1);
qed "Union_quotient";
**)

(** Not needed by Theory Integ --> bypassed **)
(*goalw Equiv.thy [quotient_def]
    "!!A r. [| equiv A r;  X: A/r;  Y: A/r |] ==> X=Y | (X Int Y <= 0)";
by (safe_tac (ZF_cs addSIs [equiv_class_eq]));
by (assume_tac 1);
by (rewrite_goals_tac [equiv_def,trans_def,sym_def]);
by (fast_tac ZF_cs 1);
qed "quotient_disj";
**)

(**** Defining unary operations upon equivalence classes ****)

(* theorem needed to prove UN_equiv_class *)
goal Set.thy "!!A. [| a:A; ! y:A. b(y)=b(a) |] ==> (UN y:A. b(y))=b(a)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "UN_singleton_lemma";
val UN_singleton = ballI RSN (2,UN_singleton_lemma);


(** These proofs really require as local premises
     equiv A r;  congruent r b
**)

(*Conversion rule*)
val prems as [equivA,bcong,_] = goal Equiv.thy
    "[| equiv A r;  congruent r b;  a: A |] ==> (UN x:r^^{a}. b(x)) = b(a)";
by (cut_facts_tac prems 1);
by (rtac UN_singleton 1);
by (rtac equiv_class_self 1);
by (assume_tac 1);
by (assume_tac 1);
by (rewrite_goals_tac [equiv_def,congruent_def,sym_def]);
by (fast_tac rel_cs 1);
qed "UN_equiv_class";

(*Resolve th against the "local" premises*)
val localize = RSLIST [equivA,bcong];

(*type checking of  UN x:r``{a}. b(x) *)
val _::_::prems = goalw Equiv.thy [quotient_def]
    "[| equiv A r;  congruent r b;  X: A/r;	\
\	!!x.  x : A ==> b(x) : B |] 	\
\    ==> (UN x:X. b(x)) : B";
by (cut_facts_tac prems 1);
by (safe_tac rel_cs);
by (rtac (localize UN_equiv_class RS ssubst) 1);
by (REPEAT (ares_tac prems 1));
qed "UN_equiv_class_type";

(*Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be !!y. y:A ==> b(y):B
*)
val _::_::prems = goalw Equiv.thy [quotient_def]
    "[| equiv A r;   congruent r b;  \
\       (UN x:X. b(x))=(UN y:Y. b(y));  X: A/r;  Y: A/r;  \
\       !!x y. [| x:A; y:A; b(x)=b(y) |] ==> <x,y>:r |] 	\
\    ==> X=Y";
by (cut_facts_tac prems 1);
by (safe_tac rel_cs);
by (rtac (equivA RS equiv_class_eq) 1);
by (REPEAT (ares_tac prems 1));
by (etac box_equals 1);
by (REPEAT (ares_tac [localize UN_equiv_class] 1));
qed "UN_equiv_class_inject";


(**** Defining binary operations upon equivalence classes ****)


goalw Equiv.thy [congruent_def,congruent2_def,equiv_def,refl_def]
    "!!A r. [| equiv A r;  congruent2 r b;  a: A |] ==> congruent r (b a)";
by (fast_tac rel_cs 1);
qed "congruent2_implies_congruent";

val equivA::prems = goalw Equiv.thy [congruent_def]
    "[| equiv A r;  congruent2 r b;  a: A |] ==> \
\    congruent r (%x1. UN x2:r^^{a}. b x1 x2)";
by (cut_facts_tac (equivA::prems) 1);
by (safe_tac rel_cs);
by (rtac (equivA RS equiv_type RS subsetD RS SigmaE2) 1);
by (assume_tac 1);
by (asm_simp_tac (prod_ss addsimps [equivA RS UN_equiv_class,
				 congruent2_implies_congruent]) 1);
by (rewrite_goals_tac [congruent2_def,equiv_def,refl_def]);
by (fast_tac rel_cs 1);
qed "congruent2_implies_congruent_UN";

val prems as equivA::_ = goal Equiv.thy
    "[| equiv A r;  congruent2 r b;  a1: A;  a2: A |]  \
\    ==> (UN x1:r^^{a1}. UN x2:r^^{a2}. b x1 x2) = b a1 a2";
by (cut_facts_tac prems 1);
by (asm_simp_tac (prod_ss addsimps [equivA RS UN_equiv_class,
				    congruent2_implies_congruent,
				    congruent2_implies_congruent_UN]) 1);
qed "UN_equiv_class2";

(*type checking*)
val prems = goalw Equiv.thy [quotient_def]
    "[| equiv A r;  congruent2 r b;  \
\       X1: A/r;  X2: A/r;	\
\	!!x1 x2.  [| x1: A; x2: A |] ==> b x1 x2 : B |]    \
\    ==> (UN x1:X1. UN x2:X2. b x1 x2) : B";
by (cut_facts_tac prems 1);
by (safe_tac rel_cs);
by (REPEAT (ares_tac (prems@[UN_equiv_class_type,
			     congruent2_implies_congruent_UN,
			     congruent2_implies_congruent, quotientI]) 1));
qed "UN_equiv_class_type2";


(*Suggested by John Harrison -- the two subproofs may be MUCH simpler
  than the direct proof*)
val prems = goalw Equiv.thy [congruent2_def,equiv_def,refl_def]
    "[| equiv A r;	\
\       !! y z w. [| w: A;  <y,z> : r |] ==> b y w = b z w;      \
\       !! y z w. [| w: A;  <y,z> : r |] ==> b w y = b w z       \
\    |] ==> congruent2 r b";
by (cut_facts_tac prems 1);
by (safe_tac rel_cs);
by (rtac trans 1);
by (REPEAT (ares_tac prems 1
     ORELSE etac (subsetD RS SigmaE2) 1 THEN assume_tac 2 THEN assume_tac 1));
qed "congruent2I";

val [equivA,commute,congt] = goal Equiv.thy
    "[| equiv A r;	\
\       !! y z. [| y: A;  z: A |] ==> b y z = b z y;        \
\       !! y z w. [| w: A;  <y,z>: r |] ==> b w y = b w z	\
\    |] ==> congruent2 r b";
by (resolve_tac [equivA RS congruent2I] 1);
by (rtac (commute RS trans) 1);
by (rtac (commute RS trans RS sym) 3);
by (rtac sym 5);
by (REPEAT (ares_tac [congt] 1
     ORELSE etac (equivA RS equiv_type RS subsetD RS SigmaE2) 1));
qed "congruent2_commuteI";

