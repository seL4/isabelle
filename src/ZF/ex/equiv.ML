(*  Title: 	ZF/ex/equiv.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For equiv.thy.  Equivalence relations in Zermelo-Fraenkel Set Theory 
*)

val RSLIST = curry (op MRS);

open Equiv;

(*** Suppes, Theorem 70: r is an equiv relation iff converse(r) O r = r ***)

(** first half: equiv(A,r) ==> converse(r) O r = r **)

goalw Equiv.thy [trans_def,sym_def]
    "!!r. [| sym(r); trans(r) |] ==> converse(r) O r <= r";
by (fast_tac (ZF_cs addSEs [converseD,compE]) 1);
val sym_trans_comp_subset = result();

goalw Equiv.thy [refl_def]
    "!!A r. refl(A,r) ==> r <= converse(r) O r";
by (fast_tac (ZF_cs addSIs [converseI] addIs [compI]) 1);
val refl_comp_subset = result();

goalw Equiv.thy [equiv_def]
    "!!A r. equiv(A,r) ==> converse(r) O r = r";
by (rtac equalityI 1);
by (REPEAT (ares_tac [sym_trans_comp_subset, refl_comp_subset] 1
     ORELSE etac conjE 1));
val equiv_comp_eq = result();

(*second half*)
goalw Equiv.thy [equiv_def,refl_def,sym_def,trans_def]
    "!!A r. [| converse(r) O r = r;  domain(r) = A |] ==> equiv(A,r)";
by (etac equalityE 1);
by (subgoal_tac "ALL x y. <x,y> : r --> <y,x> : r" 1);
by (safe_tac ZF_cs);
by (fast_tac (ZF_cs addSIs [converseI] addIs [compI]) 3);
by (ALLGOALS (fast_tac 
	      (ZF_cs addSIs [converseI] addIs [compI] addSEs [compE])));
by flexflex_tac;
val comp_equivI = result();

(** Equivalence classes **)

(*Lemma for the next result*)
goalw Equiv.thy [equiv_def,trans_def,sym_def]
    "!!A r. [| equiv(A,r);  <a,b>: r |] ==> r``{a} <= r``{b}";
by (fast_tac ZF_cs 1);
val equiv_class_subset = result();

goal Equiv.thy "!!A r. [| equiv(A,r);  <a,b>: r |] ==> r``{a} = r``{b}";
by (REPEAT (ares_tac [equalityI, equiv_class_subset] 1));
by (rewrite_goals_tac [equiv_def,sym_def]);
by (fast_tac ZF_cs 1);
val equiv_class_eq = result();

val prems = goalw Equiv.thy [equiv_def,refl_def]
    "[| equiv(A,r);  a: A |] ==> a: r``{a}";
by (cut_facts_tac prems 1);
by (fast_tac ZF_cs 1);
val equiv_class_self = result();

(*Lemma for the next result*)
goalw Equiv.thy [equiv_def,refl_def]
    "!!A r. [| equiv(A,r);  r``{b} <= r``{a};  b: A |] ==> <a,b>: r";
by (fast_tac ZF_cs 1);
val subset_equiv_class = result();

val prems = goal Equiv.thy
    "[| r``{a} = r``{b};  equiv(A,r);  b: A |] ==> <a,b>: r";
by (REPEAT (resolve_tac (prems @ [equalityD2, subset_equiv_class]) 1));
val eq_equiv_class = result();

(*thus r``{a} = r``{b} as well*)
goalw Equiv.thy [equiv_def,trans_def,sym_def]
    "!!A r. [| equiv(A,r);  x: (r``{a} Int r``{b}) |] ==> <a,b>: r";
by (fast_tac ZF_cs 1);
val equiv_class_nondisjoint = result();

val [major] = goalw Equiv.thy [equiv_def,refl_def]
    "equiv(A,r) ==> r <= A*A";
by (rtac (major RS conjunct1 RS conjunct1) 1);
val equiv_type = result();

goal Equiv.thy
    "!!A r. equiv(A,r) ==> <x,y>: r <-> r``{x} = r``{y} & x:A & y:A";
by (fast_tac (ZF_cs addIs [eq_equiv_class, equiv_class_eq]
		    addDs [equiv_type]) 1);
val equiv_class_eq_iff = result();

goal Equiv.thy
    "!!A r. [| equiv(A,r);  x: A;  y: A |] ==> r``{x} = r``{y} <-> <x,y>: r";
by (fast_tac (ZF_cs addIs [eq_equiv_class, equiv_class_eq]
		    addDs [equiv_type]) 1);
val eq_equiv_class_iff = result();

(*** Quotients ***)

(** Introduction/elimination rules -- needed? **)

val prems = goalw Equiv.thy [quotient_def] "x:A ==> r``{x}: A/r";
by (rtac RepFunI 1);
by (resolve_tac prems 1);
val quotientI = result();

val major::prems = goalw Equiv.thy [quotient_def]
    "[| X: A/r;  !!x. [| X = r``{x};  x:A |] ==> P |] 	\
\    ==> P";
by (rtac (major RS RepFunE) 1);
by (eresolve_tac prems 1);
by (assume_tac 1);
val quotientE = result();

goalw Equiv.thy [equiv_def,refl_def,quotient_def]
    "!!A r. equiv(A,r) ==> Union(A/r) = A";
by (fast_tac eq_cs 1);
val Union_quotient = result();

goalw Equiv.thy [quotient_def]
    "!!A r. [| equiv(A,r);  X: A/r;  Y: A/r |] ==> X=Y | (X Int Y <= 0)";
by (safe_tac (ZF_cs addSIs [equiv_class_eq]));
by (assume_tac 1);
by (rewrite_goals_tac [equiv_def,trans_def,sym_def]);
by (fast_tac ZF_cs 1);
val quotient_disj = result();

(**** Defining unary operations upon equivalence classes ****)

(** These proofs really require as local premises
     equiv(A,r);  congruent(r,b)
**)

(*Conversion rule*)
val prems as [equivA,bcong,_] = goal Equiv.thy
    "[| equiv(A,r);  congruent(r,b);  a: A |] ==> (UN x:r``{a}. b(x)) = b(a)";
by (cut_facts_tac prems 1);
by (rtac UN_singleton 1);
by (etac equiv_class_self 1);
by (assume_tac 1);
by (rewrite_goals_tac [equiv_def,sym_def,congruent_def]);
by (fast_tac ZF_cs 1);
val UN_equiv_class = result();

(*Resolve th against the "local" premises*)
val localize = RSLIST [equivA,bcong];

(*type checking of  UN x:r``{a}. b(x) *)
val _::_::prems = goalw Equiv.thy [quotient_def]
    "[| equiv(A,r);  congruent(r,b);  X: A/r;	\
\	!!x.  x : A ==> b(x) : B |] 	\
\    ==> (UN x:X. b(x)) : B";
by (cut_facts_tac prems 1);
by (safe_tac ZF_cs);
by (rtac (localize UN_equiv_class RS ssubst) 1);
by (REPEAT (ares_tac prems 1));
val UN_equiv_class_type = result();

(*Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be !!y. y:A ==> b(y):B
*)
val _::_::prems = goalw Equiv.thy [quotient_def]
    "[| equiv(A,r);   congruent(r,b);  \
\       (UN x:X. b(x))=(UN y:Y. b(y));  X: A/r;  Y: A/r;  \
\       !!x y. [| x:A; y:A; b(x)=b(y) |] ==> <x,y>:r |] 	\
\    ==> X=Y";
by (cut_facts_tac prems 1);
by (safe_tac ZF_cs);
by (rtac (equivA RS equiv_class_eq) 1);
by (REPEAT (ares_tac prems 1));
by (etac box_equals 1);
by (REPEAT (ares_tac [localize UN_equiv_class] 1));
val UN_equiv_class_inject = result();


(**** Defining binary operations upon equivalence classes ****)


goalw Equiv.thy [congruent_def,congruent2_def,equiv_def,refl_def]
    "!!A r. [| equiv(A,r);  congruent2(r,b);  a: A |] ==> congruent(r,b(a))";
by (fast_tac ZF_cs 1);
val congruent2_implies_congruent = result();

val equivA::prems = goalw Equiv.thy [congruent_def]
    "[| equiv(A,r);  congruent2(r,b);  a: A |] ==> \
\    congruent(r, %x1. UN x2:r``{a}. b(x1,x2))";
by (cut_facts_tac (equivA::prems) 1);
by (safe_tac ZF_cs);
by (rtac (equivA RS equiv_type RS subsetD RS SigmaE2) 1);
by (assume_tac 1);
by (ASM_SIMP_TAC (ZF_ss addrews [equivA RS UN_equiv_class,
				 congruent2_implies_congruent]) 1);
by (rewrite_goals_tac [congruent2_def,equiv_def,refl_def]);
by (fast_tac ZF_cs 1);
val congruent2_implies_congruent_UN = result();

val prems as equivA::_ = goal Equiv.thy
    "[| equiv(A,r);  congruent2(r,b);  a1: A;  a2: A |]  \
\    ==> (UN x1:r``{a1}. UN x2:r``{a2}. b(x1,x2)) = b(a1,a2)";
by (cut_facts_tac prems 1);
by (ASM_SIMP_TAC (ZF_ss addrews [equivA RS UN_equiv_class,
				 congruent2_implies_congruent,
				 congruent2_implies_congruent_UN]) 1);
val UN_equiv_class2 = result();

(*type checking*)
val prems = goalw Equiv.thy [quotient_def]
    "[| equiv(A,r);  congruent2(r,b);  \
\       X1: A/r;  X2: A/r;	\
\	!!x1 x2.  [| x1: A; x2: A |] ==> b(x1,x2) : B |]    \
\    ==> (UN x1:X1. UN x2:X2. b(x1,x2)) : B";
by (cut_facts_tac prems 1);
by (safe_tac ZF_cs);
by (REPEAT (ares_tac (prems@[UN_equiv_class_type,
			     congruent2_implies_congruent_UN,
			     congruent2_implies_congruent, quotientI]) 1));
val UN_equiv_class_type2 = result();


(*Suggested by John Harrison -- the two subproofs may be MUCH simpler
  than the direct proof*)
val prems = goalw Equiv.thy [congruent2_def,equiv_def,refl_def]
    "[| equiv(A,r);	\
\       !! y z w. [| w: A;  <y,z> : r |] ==> b(y,w) = b(z,w);      \
\       !! y z w. [| w: A;  <y,z> : r |] ==> b(w,y) = b(w,z)       \
\    |] ==> congruent2(r,b)";
by (cut_facts_tac prems 1);
by (safe_tac ZF_cs);
by (rtac trans 1);
by (REPEAT (ares_tac prems 1
     ORELSE etac (subsetD RS SigmaE2) 1 THEN assume_tac 2 THEN assume_tac 1));
val congruent2I = result();

val [equivA,commute,congt] = goal Equiv.thy
    "[| equiv(A,r);	\
\       !! y z w. [| y: A;  z: A |] ==> b(y,z) = b(z,y);        \
\       !! y z w. [| w: A;  <y,z>: r |] ==> b(w,y) = b(w,z)	\
\    |] ==> congruent2(r,b)";
by (resolve_tac [equivA RS congruent2I] 1);
by (rtac (commute RS trans) 1);
by (rtac (commute RS trans RS sym) 3);
by (rtac sym 5);
by (REPEAT (ares_tac [congt] 1
     ORELSE etac (equivA RS equiv_type RS subsetD RS SigmaE2) 1));
val congruent2_commuteI = result();

(***OBSOLETE VERSION
(*Rules congruentI and congruentD would simplify use of rewriting below*)
val [equivA,ZinA,congt,commute] = goalw Equiv.thy [quotient_def]
    "[| equiv(A,r);  Z: A/r;  \
\       !!w. [| w: A |] ==> congruent(r, %z.b(w,z));	\
\       !!x y. [| x: A;  y: A |] ==> b(y,x) = b(x,y)	\
\    |] ==> congruent(r, %w. UN z: Z. b(w,z))";
val congt' = rewrite_rule [congruent_def] congt;
by (cut_facts_tac [ZinA,congt] 1);
by (rewtac congruent_def);
by (safe_tac ZF_cs);
by (rtac (equivA RS equiv_type RS subsetD RS SigmaE2) 1);
by (assume_tac 1);
by (ASM_SIMP_TAC (ZF_ss addrews [congt RS (equivA RS UN_equiv_class)]) 1);
by (rtac (commute RS trans) 1);
by (rtac (commute RS trans RS sym) 3);
by (rtac sym 5);
by (REPEAT (ares_tac [congt' RS spec RS spec RS mp] 1));
val congruent_commuteI = result();
***)
