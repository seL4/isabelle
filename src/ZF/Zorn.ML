(*  Title: 	ZF/Zorn.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Proofs from the paper
    Abrial & Laffitte, 
    Towards the Mechanization of the Proofs of Some 
    Classical Theorems of Set Theory. 
*)

open Zorn;

(*** Section 1.  Mathematical Preamble ***)

goal ZF.thy "!!A B C. (ALL x:C. x<=A | B<=x) ==> Union(C)<=A | B<=Union(C)";
by (fast_tac ZF_cs 1);
val Union_lemma0 = result();

goal ZF.thy
    "!!A B C. [| c:C; ALL x:C. A<=x | x<=B |] ==> A<=Inter(C) | Inter(C)<=B";
by (fast_tac ZF_cs 1);
val Inter_lemma0 = result();


(*** Section 2.  The Transfinite Construction ***)

goalw Zorn.thy [increasing_def]
    "!!f A. f: increasing(A) ==> f: Pow(A)->Pow(A)";
by (eresolve_tac [CollectD1] 1);
val increasingD1 = result();

goalw Zorn.thy [increasing_def]
    "!!f A. [| f: increasing(A); x<=A |] ==> x <= f`x";
by (eresolve_tac [CollectD2 RS spec RS mp] 1);
by (assume_tac 1);
val increasingD2 = result();

(*Introduction rules*)
val [TFin_nextI, Pow_TFin_UnionI] = TFin.intrs;
val TFin_UnionI = PowI RS Pow_TFin_UnionI;

val TFin_is_subset = TFin.dom_subset RS subsetD RS PowD;


(** Structural induction on TFin(S,next) **)

val major::prems = goal Zorn.thy
  "[| n: TFin(S,next);  \
\     !!x. [| x : TFin(S,next);  P(x);  next: increasing(S) |] ==> P(next`x); \
\     !!Y. [| Y <= TFin(S,next);  ALL y:Y. P(y) |] ==> P(Union(Y)) \
\  |] ==> P(n)";
by (rtac (major RS TFin.induct) 1);
by (ALLGOALS (fast_tac (ZF_cs addIs prems)));
val TFin_induct = result();

(*Perform induction on n, then prove the major premise using prems. *)
fun TFin_ind_tac a prems i = 
    EVERY [res_inst_tac [("n",a)] TFin_induct i,
	   rename_last_tac a ["1"] (i+1),
	   rename_last_tac a ["2"] (i+2),
	   ares_tac prems i];

(*** Section 3.  Some Properties of the Transfinite Construction ***)

val increasing_trans = 
    TFin_is_subset RSN (3, increasingD2 RSN (2,subset_trans)) |> standard;

(*Lemma 1 of section 3.1*)
val major::prems = goal Zorn.thy
    "[| n: TFin(S,next);  m: TFin(S,next);  \
\       ALL x: TFin(S,next) . x<=m --> x=m | next`x<=m \
\    |] ==> n<=m | next`m<=n";
by (cut_facts_tac prems 1);
br (major RS TFin_induct) 1;
by (etac Union_lemma0 2);		(*or just fast_tac ZF_cs*)
by (fast_tac (subset_cs addIs [increasing_trans]) 1);
val TFin_linear_lemma1 = result();

(*Lemma 2 of section 3.2.  Interesting in its own right!
  Requires next: increasing(S) in the second induction step. *)
val [major,ninc] = goal Zorn.thy
    "[| m: TFin(S,next);  next: increasing(S) \
\    |] ==> ALL n: TFin(S,next) . n<=m --> n=m | next`n<=m";
br (major RS TFin_induct) 1;
br (impI RS ballI) 1;
(*case split using TFin_linear_lemma1*)
by (res_inst_tac [("n1","n"), ("m1","x")] 
    (TFin_linear_lemma1 RS disjE) 1  THEN  REPEAT (assume_tac 1));
by (dres_inst_tac [("x","n")] bspec 1 THEN assume_tac 1);
by (fast_tac (subset_cs addIs [increasing_trans]) 1);
by (REPEAT (ares_tac [disjI1,equalityI] 1));
(*second induction step*)
br (impI RS ballI) 1;
br (Union_lemma0 RS disjE) 1;
be disjI2 3;
by (REPEAT (ares_tac [disjI1,equalityI] 2));
br ballI 1;
by (ball_tac 1);
by (set_mp_tac 1);
by (res_inst_tac [("n1","n"), ("m1","x")] 
    (TFin_linear_lemma1 RS disjE) 1  THEN  REPEAT (assume_tac 1));
by (fast_tac subset_cs 1);
br (ninc RS increasingD2 RS subset_trans RS disjI1) 1;
by (REPEAT (ares_tac [TFin_is_subset] 1));
val TFin_linear_lemma2 = result();

(*a more convenient form for Lemma 2*)
goal Zorn.thy
    "!!m n. [| n<=m;  m: TFin(S,next);  n: TFin(S,next);  next: increasing(S) \
\           |] ==> n=m | next`n<=m";
br (TFin_linear_lemma2 RS bspec RS mp) 1;
by (REPEAT (assume_tac 1));
val TFin_subsetD = result();

(*Consequences from section 3.3 -- Property 3.2, the ordering is total*)
goal Zorn.thy
    "!!m n. [| m: TFin(S,next);  n: TFin(S,next);  next: increasing(S) \
\           |] ==> n<=m | m<=n";
br (TFin_linear_lemma2 RSN (3,TFin_linear_lemma1) RS disjE) 1;
by (REPEAT (assume_tac 1) THEN etac disjI2 1);
by (fast_tac (subset_cs addIs [increasingD2 RS subset_trans, 
			       TFin_is_subset]) 1);
val TFin_subset_linear = result();


(*Lemma 3 of section 3.3*)
val major::prems = goal Zorn.thy
    "[| n: TFin(S,next);  m: TFin(S,next);  m = next`m |] ==> n<=m";
by (cut_facts_tac prems 1);
br (major RS TFin_induct) 1;
bd TFin_subsetD 1;
by (REPEAT (assume_tac 1));
by (fast_tac (ZF_cs addEs [ssubst]) 1);
by (fast_tac (subset_cs addIs [TFin_is_subset]) 1);
val equal_next_upper = result();

(*Property 3.3 of section 3.3*)
goal Zorn.thy
    "!!m. [| m: TFin(S,next);  next: increasing(S) \
\         |] ==> m = next`m <-> m = Union(TFin(S,next))";
br iffI 1;
br (Union_upper RS equalityI) 1;
br (equal_next_upper RS Union_least) 2;
by (REPEAT (assume_tac 1));
be ssubst 1;
by (rtac (increasingD2 RS equalityI) 1 THEN assume_tac 1);
by (ALLGOALS
    (fast_tac (subset_cs addIs [TFin_UnionI, TFin_nextI, TFin_is_subset])));
val equal_next_Union = result();


(*** Section 4.  Hausdorff's Theorem: every set contains a maximal chain ***)
(*** NB: We assume the partial ordering is <=, the subset relation! **)

(** Defining the "next" operation for Hausdorff's Theorem **)

goalw Zorn.thy [chain_def] "chain(A) <= Pow(A)";
by (resolve_tac [Collect_subset] 1);
val chain_subset_Pow = result();

goalw Zorn.thy [super_def] "super(A,c) <= chain(A)";
by (resolve_tac [Collect_subset] 1);
val super_subset_chain = result();

goalw Zorn.thy [maxchain_def] "maxchain(A) <= chain(A)";
by (resolve_tac [Collect_subset] 1);
val maxchain_subset_chain = result();

goal Zorn.thy
    "!!S. [| ch : (PROD X:Pow(chain(S)) - {0}. X);	\
\            X : chain(S);  X ~: maxchain(S)		\
\         |] ==> ch ` super(S,X) : super(S,X)";
by (eresolve_tac [apply_type] 1);
by (rewrite_goals_tac [super_def, maxchain_def]);
by (fast_tac ZF_cs 1);
val choice_super = result();

goal Zorn.thy
    "!!S. [| ch : (PROD X:Pow(chain(S)) - {0}. X);	\
\            X : chain(S);  X ~: maxchain(S)		\
\         |] ==> ch ` super(S,X) ~= X";
by (resolve_tac [notI] 1);
by (dresolve_tac [choice_super] 1);
by (assume_tac 1);
by (assume_tac 1);
by (asm_full_simp_tac (ZF_ss addsimps [super_def]) 1);
val choice_not_equals = result();

(*This justifies Definition 4.4*)
goal Zorn.thy
    "!!S. ch: (PROD X: Pow(chain(S))-{0}. X) ==>	\
\          EX next: increasing(S). ALL X: Pow(S). 	\
\                     next`X = if(X: chain(S)-maxchain(S), ch`super(S,X), X)";
by (rtac bexI 1);
by (rtac ballI 1);
by (resolve_tac [beta] 1);
by (assume_tac 1);
bw increasing_def;
by (rtac CollectI 1);
by (rtac lam_type 1);
by (asm_simp_tac (ZF_ss setloop split_tac [expand_if]) 1);
by (fast_tac (ZF_cs addSIs [super_subset_chain RS subsetD,
			    chain_subset_Pow RS subsetD,
			    choice_super]) 1);
(*Now, verify that it increases*)
by (resolve_tac [allI] 1);
by (resolve_tac [impI] 1);
by (asm_simp_tac (ZF_ss addsimps [Pow_iff, subset_refl]
                        setloop split_tac [expand_if]) 1);
by (safe_tac ZF_cs);
by (dresolve_tac [choice_super] 1);
by (REPEAT (assume_tac 1));
bw super_def;
by (fast_tac ZF_cs 1);
val Hausdorff_next_exists = result();

(*Lemma 4*)
goal Zorn.thy
 "!!S. [| c: TFin(S,next);				\
\	  ch: (PROD X: Pow(chain(S))-{0}. X);		\
\         next: increasing(S);			 	\
\         ALL X: Pow(S). next`X = 	\
\			  if(X: chain(S)-maxchain(S), ch`super(S,X), X)	\
\      |] ==> c: chain(S)";
by (eresolve_tac [TFin_induct] 1);
by (asm_simp_tac 
    (ZF_ss addsimps [chain_subset_Pow RS subsetD, 
		     choice_super RS (super_subset_chain RS subsetD)]
           setloop split_tac [expand_if]) 1);
bw chain_def;
by (rtac CollectI 1 THEN fast_tac ZF_cs 1);
(*Cannot use safe_tac: the disjunction must be left alone*)
by (REPEAT (rtac ballI 1 ORELSE etac UnionE 1));
by (res_inst_tac  [("m1","B"), ("n1","Ba")] (TFin_subset_linear RS disjE) 1);
(*fast_tac is just too slow here!*)
by (DEPTH_SOLVE (eresolve_tac [asm_rl, subsetD] 1
       ORELSE ball_tac 1 THEN etac (CollectD2 RS bspec RS bspec) 1));
val TFin_chain_lemma4 = result();

goal Zorn.thy "EX c. c : maxchain(S)";
by (rtac (AC_Pi_Pow RS exE) 1);
by (rtac (Hausdorff_next_exists RS bexE) 1);
by (assume_tac 1);
by (rename_tac "ch next" 1);
by (subgoal_tac "Union(TFin(S,next)) : chain(S)" 1);
by (REPEAT (ares_tac [TFin_chain_lemma4, subset_refl RS TFin_UnionI] 2));
by (res_inst_tac [("x", "Union(TFin(S,next))")] exI 1);
by (resolve_tac [classical] 1);
by (subgoal_tac "next ` Union(TFin(S,next)) = Union(TFin(S,next))" 1);
by (resolve_tac [equal_next_Union RS iffD2 RS sym] 2);
by (resolve_tac [subset_refl RS TFin_UnionI] 2);
by (assume_tac 2);
by (resolve_tac [refl] 2);
by (asm_full_simp_tac 
    (ZF_ss addsimps [subset_refl RS TFin_UnionI RS
		     (TFin.dom_subset RS subsetD)]
           setloop split_tac [expand_if]) 1);
by (eresolve_tac [choice_not_equals RS notE] 1);
by (REPEAT (assume_tac 1));
val Hausdorff = result();


(*** Section 5.  Zorn's Lemma: if all chains in S have upper bounds in S 
                               then S contains a maximal element ***)

(*Used in the proof of Zorn's Lemma*)
goalw Zorn.thy [chain_def]
    "!!c. [| c: chain(A);  z: A;  ALL x:c. x<=z |] ==> cons(z,c) : chain(A)";
by (fast_tac ZF_cs 1);
val chain_extend = result();

goal Zorn.thy
    "!!S. ALL c: chain(S). Union(c) : S ==> EX y:S. ALL z:S. y<=z --> y=z";
by (resolve_tac [Hausdorff RS exE] 1);
by (asm_full_simp_tac (ZF_ss addsimps [maxchain_def]) 1);
by (rename_tac "c" 1);
by (res_inst_tac [("x", "Union(c)")] bexI 1);
by (fast_tac ZF_cs 2);
by (safe_tac ZF_cs);
by (rename_tac "z" 1);
by (resolve_tac [classical] 1);
by (subgoal_tac "cons(z,c): super(S,c)" 1);
by (fast_tac (ZF_cs addEs [equalityE]) 1);
bw super_def;
by (safe_tac eq_cs);
by (fast_tac (ZF_cs addEs [chain_extend]) 1);
by (best_tac (ZF_cs addEs [equalityE]) 1);
val Zorn = result();


(*** Section 6.  Zermelo's Theorem: every set can be well-ordered ***)

(*Lemma 5*)
val major::prems = goal Zorn.thy
    "[| n: TFin(S,next);  Z <= TFin(S,next);  z:Z;  ~ Inter(Z) : Z	\
\    |] ==> ALL m:Z. n<=m";
by (cut_facts_tac prems 1);
br (major RS TFin_induct) 1;
by (fast_tac ZF_cs 2);			(*second induction step is easy*)
br ballI 1;
br (bspec RS TFin_subsetD RS disjE) 1;
by (REPEAT_SOME (eresolve_tac [asm_rl,subsetD]));
by (subgoal_tac "x = Inter(Z)" 1);
by (fast_tac ZF_cs 1);
by (fast_tac eq_cs 1);
val TFin_well_lemma5 = result();

(*Well-ordering of TFin(S,next)*)
goal Zorn.thy "!!Z. [| Z <= TFin(S,next);  z:Z |] ==> Inter(Z) : Z";
br classical 1;
by (subgoal_tac "Z = {Union(TFin(S,next))}" 1);
by (asm_simp_tac (ZF_ss addsimps [Inter_singleton]) 1);
be equal_singleton 1;
br (Union_upper RS equalityI) 1;
br (subset_refl RS TFin_UnionI RS TFin_well_lemma5 RS bspec) 2;
by (REPEAT_SOME (eresolve_tac [asm_rl,subsetD]));
val well_ord_TFin_lemma = result();

(*This theorem just packages the previous result*)
goal Zorn.thy
    "!!S. next: increasing(S) ==> \
\         well_ord(TFin(S,next), Subset_rel(TFin(S,next)))";
by (resolve_tac [well_ordI] 1);
by (rewrite_goals_tac [Subset_rel_def, linear_def]);
(*Prove the linearity goal first*)
by (REPEAT (rtac ballI 2));
by (excluded_middle_tac "x=y" 2);
by (fast_tac ZF_cs 3);
(*The x~=y case remains*)
by (res_inst_tac [("n1","x"), ("m1","y")] 
    (TFin_subset_linear RS disjE) 2  THEN  REPEAT (assume_tac 2));
by (fast_tac ZF_cs 2);
by (fast_tac ZF_cs 2);
(*Now prove the well_foundedness goal*)
by (resolve_tac [wf_onI] 1);
by (forward_tac [well_ord_TFin_lemma] 1 THEN assume_tac 1);
by (dres_inst_tac [("x","Inter(Z)")] bspec 1 THEN assume_tac 1);
by (fast_tac eq_cs 1);
val well_ord_TFin = result();

(** Defining the "next" operation for Zermelo's Theorem **)

goal AC.thy
    "!!S. [| ch : (PROD X:Pow(S) - {0}. X);  X<=S;  X~=S	\
\         |] ==> ch ` (S-X) : S-X";
by (eresolve_tac [apply_type] 1);
by (fast_tac (eq_cs addEs [equalityE]) 1);
val choice_Diff = result();

(*This justifies Definition 6.1*)
goal Zorn.thy
    "!!S. ch: (PROD X: Pow(S)-{0}. X) ==>		\
\          EX next: increasing(S). ALL X: Pow(S). 	\
\                     next`X = if(X=S, S, cons(ch`(S-X), X))";
by (rtac bexI 1);
by (rtac ballI 1);
by (resolve_tac [beta] 1);
by (assume_tac 1);
bw increasing_def;
by (rtac CollectI 1);
by (rtac lam_type 1);
(*Verify that it increases*)
by (resolve_tac [allI] 2);
by (resolve_tac [impI] 2);
by (asm_simp_tac (ZF_ss addsimps [Pow_iff, subset_consI, subset_refl]
                        setloop split_tac [expand_if]) 2);
(*Type checking is surprisingly hard!*)
by (asm_simp_tac (ZF_ss addsimps [Pow_iff, cons_subset_iff, subset_refl]
                        setloop split_tac [expand_if]) 1);
by (fast_tac (ZF_cs addSIs [choice_Diff RS DiffD1]) 1);
val Zermelo_next_exists = result();


(*The construction of the injection*)
goal Zorn.thy
  "!!S. [| ch: (PROD X: Pow(S)-{0}. X);			\
\          next: increasing(S);			 	\
\          ALL X: Pow(S). next`X = if(X=S, S, cons(ch`(S-X), X))	\
\       |] ==> (lam x:S. Union({y: TFin(S,next). x~: y})) 	\
\              : inj(S, TFin(S,next) - {S})";
by (res_inst_tac [("d", "%y. ch`(S-y)")] lam_injective 1);
by (rtac DiffI 1);
by (resolve_tac [Collect_subset RS TFin_UnionI] 1);
by (fast_tac (ZF_cs addSIs [Collect_subset RS TFin_UnionI]
                    addEs [equalityE]) 1);
by (subgoal_tac "x ~: Union({y: TFin(S,next). x~: y})" 1);
by (fast_tac (ZF_cs addEs [equalityE]) 2);
by (subgoal_tac "Union({y: TFin(S,next). x~: y}) ~= S" 1);
by (fast_tac (ZF_cs addEs [equalityE]) 2);
(*For proving x : next`Union(...);
  Abrial & Laffitte's justification appears to be faulty.*)
by (subgoal_tac "~ next ` Union({y: TFin(S,next). x~: y}) <= \
\                  Union({y: TFin(S,next). x~: y})" 1);
by (asm_simp_tac 
    (ZF_ss addsimps [Collect_subset RS TFin_UnionI RS TFin_is_subset,
		     Pow_iff, cons_subset_iff, subset_refl,
		     choice_Diff RS DiffD2]
           setloop split_tac [expand_if]) 2);
by (subgoal_tac "x : next ` Union({y: TFin(S,next). x~: y})" 1);
by (fast_tac (subset_cs addSIs [Collect_subset RS TFin_UnionI, TFin_nextI]) 2);
(*End of the lemmas!*)
by (asm_full_simp_tac 
    (ZF_ss addsimps [Collect_subset RS TFin_UnionI RS TFin_is_subset,
		     Pow_iff, cons_subset_iff, subset_refl]
           setloop split_tac [expand_if]) 1);
by (REPEAT (eresolve_tac [asm_rl, consE, sym, notE] 1));
val choice_imp_injection = result();

(*The wellordering theorem*)
goal Zorn.thy "EX r. well_ord(S,r)";
by (rtac (AC_Pi_Pow RS exE) 1);
by (rtac (Zermelo_next_exists RS bexE) 1);
by (assume_tac 1);
br exI 1;
by (resolve_tac [well_ord_rvimage] 1);
by (eresolve_tac [well_ord_TFin] 2);
by (resolve_tac [choice_imp_injection RS inj_weaken_type] 1);
by (REPEAT (ares_tac [Diff_subset] 1));
val AC_well_ord = result();
