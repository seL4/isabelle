(*  Title:      ZF/ZF.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1994  University of Cambridge

Basic introduction and elimination rules for Zermelo-Fraenkel Set Theory 
*)

(*Useful examples:  singletonI RS subst_elem,  subst_elem RSN (2,IntI) *)
Goal "[| b:A;  a=b |] ==> a:A";
by (etac ssubst 1);
by (assume_tac 1);
qed "subst_elem";


(*** Bounded universal quantifier ***)

val prems= Goalw [Ball_def] 
    "[| !!x. x:A ==> P(x) |] ==> ALL x:A. P(x)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1)) ;
qed "ballI";

Goalw [Ball_def] "[| ALL x:A. P(x);  x: A |] ==> P(x)";
by (etac (spec RS mp) 1);
by (assume_tac 1) ;
qed "bspec";

val major::prems= Goalw [Ball_def] 
    "[| ALL x:A. P(x);  P(x) ==> Q;  x~:A ==> Q |] ==> Q";
by (rtac (major RS allE) 1);
by (REPEAT (eresolve_tac (prems@[asm_rl,impCE]) 1)) ;
qed "ballE";

(*Used in the datatype package*)
Goal "[| x: A;  ALL x:A. P(x) |] ==> P(x)";
by (REPEAT (ares_tac [bspec] 1)) ;
qed "rev_bspec";

(*Instantiates x first: better for automatic theorem proving?*)
val major::prems= Goal
    "[| ALL x:A. P(x);  x~:A ==> Q;  P(x) ==> Q |] ==> Q";
by (rtac (major RS ballE) 1);
by (REPEAT (eresolve_tac prems 1)) ;
qed "rev_ballE";

AddSIs [ballI];
AddEs  [rev_ballE];

(*Takes assumptions ALL x:A.P(x) and a:A; creates assumption P(a)*)
val ball_tac = dtac bspec THEN' assume_tac;

(*Trival rewrite rule;   (ALL x:A.P)<->P holds only if A is nonempty!*)
Goal "(ALL x:A. P) <-> ((EX x. x:A) --> P)";
by (simp_tac (simpset() addsimps [Ball_def]) 1) ;
qed "ball_triv";
Addsimps [ball_triv];

(*Congruence rule for rewriting*)
val prems= Goalw [Ball_def] 
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) |] ==> Ball(A,P) <-> Ball(A',P')";
by (simp_tac (FOL_ss addsimps prems) 1) ;
qed "ball_cong";

(*** Bounded existential quantifier ***)

Goalw [Bex_def] "[| P(x);  x: A |] ==> EX x:A. P(x)";
by (Blast_tac 1);
qed "bexI";

(*The best argument order when there is only one x:A*)
Goalw [Bex_def] "[| x:A;  P(x) |] ==> EX x:A. P(x)";
by (Blast_tac 1);
qed "rev_bexI";

(*Not of the general form for such rules; ~EX has become ALL~ *)
val prems= Goal "[| ALL x:A. ~P(x) ==> P(a);  a: A |] ==> EX x:A. P(x)";
by (rtac classical 1);
by (REPEAT (ares_tac (prems@[bexI,ballI,notI,notE]) 1)) ;
qed "bexCI";

val major::prems= Goalw [Bex_def] 
    "[| EX x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q \
\    |] ==> Q";
by (rtac (major RS exE) 1);
by (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1)) ;
qed "bexE";

AddIs  [bexI];  
AddSEs [bexE];

(*We do not even have (EX x:A. True) <-> True unless A is nonempty!!*)
Goal "(EX x:A. P) <-> ((EX x. x:A) & P)";
by (simp_tac (simpset() addsimps [Bex_def]) 1) ;
qed "bex_triv";
Addsimps [bex_triv];

val prems= Goalw [Bex_def] 
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) \
\    |] ==> Bex(A,P) <-> Bex(A',P')";
by (simp_tac (FOL_ss addsimps prems addcongs [conj_cong]) 1) ;
qed "bex_cong";

Addcongs [ball_cong, bex_cong];


(*** Rules for subsets ***)

val prems= Goalw [subset_def] 
    "(!!x. x:A ==> x:B) ==> A <= B";
by (REPEAT (ares_tac (prems @ [ballI]) 1)) ;
qed "subsetI";

(*Rule in Modus Ponens style [was called subsetE] *)
Goalw [subset_def]  "[| A <= B;  c:A |] ==> c:B";
by (etac bspec 1);
by (assume_tac 1) ;
qed "subsetD";

(*Classical elimination rule*)
val major::prems= Goalw [subset_def] 
    "[| A <= B;  c~:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS ballE) 1);
by (REPEAT (eresolve_tac prems 1)) ;
qed "subsetCE";

AddSIs [subsetI];
AddEs  [subsetCE, subsetD];


(*Takes assumptions A<=B; c:A and creates the assumption c:B *)
val set_mp_tac = dtac subsetD THEN' assume_tac;

(*Sometimes useful with premises in this order*)
Goal "[| c:A; A<=B |] ==> c:B";
by (Blast_tac 1);
qed "rev_subsetD";

(*Converts A<=B to x:A ==> x:B*)
fun impOfSubs th = th RSN (2, rev_subsetD);

Goal "[| A <= B; c ~: B |] ==> c ~: A";
by (Blast_tac 1);
qed "contra_subsetD";

Goal "[| c ~: B;  A <= B |] ==> c ~: A";
by (Blast_tac 1);
qed "rev_contra_subsetD";

Goal "A <= A";
by (Blast_tac 1);
qed "subset_refl";

Addsimps [subset_refl];

Goal "[| A<=B;  B<=C |] ==> A<=C";
by (Blast_tac 1);
qed "subset_trans";

(*Useful for proving A<=B by rewriting in some cases*)
Goalw [subset_def,Ball_def] 
     "A<=B <-> (ALL x. x:A --> x:B)";
by (rtac iff_refl 1) ;
qed "subset_iff";


(*** Rules for equality ***)

(*Anti-symmetry of the subset relation*)
Goal "[| A <= B;  B <= A |] ==> A = B";
by (REPEAT (ares_tac [conjI, extension RS iffD2] 1)) ;
qed "equalityI";

AddIs [equalityI];

val [prem] = Goal "(!!x. x:A <-> x:B) ==> A = B";
by (rtac equalityI 1);
by (REPEAT (ares_tac [subsetI, prem RS iffD1, prem RS iffD2] 1)) ;
qed "equality_iffI";

bind_thm ("equalityD1", extension RS iffD1 RS conjunct1);
bind_thm ("equalityD2", extension RS iffD1 RS conjunct2);

val prems = Goal "[| A = B;  [| A<=B; B<=A |] ==> P |]  ==>  P";
by (DEPTH_SOLVE (resolve_tac (prems@[equalityD1,equalityD2]) 1)) ;
qed "equalityE";

val major::prems= Goal
    "[| A = B;  [| c:A; c:B |] ==> P;  [| c~:A; c~:B |] ==> P |]  ==>  P";
by (rtac (major RS equalityE) 1);
by (REPEAT (contr_tac 1 ORELSE eresolve_tac ([asm_rl,subsetCE]@prems) 1)) ;
qed "equalityCE";

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. 
  Would it be better to do subgoal_tac "ALL z. p = f(z) --> R(z)" ??*)
val prems = Goal "[| p: A;  !!z. z: A ==> p=z --> R |] ==> R";
by (rtac mp 1);
by (REPEAT (resolve_tac (refl::prems) 1)) ;
qed "setup_induction";


(*** Rules for Replace -- the derived form of replacement ***)

Goalw [Replace_def] 
    "b : {y. x:A, P(x,y)}  <->  (EX x:A. P(x,b) & (ALL y. P(x,y) --> y=b))";
by (rtac (replacement RS iff_trans) 1);
by (REPEAT (ares_tac [refl,bex_cong,iffI,ballI,allI,conjI,impI,ex1I] 1 
     ORELSE eresolve_tac [conjE, spec RS mp, ex1_functional] 1)) ;
qed "Replace_iff";

(*Introduction; there must be a unique y such that P(x,y), namely y=b. *)
val prems = Goal
    "[| P(x,b);  x: A;  !!y. P(x,y) ==> y=b |] ==> \
\    b : {y. x:A, P(x,y)}";
by (rtac (Replace_iff RS iffD2) 1);
by (REPEAT (ares_tac (prems@[bexI,conjI,allI,impI]) 1)) ;
qed "ReplaceI";

(*Elimination; may asssume there is a unique y such that P(x,y), namely y=b. *)
val prems = Goal
    "[| b : {y. x:A, P(x,y)};  \
\       !!x. [| x: A;  P(x,b);  ALL y. P(x,y)-->y=b |] ==> R \
\    |] ==> R";
by (rtac (Replace_iff RS iffD1 RS bexE) 1);
by (etac conjE 2);
by (REPEAT (ares_tac prems 1)) ;
qed "ReplaceE";

(*As above but without the (generally useless) 3rd assumption*)
val major::prems = Goal
    "[| b : {y. x:A, P(x,y)};  \
\       !!x. [| x: A;  P(x,b) |] ==> R \
\    |] ==> R";
by (rtac (major RS ReplaceE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "ReplaceE2";

AddIs  [ReplaceI];  
AddSEs [ReplaceE2];

val prems = Goal
    "[| A=B;  !!x y. x:B ==> P(x,y) <-> Q(x,y) |] ==> \
\    Replace(A,P) = Replace(B,Q)";
by (rtac equalityI 1);
by (REPEAT
    (eresolve_tac ((prems RL [subst, ssubst])@[asm_rl, ReplaceE, spec RS mp]) 1     ORELSE resolve_tac [subsetI, ReplaceI] 1 
     ORELSE (resolve_tac (prems RL [iffD1,iffD2]) 1 THEN assume_tac 2)));
qed "Replace_cong";

Addcongs [Replace_cong];

(*** Rules for RepFun ***)

Goalw [RepFun_def] "a : A ==> f(a) : {f(x). x:A}";
by (REPEAT (ares_tac [ReplaceI,refl] 1)) ;
qed "RepFunI";

(*Useful for coinduction proofs*)
Goal "[| b=f(a);  a : A |] ==> b : {f(x). x:A}";
by (etac ssubst 1);
by (etac RepFunI 1) ;
qed "RepFun_eqI";

val major::prems= Goalw [RepFun_def] 
    "[| b : {f(x). x:A};  \
\       !!x.[| x:A;  b=f(x) |] ==> P |] ==> \
\    P";
by (rtac (major RS ReplaceE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "RepFunE";

AddIs  [RepFun_eqI];  
AddSEs [RepFunE];

val prems= Goalw [RepFun_def] 
    "[| A=B;  !!x. x:B ==> f(x)=g(x) |] ==> RepFun(A,f) = RepFun(B,g)";
by (simp_tac (simpset() addsimps prems) 1) ;
qed "RepFun_cong";

Addcongs [RepFun_cong];

Goalw [Bex_def] "b : {f(x). x:A} <-> (EX x:A. b=f(x))";
by (Blast_tac 1);
qed "RepFun_iff";

Goal "{x. x:A} = A";
by (Blast_tac 1);
qed "triv_RepFun";

Addsimps [RepFun_iff, triv_RepFun];

(*** Rules for Collect -- forming a subset by separation ***)

(*Separation is derivable from Replacement*)
Goalw [Collect_def] "a : {x:A. P(x)} <-> a:A & P(a)";
by (Blast_tac 1);
qed "separation";

Addsimps [separation];

Goal "[| a:A;  P(a) |] ==> a : {x:A. P(x)}";
by (Asm_simp_tac 1);
qed "CollectI";

val prems = Goal
    "[| a : {x:A. P(x)};  [| a:A; P(a) |] ==> R |] ==> R";
by (rtac (separation RS iffD1 RS conjE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "CollectE";

Goal "a : {x:A. P(x)} ==> a:A";
by (etac CollectE 1);
by (assume_tac 1) ;
qed "CollectD1";

Goal "a : {x:A. P(x)} ==> P(a)";
by (etac CollectE 1);
by (assume_tac 1) ;
qed "CollectD2";

val prems= Goalw [Collect_def]  
    "[| A=B;  !!x. x:B ==> P(x) <-> Q(x) |] ==> Collect(A,P) = Collect(B,Q)";
by (simp_tac (simpset() addsimps prems) 1) ;
qed "Collect_cong";

AddSIs [CollectI];
AddSEs [CollectE];
Addcongs [Collect_cong];

(*** Rules for Unions ***)

Addsimps [Union_iff];

(*The order of the premises presupposes that C is rigid; A may be flexible*)
Goal "[| B: C;  A: B |] ==> A: Union(C)";
by (Simp_tac 1);
by (Blast_tac 1) ;
qed "UnionI";

val prems = Goal "[| A : Union(C);  !!B.[| A: B;  B: C |] ==> R |] ==> R";
by (resolve_tac [Union_iff RS iffD1 RS bexE] 1);
by (REPEAT (ares_tac prems 1)) ;
qed "UnionE";

(*** Rules for Unions of families ***)
(* UN x:A. B(x) abbreviates Union({B(x). x:A}) *)

Goalw [Bex_def] "b : (UN x:A. B(x)) <-> (EX x:A. b : B(x))";
by (Simp_tac 1);
by (Blast_tac 1) ;
qed "UN_iff";

Addsimps [UN_iff];

(*The order of the premises presupposes that A is rigid; b may be flexible*)
Goal "[| a: A;  b: B(a) |] ==> b: (UN x:A. B(x))";
by (Simp_tac 1);
by (Blast_tac 1) ;
qed "UN_I";

val major::prems= Goal
    "[| b : (UN x:A. B(x));  !!x.[| x: A;  b: B(x) |] ==> R |] ==> R";
by (rtac (major RS UnionE) 1);
by (REPEAT (eresolve_tac (prems@[asm_rl, RepFunE, subst]) 1)) ;
qed "UN_E";

val prems = Goal
    "[| A=B;  !!x. x:B ==> C(x)=D(x) |] ==> (UN x:A. C(x)) = (UN x:B. D(x))";
by (simp_tac (simpset() addsimps prems) 1) ;
qed "UN_cong";

(*No "Addcongs [UN_cong]" because UN is a combination of constants*)

(* UN_E appears before UnionE so that it is tried first, to avoid expensive
  calls to hyp_subst_tac.  Cannot include UN_I as it is unsafe: would enlarge
  the search space.*)
AddIs  [UnionI];  
AddSEs [UN_E];
AddSEs [UnionE];


(*** Rules for Inter ***)

(*Not obviously useful towards proving InterI, InterD, InterE*)
Goalw [Inter_def,Ball_def] 
    "A : Inter(C) <-> (ALL x:C. A: x) & (EX x. x:C)";
by (Simp_tac 1);
by (Blast_tac 1) ;
qed "Inter_iff";

(* Intersection is well-behaved only if the family is non-empty! *)
val prems = Goal
    "[| !!x. x: C ==> A: x;  EX c. c:C |] ==> A : Inter(C)";
by (simp_tac (simpset() addsimps [Inter_iff]) 1);
by (blast_tac (claset() addIs prems) 1) ;
qed "InterI";

(*A "destruct" rule -- every B in C contains A as an element, but
  A:B can hold when B:C does not!  This rule is analogous to "spec". *)
Goalw [Inter_def] "[| A : Inter(C);  B : C |] ==> A : B";
by (Blast_tac 1);
qed "InterD";

(*"Classical" elimination rule -- does not require exhibiting B:C *)
val major::prems= Goalw [Inter_def] 
    "[| A : Inter(C);  B~:C ==> R;  A:B ==> R |] ==> R";
by (rtac (major RS CollectD2 RS ballE) 1);
by (REPEAT (eresolve_tac prems 1)) ;
qed "InterE";

AddSIs [InterI];
AddEs  [InterD, InterE];

(*** Rules for Intersections of families ***)
(* INT x:A. B(x) abbreviates Inter({B(x). x:A}) *)

Goalw [Inter_def] "b : (INT x:A. B(x)) <-> (ALL x:A. b : B(x)) & (EX x. x:A)";
by (Simp_tac 1);
by (Best_tac 1) ;
qed "INT_iff";

val prems = Goal
    "[| !!x. x: A ==> b: B(x);  a: A |] ==> b: (INT x:A. B(x))";
by (blast_tac (claset() addIs prems) 1);
qed "INT_I";

Goal "[| b : (INT x:A. B(x));  a: A |] ==> b : B(a)";
by (Blast_tac 1);
qed "INT_E";

val prems = Goal
    "[| A=B;  !!x. x:B ==> C(x)=D(x) |] ==> (INT x:A. C(x)) = (INT x:B. D(x))";
by (simp_tac (simpset() addsimps prems) 1) ;
qed "INT_cong";

(*No "Addcongs [INT_cong]" because INT is a combination of constants*)


(*** Rules for Powersets ***)

Goal "A <= B ==> A : Pow(B)";
by (etac (Pow_iff RS iffD2) 1) ;
qed "PowI";

Goal "A : Pow(B)  ==>  A<=B";
by (etac (Pow_iff RS iffD1) 1) ;
qed "PowD";

AddSIs [PowI];
AddSDs [PowD];


(*** Rules for the empty set ***)

(*The set {x:0.False} is empty; by foundation it equals 0 
  See Suppes, page 21.*)
Goal "a ~: 0";
by (cut_facts_tac [foundation] 1);
by (best_tac (claset() addDs [equalityD2]) 1) ;
qed "not_mem_empty";

bind_thm ("emptyE", not_mem_empty RS notE);

Addsimps [not_mem_empty];
AddSEs [emptyE];

Goal "0 <= A";
by (Blast_tac 1);
qed "empty_subsetI";

Addsimps [empty_subsetI];

val prems = Goal "[| !!y. y:A ==> False |] ==> A=0";
by (blast_tac (claset() addDs prems) 1) ;
qed "equals0I";

Goal "A=0 ==> a ~: A";
by (Blast_tac 1);
qed "equals0D";

AddDs [equals0D, sym RS equals0D];

Goal "a:A ==> A ~= 0";
by (Blast_tac 1);
qed "not_emptyI";

val [major,minor]= Goal "[| A ~= 0;  !!x. x:A ==> R |] ==> R";
by (rtac ([major, equals0I] MRS swap) 1);
by (swap_res_tac [minor] 1);
by (assume_tac 1) ;
qed "not_emptyE";


(*** Cantor's Theorem: There is no surjection from a set to its powerset. ***)

val cantor_cs = FOL_cs   (*precisely the rules needed for the proof*)
  addSIs [ballI, CollectI, PowI, subsetI] addIs [bexI]
  addSEs [CollectE, equalityCE];

(*The search is undirected; similar proof attempts may fail.
  b represents ANY map, such as (lam x:A.b(x)): A->Pow(A). *)
Goal "EX S: Pow(A). ALL x:A. b(x) ~= S";
by (best_tac cantor_cs 1);
qed "cantor";

(*Lemma for the inductive definition in theory Zorn*)
Goal "Y : Pow(Pow(A)) ==> Union(Y) : Pow(A)";
by (Blast_tac 1);
qed "Union_in_Pow";

Goal "(!!x. x:A ==> P(x)) == Trueprop (ALL x:A. P(x))";
by (simp_tac (simpset () addsimps [Ball_def, thm "atomize_all", thm "atomize_imp"]) 1);
qed "atomize_ball";
