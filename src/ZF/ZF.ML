(*  Title:      ZF/ZF.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1994  University of Cambridge

Basic introduction and elimination rules for Zermelo-Fraenkel Set Theory 
*)

open ZF;

(*Useful examples:  singletonI RS subst_elem,  subst_elem RSN (2,IntI) *)
goal ZF.thy "!!a b A. [| b:A;  a=b |] ==> a:A";
by (etac ssubst 1);
by (assume_tac 1);
val subst_elem = result();


(*** Bounded universal quantifier ***)

qed_goalw "ballI" ZF.thy [Ball_def]
    "[| !!x. x:A ==> P(x) |] ==> ALL x:A. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [allI,impI]) 1)) ]);

qed_goalw "bspec" ZF.thy [Ball_def]
    "[| ALL x:A. P(x);  x: A |] ==> P(x)"
 (fn major::prems=>
  [ (rtac (major RS spec RS mp) 1),
    (resolve_tac prems 1) ]);

qed_goalw "ballE" ZF.thy [Ball_def]
    "[| ALL x:A. P(x);  P(x) ==> Q;  x~:A ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS allE) 1),
    (REPEAT (eresolve_tac (prems@[asm_rl,impCE]) 1)) ]);

(*Used in the datatype package*)
qed_goal "rev_bspec" ZF.thy
    "!!x A P. [| x: A;  ALL x:A. P(x) |] ==> P(x)"
 (fn _ =>
  [ REPEAT (ares_tac [bspec] 1) ]);

(*Instantiates x first: better for automatic theorem proving?*)
qed_goal "rev_ballE" ZF.thy
    "[| ALL x:A. P(x);  x~:A ==> Q;  P(x) ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS ballE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

AddSIs [ballI];
AddEs  [rev_ballE];

(*Takes assumptions ALL x:A.P(x) and a:A; creates assumption P(a)*)
val ball_tac = dtac bspec THEN' assume_tac;

(*Trival rewrite rule;   (ALL x:A.P)<->P holds only if A is nonempty!*)
qed_goal "ball_triv" ZF.thy "(ALL x:A. P) <-> ((EX x. x:A) --> P)"
 (fn _=> [ simp_tac (simpset() addsimps [Ball_def]) 1 ]);
Addsimps [ball_triv];

(*Congruence rule for rewriting*)
qed_goalw "ball_cong" ZF.thy [Ball_def]
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) |] ==> Ball(A,P) <-> Ball(A',P')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems) 1) ]);

(*** Bounded existential quantifier ***)

qed_goalw "bexI" ZF.thy [Bex_def]
    "!!P. [| P(x);  x: A |] ==> EX x:A. P(x)"
 (fn _=> [ Blast_tac 1 ]);

(*Not of the general form for such rules; ~EX has become ALL~ *)
qed_goal "bexCI" ZF.thy 
   "[| ALL x:A. ~P(x) ==> P(a);  a: A |] ==> EX x:A. P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[bexI,ballI,notI,notE]) 1)) ]);

qed_goalw "bexE" ZF.thy [Bex_def]
    "[| EX x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q \
\    |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS exE) 1),
    (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1)) ]);

AddIs  [bexI];  
AddSEs [bexE];

(*We do not even have (EX x:A. True) <-> True unless A is nonempty!!*)
qed_goal  "bex_triv" ZF.thy "(EX x:A. P) <-> ((EX x. x:A) & P)"
 (fn _=> [ simp_tac (simpset() addsimps [Bex_def]) 1 ]);
Addsimps [bex_triv];

qed_goalw "bex_cong" ZF.thy [Bex_def]
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) \
\    |] ==> Bex(A,P) <-> Bex(A',P')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems addcongs [conj_cong]) 1) ]);

Addcongs [ball_cong, bex_cong];


(*** Rules for subsets ***)

qed_goalw "subsetI" ZF.thy [subset_def]
    "(!!x. x:A ==> x:B) ==> A <= B"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [ballI]) 1)) ]);

(*Rule in Modus Ponens style [was called subsetE] *)
qed_goalw "subsetD" ZF.thy [subset_def] "[| A <= B;  c:A |] ==> c:B"
 (fn major::prems=>
  [ (rtac (major RS bspec) 1),
    (resolve_tac prems 1) ]);

(*Classical elimination rule*)
qed_goalw "subsetCE" ZF.thy [subset_def]
    "[| A <= B;  c~:A ==> P;  c:B ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS ballE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

AddSIs [subsetI];
AddEs  [subsetCE, subsetD];


(*Takes assumptions A<=B; c:A and creates the assumption c:B *)
val set_mp_tac = dtac subsetD THEN' assume_tac;

(*Sometimes useful with premises in this order*)
qed_goal "rev_subsetD" ZF.thy "!!A B c. [| c:A; A<=B |] ==> c:B"
 (fn _=> [ Blast_tac 1 ]);

qed_goal "contra_subsetD" ZF.thy "!!c. [| A <= B; c ~: B |] ==> c ~: A"
 (fn _=> [ Blast_tac 1 ]);

qed_goal "rev_contra_subsetD" ZF.thy "!!c. [| c ~: B;  A <= B |] ==> c ~: A"
 (fn _=> [ Blast_tac 1 ]);

qed_goal "subset_refl" ZF.thy "A <= A"
 (fn _=> [ Blast_tac 1 ]);

Addsimps [subset_refl];

qed_goal "subset_trans" ZF.thy "!!A B C. [| A<=B;  B<=C |] ==> A<=C"
 (fn _=> [ Blast_tac 1 ]);

(*Useful for proving A<=B by rewriting in some cases*)
qed_goalw "subset_iff" ZF.thy [subset_def,Ball_def]
     "A<=B <-> (ALL x. x:A --> x:B)"
 (fn _=> [ (rtac iff_refl 1) ]);


(*** Rules for equality ***)

(*Anti-symmetry of the subset relation*)
qed_goal "equalityI" ZF.thy "[| A <= B;  B <= A |] ==> A = B"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[conjI, extension RS iffD2]) 1)) ]);

AddIs [equalityI];

qed_goal "equality_iffI" ZF.thy "(!!x. x:A <-> x:B) ==> A = B"
 (fn [prem] =>
  [ (rtac equalityI 1),
    (REPEAT (ares_tac [subsetI, prem RS iffD1, prem RS iffD2] 1)) ]);

bind_thm ("equalityD1", extension RS iffD1 RS conjunct1);
bind_thm ("equalityD2", extension RS iffD1 RS conjunct2);

qed_goal "equalityE" ZF.thy
    "[| A = B;  [| A<=B; B<=A |] ==> P |]  ==>  P"
 (fn prems=>
  [ (DEPTH_SOLVE (resolve_tac (prems@[equalityD1,equalityD2]) 1)) ]);

qed_goal "equalityCE" ZF.thy
    "[| A = B;  [| c:A; c:B |] ==> P;  [| c~:A; c~:B |] ==> P |]  ==>  P"
 (fn major::prems=>
  [ (rtac (major RS equalityE) 1),
    (REPEAT (contr_tac 1 ORELSE eresolve_tac ([asm_rl,subsetCE]@prems) 1)) ]);

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. 
  Would it be better to do subgoal_tac "ALL z. p = f(z) --> R(z)" ??*)
qed_goal "setup_induction" ZF.thy
    "[| p: A;  !!z. z: A ==> p=z --> R |] ==> R"
 (fn prems=>
  [ (rtac mp 1),
    (REPEAT (resolve_tac (refl::prems) 1)) ]);


(*** Rules for Replace -- the derived form of replacement ***)

qed_goalw "Replace_iff" ZF.thy [Replace_def]
    "b : {y. x:A, P(x,y)}  <->  (EX x:A. P(x,b) & (ALL y. P(x,y) --> y=b))"
 (fn _=>
  [ (rtac (replacement RS iff_trans) 1),
    (REPEAT (ares_tac [refl,bex_cong,iffI,ballI,allI,conjI,impI,ex1I] 1
        ORELSE eresolve_tac [conjE, spec RS mp, ex1_functional] 1)) ]);

(*Introduction; there must be a unique y such that P(x,y), namely y=b. *)
qed_goal "ReplaceI" ZF.thy
    "[| P(x,b);  x: A;  !!y. P(x,y) ==> y=b |] ==> \
\    b : {y. x:A, P(x,y)}"
 (fn prems=>
  [ (rtac (Replace_iff RS iffD2) 1),
    (REPEAT (ares_tac (prems@[bexI,conjI,allI,impI]) 1)) ]);

(*Elimination; may asssume there is a unique y such that P(x,y), namely y=b. *)
qed_goal "ReplaceE" ZF.thy 
    "[| b : {y. x:A, P(x,y)};  \
\       !!x. [| x: A;  P(x,b);  ALL y. P(x,y)-->y=b |] ==> R \
\    |] ==> R"
 (fn prems=>
  [ (rtac (Replace_iff RS iffD1 RS bexE) 1),
    (etac conjE 2),
    (REPEAT (ares_tac prems 1)) ]);

(*As above but without the (generally useless) 3rd assumption*)
qed_goal "ReplaceE2" ZF.thy 
    "[| b : {y. x:A, P(x,y)};  \
\       !!x. [| x: A;  P(x,b) |] ==> R \
\    |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (ares_tac prems 1)) ]);

AddIs  [ReplaceI];  
AddSEs [ReplaceE2];

qed_goal "Replace_cong" ZF.thy
    "[| A=B;  !!x y. x:B ==> P(x,y) <-> Q(x,y) |] ==> \
\    Replace(A,P) = Replace(B,Q)"
 (fn prems=>
   let val substprems = prems RL [subst, ssubst]
       and iffprems = prems RL [iffD1,iffD2]
   in [ (rtac equalityI 1),
        (REPEAT (eresolve_tac (substprems@[asm_rl, ReplaceE, spec RS mp]) 1
         ORELSE resolve_tac [subsetI, ReplaceI] 1
         ORELSE (resolve_tac iffprems 1 THEN assume_tac 2))) ]
   end);

Addcongs [Replace_cong];

(*** Rules for RepFun ***)

qed_goalw "RepFunI" ZF.thy [RepFun_def]
    "!!a A. a : A ==> f(a) : {f(x). x:A}"
 (fn _ => [ (REPEAT (ares_tac [ReplaceI,refl] 1)) ]);

(*Useful for coinduction proofs*)
qed_goal "RepFun_eqI" ZF.thy
    "!!b a f. [| b=f(a);  a : A |] ==> b : {f(x). x:A}"
 (fn _ => [ etac ssubst 1, etac RepFunI 1 ]);

qed_goalw "RepFunE" ZF.thy [RepFun_def]
    "[| b : {f(x). x:A};  \
\       !!x.[| x:A;  b=f(x) |] ==> P |] ==> \
\    P"
 (fn major::prems=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (ares_tac prems 1)) ]);

AddIs  [RepFun_eqI];  
AddSEs [RepFunE];

qed_goalw "RepFun_cong" ZF.thy [RepFun_def]
    "[| A=B;  !!x. x:B ==> f(x)=g(x) |] ==> RepFun(A,f) = RepFun(B,g)"
 (fn prems=> [ (simp_tac (simpset() addsimps prems) 1) ]);

Addcongs [RepFun_cong];

qed_goalw "RepFun_iff" ZF.thy [Bex_def]
    "b : {f(x). x:A} <-> (EX x:A. b=f(x))"
 (fn _ => [Blast_tac 1]);

goal ZF.thy "{x. x:A} = A";
by (Blast_tac 1);
qed "triv_RepFun";

Addsimps [RepFun_iff, triv_RepFun];

(*** Rules for Collect -- forming a subset by separation ***)

(*Separation is derivable from Replacement*)
qed_goalw "separation" ZF.thy [Collect_def]
    "a : {x:A. P(x)} <-> a:A & P(a)"
 (fn _=> [Blast_tac 1]);

Addsimps [separation];

qed_goal "CollectI" ZF.thy
    "!!P. [| a:A;  P(a) |] ==> a : {x:A. P(x)}"
 (fn _=> [ Asm_simp_tac 1 ]);

qed_goal "CollectE" ZF.thy
    "[| a : {x:A. P(x)};  [| a:A; P(a) |] ==> R |] ==> R"
 (fn prems=>
  [ (rtac (separation RS iffD1 RS conjE) 1),
    (REPEAT (ares_tac prems 1)) ]);

qed_goal "CollectD1" ZF.thy "!!P. a : {x:A. P(x)} ==> a:A"
 (fn _=> [ (etac CollectE 1), (assume_tac 1) ]);

qed_goal "CollectD2" ZF.thy "!!P. a : {x:A. P(x)} ==> P(a)"
 (fn _=> [ (etac CollectE 1), (assume_tac 1) ]);

qed_goalw "Collect_cong" ZF.thy [Collect_def] 
    "[| A=B;  !!x. x:B ==> P(x) <-> Q(x) |] ==> Collect(A,P) = Collect(B,Q)"
 (fn prems=> [ (simp_tac (simpset() addsimps prems) 1) ]);

AddSIs [CollectI];
AddSEs [CollectE];
Addcongs [Collect_cong];

(*** Rules for Unions ***)

Addsimps [Union_iff];

(*The order of the premises presupposes that C is rigid; A may be flexible*)
qed_goal "UnionI" ZF.thy "!!C. [| B: C;  A: B |] ==> A: Union(C)"
 (fn _=> [ Simp_tac 1, Blast_tac 1 ]);

qed_goal "UnionE" ZF.thy
    "[| A : Union(C);  !!B.[| A: B;  B: C |] ==> R |] ==> R"
 (fn prems=>
  [ (resolve_tac [Union_iff RS iffD1 RS bexE] 1),
    (REPEAT (ares_tac prems 1)) ]);

(*** Rules for Unions of families ***)
(* UN x:A. B(x) abbreviates Union({B(x). x:A}) *)

qed_goalw "UN_iff" ZF.thy [Bex_def]
    "b : (UN x:A. B(x)) <-> (EX x:A. b : B(x))"
 (fn _=> [ Simp_tac 1, Blast_tac 1 ]);

Addsimps [UN_iff];

(*The order of the premises presupposes that A is rigid; b may be flexible*)
qed_goal "UN_I" ZF.thy "!!A B. [| a: A;  b: B(a) |] ==> b: (UN x:A. B(x))"
 (fn _=> [ Simp_tac 1, Blast_tac 1 ]);

qed_goal "UN_E" ZF.thy
    "[| b : (UN x:A. B(x));  !!x.[| x: A;  b: B(x) |] ==> R |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS UnionE) 1),
    (REPEAT (eresolve_tac (prems@[asm_rl, RepFunE, subst]) 1)) ]);

qed_goal "UN_cong" ZF.thy
    "[| A=B;  !!x. x:B ==> C(x)=D(x) |] ==> (UN x:A. C(x)) = (UN x:B. D(x))"
 (fn prems=> [ (simp_tac (simpset() addsimps prems) 1) ]);

(*No "Addcongs [UN_cong]" because UN is a combination of constants*)

(* UN_E appears before UnionE so that it is tried first, to avoid expensive
  calls to hyp_subst_tac.  Cannot include UN_I as it is unsafe: would enlarge
  the search space.*)
AddIs  [UnionI];  
AddSEs [UN_E];
AddSEs [UnionE];


(*** Rules for Inter ***)

(*Not obviously useful towards proving InterI, InterD, InterE*)
qed_goalw "Inter_iff" ZF.thy [Inter_def,Ball_def]
    "A : Inter(C) <-> (ALL x:C. A: x) & (EX x. x:C)"
 (fn _=> [ Simp_tac 1, Blast_tac 1 ]);

(* Intersection is well-behaved only if the family is non-empty! *)
qed_goal "InterI" ZF.thy
    "[| !!x. x: C ==> A: x;  EX c. c:C |] ==> A : Inter(C)"
 (fn prems=> [ (simp_tac (simpset() addsimps [Inter_iff]) 1), 
	       blast_tac (claset() addIs prems) 1 ]);

(*A "destruct" rule -- every B in C contains A as an element, but
  A:B can hold when B:C does not!  This rule is analogous to "spec". *)
qed_goalw "InterD" ZF.thy [Inter_def]
    "!!C. [| A : Inter(C);  B : C |] ==> A : B"
 (fn _=> [ Blast_tac 1 ]);

(*"Classical" elimination rule -- does not require exhibiting B:C *)
qed_goalw "InterE" ZF.thy [Inter_def]
    "[| A : Inter(C);  B~:C ==> R;  A:B ==> R |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS CollectD2 RS ballE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

AddSIs [InterI];
AddEs  [InterD, InterE];

(*** Rules for Intersections of families ***)
(* INT x:A. B(x) abbreviates Inter({B(x). x:A}) *)

qed_goalw "INT_iff" ZF.thy [Inter_def]
    "b : (INT x:A. B(x)) <-> (ALL x:A. b : B(x)) & (EX x. x:A)"
 (fn _=> [ Simp_tac 1, Best_tac 1 ]);

qed_goal "INT_I" ZF.thy
    "[| !!x. x: A ==> b: B(x);  a: A |] ==> b: (INT x:A. B(x))"
 (fn prems=> [ blast_tac (claset() addIs prems) 1 ]);

qed_goal "INT_E" ZF.thy
    "[| b : (INT x:A. B(x));  a: A |] ==> b : B(a)"
 (fn [major,minor]=>
  [ (rtac (major RS InterD) 1),
    (rtac (minor RS RepFunI) 1) ]);

qed_goal "INT_cong" ZF.thy
    "[| A=B;  !!x. x:B ==> C(x)=D(x) |] ==> (INT x:A. C(x)) = (INT x:B. D(x))"
 (fn prems=> [ (simp_tac (simpset() addsimps prems) 1) ]);

(*No "Addcongs [INT_cong]" because INT is a combination of constants*)


(*** Rules for Powersets ***)

qed_goal "PowI" ZF.thy "A <= B ==> A : Pow(B)"
 (fn [prem]=> [ (rtac (prem RS (Pow_iff RS iffD2)) 1) ]);

qed_goal "PowD" ZF.thy "A : Pow(B)  ==>  A<=B"
 (fn [major]=> [ (rtac (major RS (Pow_iff RS iffD1)) 1) ]);

AddSIs [PowI];
AddSDs [PowD];


(*** Rules for the empty set ***)

(*The set {x:0.False} is empty; by foundation it equals 0 
  See Suppes, page 21.*)
qed_goal "not_mem_empty" ZF.thy "a ~: 0"
 (fn _=>
  [ (cut_facts_tac [foundation] 1), 
    (best_tac (claset() addDs [equalityD2]) 1) ]);

bind_thm ("emptyE", not_mem_empty RS notE);

Addsimps [not_mem_empty];
AddSEs [emptyE];

qed_goal "empty_subsetI" ZF.thy "0 <= A"
 (fn _=> [ Blast_tac 1 ]);

Addsimps [empty_subsetI];

qed_goal "equals0I" ZF.thy "[| !!y. y:A ==> False |] ==> A=0"
 (fn prems=> [ blast_tac (claset() addDs prems) 1 ]);

qed_goal "equals0D" ZF.thy "!!P. [| A=0;  a:A |] ==> P"
 (fn _=> [ Full_simp_tac 1, Blast_tac 1 ]);

qed_goal "not_emptyI" ZF.thy "!!A a. a:A ==> A ~= 0"
 (fn _=> [ Blast_tac 1 ]);

qed_goal "not_emptyE" ZF.thy "[| A ~= 0;  !!x. x:A ==> R |] ==> R"
 (fn [major,minor]=>
  [ rtac ([major, equals0I] MRS swap) 1,
    swap_res_tac [minor] 1,
    assume_tac 1 ]);


(*** Cantor's Theorem: There is no surjection from a set to its powerset. ***)

val cantor_cs = FOL_cs   (*precisely the rules needed for the proof*)
  addSIs [ballI, CollectI, PowI, subsetI] addIs [bexI]
  addSEs [CollectE, equalityCE];

(*The search is undirected; similar proof attempts may fail.
  b represents ANY map, such as (lam x:A.b(x)): A->Pow(A). *)
qed_goal "cantor" ZF.thy "EX S: Pow(A). ALL x:A. b(x) ~= S"
 (fn _ => [best_tac cantor_cs 1]);

(*Lemma for the inductive definition in Zorn.thy*)
qed_goal "Union_in_Pow" ZF.thy
    "!!Y. Y : Pow(Pow(A)) ==> Union(Y) : Pow(A)"
 (fn _ => [Blast_tac 1]);

