(*  Title: 	set/set
    ID:         $Id$

For set.thy.

Modified version of
    Title: 	HOL/set
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For set.thy.  Set theory for higher-order logic.  A set is simply a predicate.
*)

open Set;

val [prem] = goal Set.thy "[| P(a) |] ==> a : {x.P(x)}";
by (rtac (mem_Collect_iff RS iffD2) 1);
by (rtac prem 1);
val CollectI = result();

val prems = goal Set.thy "[| a : {x.P(x)} |] ==> P(a)";
by (resolve_tac (prems RL [mem_Collect_iff  RS iffD1]) 1);
val CollectD = result();

val [prem] = goal Set.thy "[| !!x. x:A <-> x:B |] ==> A = B";
by (rtac (set_extension RS iffD2) 1);
by (rtac (prem RS allI) 1);
val set_ext = result();

val prems = goal Set.thy "[| !!x. P(x) <-> Q(x) |] ==> {x. P(x)} = {x. Q(x)}";
by (REPEAT (ares_tac [set_ext,iffI,CollectI] 1 ORELSE
            eresolve_tac ([CollectD] RL (prems RL [iffD1,iffD2])) 1));
val Collect_cong = result();

val CollectE = make_elim CollectD;

(*** Bounded quantifiers ***)

val prems = goalw Set.thy [Ball_def]
    "[| !!x. x:A ==> P(x) |] ==> ALL x:A. P(x)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
val ballI = result();

val [major,minor] = goalw Set.thy [Ball_def]
    "[| ALL x:A. P(x);  x:A |] ==> P(x)";
by (rtac (minor RS (major RS spec RS mp)) 1);
val bspec = result();

val major::prems = goalw Set.thy [Ball_def]
    "[| ALL x:A. P(x);  P(x) ==> Q;  ~ x:A ==> Q |] ==> Q";
by (rtac (major RS spec RS impCE) 1);
by (REPEAT (eresolve_tac prems 1));
val ballE = result();

(*Takes assumptions ALL x:A.P(x) and a:A; creates assumption P(a)*)
fun ball_tac i = etac ballE i THEN contr_tac (i+1);

val prems = goalw Set.thy [Bex_def]
    "[| P(x);  x:A |] ==> EX x:A. P(x)";
by (REPEAT (ares_tac (prems @ [exI,conjI]) 1));
val bexI = result();

val bexCI = prove_goal Set.thy 
   "[| EX x:A. ~P(x) ==> P(a);  a:A |] ==> EX x:A.P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[bexI,ballI,notI,notE]) 1))  ]);

val major::prems = goalw Set.thy [Bex_def]
    "[| EX x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q  |] ==> Q";
by (rtac (major RS exE) 1);
by (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1));
val bexE = result();

(*Trival rewrite rule;   (! x:A.P)=P holds only if A is nonempty!*)
val prems = goal Set.thy
    "(ALL x:A. True) <-> True";
by (REPEAT (ares_tac [TrueI,ballI,iffI] 1));
val ball_rew = result();

(** Congruence rules **)

val prems = goal Set.thy
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) |] ==> \
\    (ALL x:A. P(x)) <-> (ALL x:A'. P'(x))";
by (resolve_tac (prems RL [ssubst,iffD2]) 1);
by (REPEAT (ares_tac [ballI,iffI] 1
     ORELSE eresolve_tac ([make_elim bspec, mp] @ (prems RL [iffE])) 1));
val ball_cong = result();

val prems = goal Set.thy
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) |] ==> \
\    (EX x:A. P(x)) <-> (EX x:A'. P'(x))";
by (resolve_tac (prems RL [ssubst,iffD2]) 1);
by (REPEAT (etac bexE 1
     ORELSE ares_tac ([bexI,iffI] @ (prems RL [iffD1,iffD2])) 1));
val bex_cong = result();

(*** Rules for subsets ***)

val prems = goalw Set.thy [subset_def] "(!!x.x:A ==> x:B) ==> A <= B";
by (REPEAT (ares_tac (prems @ [ballI]) 1));
val subsetI = result();

(*Rule in Modus Ponens style*)
val major::prems = goalw Set.thy [subset_def] "[| A <= B;  c:A |] ==> c:B";
by (rtac (major RS bspec) 1);
by (resolve_tac prems 1);
val subsetD = result();

(*Classical elimination rule*)
val major::prems = goalw Set.thy [subset_def] 
    "[| A <= B;  ~(c:A) ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
val subsetCE = result();

(*Takes assumptions A<=B; c:A and creates the assumption c:B *)
fun set_mp_tac i = etac subsetCE i  THEN  mp_tac i;

val subset_refl = prove_goal Set.thy "A <= A"
 (fn _=> [ (REPEAT (ares_tac [subsetI] 1)) ]);

goal Set.thy "!!A B C. [| A<=B;  B<=C |] ==> A<=C";
br subsetI 1;
by (REPEAT (eresolve_tac [asm_rl, subsetD] 1));
val subset_trans = result();


(*** Rules for equality ***)

(*Anti-symmetry of the subset relation*)
val prems = goal Set.thy "[| A <= B;  B <= A |] ==> A = B";
by (rtac (iffI RS set_ext) 1);
by (REPEAT (ares_tac (prems RL [subsetD]) 1));
val subset_antisym = result();
val equalityI = subset_antisym;

(* Equality rules from ZF set theory -- are they appropriate here? *)
val prems = goal Set.thy "A = B ==> A<=B";
by (resolve_tac (prems RL [subst]) 1);
by (rtac subset_refl 1);
val equalityD1 = result();

val prems = goal Set.thy "A = B ==> B<=A";
by (resolve_tac (prems RL [subst]) 1);
by (rtac subset_refl 1);
val equalityD2 = result();

val prems = goal Set.thy
    "[| A = B;  [| A<=B; B<=A |] ==> P |]  ==>  P";
by (resolve_tac prems 1);
by (REPEAT (resolve_tac (prems RL [equalityD1,equalityD2]) 1));
val equalityE = result();

val major::prems = goal Set.thy
    "[| A = B;  [| c:A; c:B |] ==> P;  [| ~ c:A; ~ c:B |] ==> P |]  ==>  P";
by (rtac (major RS equalityE) 1);
by (REPEAT (contr_tac 1 ORELSE eresolve_tac ([asm_rl,subsetCE]@prems) 1));
val equalityCE = result();

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. *)
val prems = goal Set.thy 
    "[| p:A;  !!z. z:A ==> p=z --> R |] ==> R";
by (rtac mp 1);
by (REPEAT (resolve_tac (refl::prems) 1));
val setup_induction = result();

goal Set.thy "{x.x:A} = A";
by (REPEAT (ares_tac [equalityI,subsetI,CollectI] 1  ORELSE eresolve_tac [CollectD] 1));
val trivial_set = result();

(*** Rules for binary union -- Un ***)

val prems = goalw Set.thy [Un_def] "c:A ==> c : A Un B";
by (REPEAT (resolve_tac (prems @ [CollectI,disjI1]) 1));
val UnI1 = result();

val prems = goalw Set.thy [Un_def] "c:B ==> c : A Un B";
by (REPEAT (resolve_tac (prems @ [CollectI,disjI2]) 1));
val UnI2 = result();

(*Classical introduction rule: no commitment to A vs B*)
val UnCI = prove_goal Set.thy "(~c:B ==> c:A) ==> c : A Un B"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[UnI1,notI]) 1)),
    (REPEAT (ares_tac (prems@[UnI2,notE]) 1)) ]);

val major::prems = goalw Set.thy [Un_def]
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS CollectD RS disjE) 1);
by (REPEAT (eresolve_tac prems 1));
val UnE = result();


(*** Rules for small intersection -- Int ***)

val prems = goalw Set.thy [Int_def]
    "[| c:A;  c:B |] ==> c : A Int B";
by (REPEAT (resolve_tac (prems @ [CollectI,conjI]) 1));
val IntI = result();

val [major] = goalw Set.thy [Int_def] "c : A Int B ==> c:A";
by (rtac (major RS CollectD RS conjunct1) 1);
val IntD1 = result();

val [major] = goalw Set.thy [Int_def] "c : A Int B ==> c:B";
by (rtac (major RS CollectD RS conjunct2) 1);
val IntD2 = result();

val [major,minor] = goal Set.thy
    "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P";
by (rtac minor 1);
by (rtac (major RS IntD1) 1);
by (rtac (major RS IntD2) 1);
val IntE = result();


(*** Rules for set complement -- Compl ***)

val prems = goalw Set.thy [Compl_def]
    "[| c:A ==> False |] ==> c : Compl(A)";
by (REPEAT (ares_tac (prems @ [CollectI,notI]) 1));
val ComplI = result();

(*This form, with negated conclusion, works well with the Classical prover.
  Negated assumptions behave like formulae on the right side of the notional
  turnstile...*)
val major::prems = goalw Set.thy [Compl_def]
    "[| c : Compl(A) |] ==> ~c:A";
by (rtac (major RS CollectD) 1);
val ComplD = result();

val ComplE = make_elim ComplD;


(*** Empty sets ***)

goalw Set.thy [empty_def] "{x.False} = {}";
br refl 1;
val empty_eq = result();

val [prem] = goalw Set.thy [empty_def] "a : {} ==> P";
by (rtac (prem RS CollectD RS FalseE) 1);
val emptyD = result();

val emptyE = make_elim emptyD;

val [prem] = goal Set.thy "~ A={} ==> (EX x.x:A)";
br (prem RS swap) 1;
br equalityI 1;
by (ALLGOALS (fast_tac (FOL_cs addSIs [subsetI] addSEs [emptyD])));
val not_emptyD = result();

(*** Singleton sets ***)

goalw Set.thy [singleton_def] "a : {a}";
by (rtac CollectI 1);
by (rtac refl 1);
val singletonI = result();

val [major] = goalw Set.thy [singleton_def] "b : {a} ==> b=a"; 
by (rtac (major RS CollectD) 1);
val singletonD = result();

val singletonE = make_elim singletonD;

(*** Unions of families ***)

(*The order of the premises presupposes that A is rigid; b may be flexible*)
val prems = goalw Set.thy [UNION_def]
    "[| a:A;  b: B(a) |] ==> b: (UN x:A. B(x))";
by (REPEAT (resolve_tac (prems @ [bexI,CollectI]) 1));
val UN_I = result();

val major::prems = goalw Set.thy [UNION_def]
    "[| b : (UN x:A. B(x));  !!x.[| x:A;  b: B(x) |] ==> R |] ==> R";
by (rtac (major RS CollectD RS bexE) 1);
by (REPEAT (ares_tac prems 1));
val UN_E = result();

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (UN x:A. C(x)) = (UN x:B. D(x))";
by (REPEAT (etac UN_E 1
     ORELSE ares_tac ([UN_I,equalityI,subsetI] @ 
		      (prems RL [equalityD1,equalityD2] RL [subsetD])) 1));
val UN_cong = result();

(*** Intersections of families -- INTER x:A. B(x) is Inter(B)``A ) *)

val prems = goalw Set.thy [INTER_def]
    "(!!x. x:A ==> b: B(x)) ==> b : (INT x:A. B(x))";
by (REPEAT (ares_tac ([CollectI,ballI] @ prems) 1));
val INT_I = result();

val major::prems = goalw Set.thy [INTER_def]
    "[| b : (INT x:A. B(x));  a:A |] ==> b: B(a)";
by (rtac (major RS CollectD RS bspec) 1);
by (resolve_tac prems 1);
val INT_D = result();

(*"Classical" elimination rule -- does not require proving X:C *)
val major::prems = goalw Set.thy [INTER_def]
    "[| b : (INT x:A. B(x));  b: B(a) ==> R;  ~ a:A ==> R |] ==> R";
by (rtac (major RS CollectD RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
val INT_E = result();

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (INT x:A. C(x)) = (INT x:B. D(x))";
by (REPEAT_FIRST (resolve_tac [INT_I,equalityI,subsetI]));
by (REPEAT (dtac INT_D 1
     ORELSE ares_tac (prems RL [equalityD1,equalityD2] RL [subsetD]) 1));
val INT_cong = result();

(*** Rules for Unions ***)

(*The order of the premises presupposes that C is rigid; A may be flexible*)
val prems = goalw Set.thy [Union_def]
    "[| X:C;  A:X |] ==> A : Union(C)";
by (REPEAT (resolve_tac (prems @ [UN_I]) 1));
val UnionI = result();

val major::prems = goalw Set.thy [Union_def]
    "[| A : Union(C);  !!X.[| A:X;  X:C |] ==> R |] ==> R";
by (rtac (major RS UN_E) 1);
by (REPEAT (ares_tac prems 1));
val UnionE = result();

(*** Rules for Inter ***)

val prems = goalw Set.thy [Inter_def]
    "[| !!X. X:C ==> A:X |] ==> A : Inter(C)";
by (REPEAT (ares_tac ([INT_I] @ prems) 1));
val InterI = result();

(*A "destruct" rule -- every X in C contains A as an element, but
  A:X can hold when X:C does not!  This rule is analogous to "spec". *)
val major::prems = goalw Set.thy [Inter_def]
    "[| A : Inter(C);  X:C |] ==> A:X";
by (rtac (major RS INT_D) 1);
by (resolve_tac prems 1);
val InterD = result();

(*"Classical" elimination rule -- does not require proving X:C *)
val major::prems = goalw Set.thy [Inter_def]
    "[| A : Inter(C);  A:X ==> R;  ~ X:C ==> R |] ==> R";
by (rtac (major RS INT_E) 1);
by (REPEAT (eresolve_tac prems 1));
val InterE = result();
