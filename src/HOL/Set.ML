(*  Title:      HOL/set
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For set.thy.  Set theory for higher-order logic.  A set is simply a predicate.
*)

open Set;

val [prem] = goal Set.thy "[| P(a) |] ==> a : {x.P(x)}";
by (rtac (mem_Collect_eq RS ssubst) 1);
by (rtac prem 1);
qed "CollectI";

val prems = goal Set.thy "[| a : {x.P(x)} |] ==> P(a)";
by (resolve_tac (prems RL [mem_Collect_eq  RS subst]) 1);
qed "CollectD";

val [prem] = goal Set.thy "[| !!x. (x:A) = (x:B) |] ==> A = B";
by (rtac (prem RS ext RS arg_cong RS box_equals) 1);
by (rtac Collect_mem_eq 1);
by (rtac Collect_mem_eq 1);
qed "set_ext";

val [prem] = goal Set.thy "[| !!x. P(x)=Q(x) |] ==> {x. P(x)} = {x. Q(x)}";
by (rtac (prem RS ext RS arg_cong) 1);
qed "Collect_cong";

val CollectE = make_elim CollectD;

(*** Bounded quantifiers ***)

val prems = goalw Set.thy [Ball_def]
    "[| !!x. x:A ==> P(x) |] ==> ! x:A. P(x)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
qed "ballI";

val [major,minor] = goalw Set.thy [Ball_def]
    "[| ! x:A. P(x);  x:A |] ==> P(x)";
by (rtac (minor RS (major RS spec RS mp)) 1);
qed "bspec";

val major::prems = goalw Set.thy [Ball_def]
    "[| ! x:A. P(x);  P(x) ==> Q;  x~:A ==> Q |] ==> Q";
by (rtac (major RS spec RS impCE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "ballE";

(*Takes assumptions ! x:A.P(x) and a:A; creates assumption P(a)*)
fun ball_tac i = etac ballE i THEN contr_tac (i+1);

val prems = goalw Set.thy [Bex_def]
    "[| P(x);  x:A |] ==> ? x:A. P(x)";
by (REPEAT (ares_tac (prems @ [exI,conjI]) 1));
qed "bexI";

qed_goal "bexCI" Set.thy 
   "[| ! x:A. ~P(x) ==> P(a);  a:A |] ==> ? x:A.P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[bexI,ballI,notI,notE]) 1))  ]);

val major::prems = goalw Set.thy [Bex_def]
    "[| ? x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q  |] ==> Q";
by (rtac (major RS exE) 1);
by (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1));
qed "bexE";

(*Trival rewrite rule;   (! x:A.P)=P holds only if A is nonempty!*)
val prems = goal Set.thy
    "(! x:A. True) = True";
by (REPEAT (ares_tac [TrueI,ballI,iffI] 1));
qed "ball_rew";

(** Congruence rules **)

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> P(x) = Q(x) |] ==> \
\    (! x:A. P(x)) = (! x:B. Q(x))";
by (resolve_tac (prems RL [ssubst]) 1);
by (REPEAT (ares_tac [ballI,iffI] 1
     ORELSE eresolve_tac ([make_elim bspec, mp] @ (prems RL [iffE])) 1));
qed "ball_cong";

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> P(x) = Q(x) |] ==> \
\    (? x:A. P(x)) = (? x:B. Q(x))";
by (resolve_tac (prems RL [ssubst]) 1);
by (REPEAT (etac bexE 1
     ORELSE ares_tac ([bexI,iffI] @ (prems RL [iffD1,iffD2])) 1));
qed "bex_cong";

(*** Subsets ***)

val prems = goalw Set.thy [subset_def] "(!!x.x:A ==> x:B) ==> A <= B";
by (REPEAT (ares_tac (prems @ [ballI]) 1));
qed "subsetI";

(*Rule in Modus Ponens style*)
val major::prems = goalw Set.thy [subset_def] "[| A <= B;  c:A |] ==> c:B";
by (rtac (major RS bspec) 1);
by (resolve_tac prems 1);
qed "subsetD";

(*The same, with reversed premises for use with etac -- cf rev_mp*)
qed_goal "rev_subsetD" Set.thy "[| c:A;  A <= B |] ==> c:B"
 (fn prems=>  [ (REPEAT (resolve_tac (prems@[subsetD]) 1)) ]);

(*Classical elimination rule*)
val major::prems = goalw Set.thy [subset_def] 
    "[| A <= B;  c~:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "subsetCE";

(*Takes assumptions A<=B; c:A and creates the assumption c:B *)
fun set_mp_tac i = etac subsetCE i  THEN  mp_tac i;

qed_goal "subset_refl" Set.thy "A <= (A::'a set)"
 (fn _=> [ (REPEAT (ares_tac [subsetI] 1)) ]);

val prems = goal Set.thy "[| A<=B;  B<=C |] ==> A<=(C::'a set)";
by (cut_facts_tac prems 1);
by (REPEAT (ares_tac [subsetI] 1 ORELSE set_mp_tac 1));
qed "subset_trans";


(*** Equality ***)

(*Anti-symmetry of the subset relation*)
val prems = goal Set.thy "[| A <= B;  B <= A |] ==> A = (B::'a set)";
by (rtac (iffI RS set_ext) 1);
by (REPEAT (ares_tac (prems RL [subsetD]) 1));
qed "subset_antisym";
val equalityI = subset_antisym;

(* Equality rules from ZF set theory -- are they appropriate here? *)
val prems = goal Set.thy "A = B ==> A<=(B::'a set)";
by (resolve_tac (prems RL [subst]) 1);
by (rtac subset_refl 1);
qed "equalityD1";

val prems = goal Set.thy "A = B ==> B<=(A::'a set)";
by (resolve_tac (prems RL [subst]) 1);
by (rtac subset_refl 1);
qed "equalityD2";

val prems = goal Set.thy
    "[| A = B;  [| A<=B; B<=(A::'a set) |] ==> P |]  ==>  P";
by (resolve_tac prems 1);
by (REPEAT (resolve_tac (prems RL [equalityD1,equalityD2]) 1));
qed "equalityE";

val major::prems = goal Set.thy
    "[| A = B;  [| c:A; c:B |] ==> P;  [| c~:A; c~:B |] ==> P |]  ==>  P";
by (rtac (major RS equalityE) 1);
by (REPEAT (contr_tac 1 ORELSE eresolve_tac ([asm_rl,subsetCE]@prems) 1));
qed "equalityCE";

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. *)
val prems = goal Set.thy 
    "[| p:A;  !!z. z:A ==> p=z --> R |] ==> R";
by (rtac mp 1);
by (REPEAT (resolve_tac (refl::prems) 1));
qed "setup_induction";


(*** Set complement -- Compl ***)

val prems = goalw Set.thy [Compl_def]
    "[| c:A ==> False |] ==> c : Compl(A)";
by (REPEAT (ares_tac (prems @ [CollectI,notI]) 1));
qed "ComplI";

(*This form, with negated conclusion, works well with the Classical prover.
  Negated assumptions behave like formulae on the right side of the notional
  turnstile...*)
val major::prems = goalw Set.thy [Compl_def]
    "[| c : Compl(A) |] ==> c~:A";
by (rtac (major RS CollectD) 1);
qed "ComplD";

val ComplE = make_elim ComplD;


(*** Binary union -- Un ***)

val prems = goalw Set.thy [Un_def] "c:A ==> c : A Un B";
by (REPEAT (resolve_tac (prems @ [CollectI,disjI1]) 1));
qed "UnI1";

val prems = goalw Set.thy [Un_def] "c:B ==> c : A Un B";
by (REPEAT (resolve_tac (prems @ [CollectI,disjI2]) 1));
qed "UnI2";

(*Classical introduction rule: no commitment to A vs B*)
qed_goal "UnCI" Set.thy "(c~:B ==> c:A) ==> c : A Un B"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[UnI1,notI]) 1)),
    (REPEAT (ares_tac (prems@[UnI2,notE]) 1)) ]);

val major::prems = goalw Set.thy [Un_def]
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS CollectD RS disjE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "UnE";


(*** Binary intersection -- Int ***)

val prems = goalw Set.thy [Int_def]
    "[| c:A;  c:B |] ==> c : A Int B";
by (REPEAT (resolve_tac (prems @ [CollectI,conjI]) 1));
qed "IntI";

val [major] = goalw Set.thy [Int_def] "c : A Int B ==> c:A";
by (rtac (major RS CollectD RS conjunct1) 1);
qed "IntD1";

val [major] = goalw Set.thy [Int_def] "c : A Int B ==> c:B";
by (rtac (major RS CollectD RS conjunct2) 1);
qed "IntD2";

val [major,minor] = goal Set.thy
    "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P";
by (rtac minor 1);
by (rtac (major RS IntD1) 1);
by (rtac (major RS IntD2) 1);
qed "IntE";


(*** Set difference ***)

qed_goalw "DiffI" Set.thy [set_diff_def]
    "[| c : A;  c ~: B |] ==> c : A - B"
 (fn prems=> [ (REPEAT (resolve_tac (prems @ [CollectI,conjI]) 1)) ]);

qed_goalw "DiffD1" Set.thy [set_diff_def]
    "c : A - B ==> c : A"
 (fn [major]=> [ (rtac (major RS CollectD RS conjunct1) 1) ]);

qed_goalw "DiffD2" Set.thy [set_diff_def]
    "[| c : A - B;  c : B |] ==> P"
 (fn [major,minor]=>
     [rtac (minor RS (major RS CollectD RS conjunct2 RS notE)) 1]);

qed_goal "DiffE" Set.thy
    "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (ares_tac (prems RL [DiffD1, DiffD2 RS notI]) 1)) ]);

qed_goal "Diff_iff" Set.thy "(c : A-B) = (c:A & c~:B)"
 (fn _ => [ (fast_tac (HOL_cs addSIs [DiffI] addSEs [DiffE]) 1) ]);


(*** The empty set -- {} ***)

qed_goalw "emptyE" Set.thy [empty_def] "a:{} ==> P"
 (fn [prem] => [rtac (prem RS CollectD RS FalseE) 1]);

qed_goal "empty_subsetI" Set.thy "{} <= A"
 (fn _ => [ (REPEAT (ares_tac [equalityI,subsetI,emptyE] 1)) ]);

qed_goal "equals0I" Set.thy "[| !!y. y:A ==> False |] ==> A={}"
 (fn prems=>
  [ (REPEAT (ares_tac (prems@[empty_subsetI,subsetI,equalityI]) 1 
      ORELSE eresolve_tac (prems RL [FalseE]) 1)) ]);

qed_goal "equals0D" Set.thy "[| A={};  a:A |] ==> P"
 (fn [major,minor]=>
  [ (rtac (minor RS (major RS equalityD1 RS subsetD RS emptyE)) 1) ]);


(*** Augmenting a set -- insert ***)

qed_goalw "insertI1" Set.thy [insert_def] "a : insert a B"
 (fn _ => [rtac (CollectI RS UnI1) 1, rtac refl 1]);

qed_goalw "insertI2" Set.thy [insert_def] "a : B ==> a : insert b B"
 (fn [prem]=> [ (rtac (prem RS UnI2) 1) ]);

qed_goalw "insertE" Set.thy [insert_def]
    "[| a : insert b A;  a=b ==> P;  a:A ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems @ [CollectE]) 1)) ]);

qed_goal "insert_iff" Set.thy "a : insert b A = (a=b | a:A)"
 (fn _ => [fast_tac (HOL_cs addIs [insertI1,insertI2] addSEs [insertE]) 1]);

(*Classical introduction rule*)
qed_goal "insertCI" Set.thy "(a~:B ==> a=b) ==> a: insert b B"
 (fn [prem]=>
  [ (rtac (disjCI RS (insert_iff RS iffD2)) 1),
    (etac prem 1) ]);

(*** Singletons, using insert ***)

qed_goal "singletonI" Set.thy "a : {a}"
 (fn _=> [ (rtac insertI1 1) ]);

qed_goal "singletonE" Set.thy "[| a: {b};  a=b ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS insertE) 1),
    (REPEAT (eresolve_tac (prems @ [emptyE]) 1)) ]);

goalw Set.thy [insert_def] "!!a. b : {a} ==> b=a";
by(fast_tac (HOL_cs addSEs [emptyE,CollectE,UnE]) 1);
qed "singletonD";

val singletonE = make_elim singletonD;

val [major] = goal Set.thy "{a}={b} ==> a=b";
by (rtac (major RS equalityD1 RS subsetD RS singletonD) 1);
by (rtac singletonI 1);
qed "singleton_inject";

(*** Unions of families -- UNION x:A. B(x) is Union(B``A)  ***)

(*The order of the premises presupposes that A is rigid; b may be flexible*)
val prems = goalw Set.thy [UNION_def]
    "[| a:A;  b: B(a) |] ==> b: (UN x:A. B(x))";
by (REPEAT (resolve_tac (prems @ [bexI,CollectI]) 1));
qed "UN_I";

val major::prems = goalw Set.thy [UNION_def]
    "[| b : (UN x:A. B(x));  !!x.[| x:A;  b: B(x) |] ==> R |] ==> R";
by (rtac (major RS CollectD RS bexE) 1);
by (REPEAT (ares_tac prems 1));
qed "UN_E";

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (UN x:A. C(x)) = (UN x:B. D(x))";
by (REPEAT (etac UN_E 1
     ORELSE ares_tac ([UN_I,equalityI,subsetI] @ 
                      (prems RL [equalityD1,equalityD2] RL [subsetD])) 1));
qed "UN_cong";


(*** Intersections of families -- INTER x:A. B(x) is Inter(B``A) *)

val prems = goalw Set.thy [INTER_def]
    "(!!x. x:A ==> b: B(x)) ==> b : (INT x:A. B(x))";
by (REPEAT (ares_tac ([CollectI,ballI] @ prems) 1));
qed "INT_I";

val major::prems = goalw Set.thy [INTER_def]
    "[| b : (INT x:A. B(x));  a:A |] ==> b: B(a)";
by (rtac (major RS CollectD RS bspec) 1);
by (resolve_tac prems 1);
qed "INT_D";

(*"Classical" elimination -- by the Excluded Middle on a:A *)
val major::prems = goalw Set.thy [INTER_def]
    "[| b : (INT x:A. B(x));  b: B(a) ==> R;  a~:A ==> R |] ==> R";
by (rtac (major RS CollectD RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "INT_E";

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (INT x:A. C(x)) = (INT x:B. D(x))";
by (REPEAT_FIRST (resolve_tac [INT_I,equalityI,subsetI]));
by (REPEAT (dtac INT_D 1
     ORELSE ares_tac (prems RL [equalityD1,equalityD2] RL [subsetD]) 1));
qed "INT_cong";


(*** Unions over a type; UNION1(B) = Union(range(B)) ***)

(*The order of the premises presupposes that A is rigid; b may be flexible*)
val prems = goalw Set.thy [UNION1_def]
    "b: B(x) ==> b: (UN x. B(x))";
by (REPEAT (resolve_tac (prems @ [TrueI, CollectI RS UN_I]) 1));
qed "UN1_I";

val major::prems = goalw Set.thy [UNION1_def]
    "[| b : (UN x. B(x));  !!x. b: B(x) ==> R |] ==> R";
by (rtac (major RS UN_E) 1);
by (REPEAT (ares_tac prems 1));
qed "UN1_E";


(*** Intersections over a type; INTER1(B) = Inter(range(B)) *)

val prems = goalw Set.thy [INTER1_def]
    "(!!x. b: B(x)) ==> b : (INT x. B(x))";
by (REPEAT (ares_tac (INT_I::prems) 1));
qed "INT1_I";

val [major] = goalw Set.thy [INTER1_def]
    "b : (INT x. B(x)) ==> b: B(a)";
by (rtac (TrueI RS (CollectI RS (major RS INT_D))) 1);
qed "INT1_D";

(*** Unions ***)

(*The order of the premises presupposes that C is rigid; A may be flexible*)
val prems = goalw Set.thy [Union_def]
    "[| X:C;  A:X |] ==> A : Union(C)";
by (REPEAT (resolve_tac (prems @ [UN_I]) 1));
qed "UnionI";

val major::prems = goalw Set.thy [Union_def]
    "[| A : Union(C);  !!X.[| A:X;  X:C |] ==> R |] ==> R";
by (rtac (major RS UN_E) 1);
by (REPEAT (ares_tac prems 1));
qed "UnionE";

(*** Inter ***)

val prems = goalw Set.thy [Inter_def]
    "[| !!X. X:C ==> A:X |] ==> A : Inter(C)";
by (REPEAT (ares_tac ([INT_I] @ prems) 1));
qed "InterI";

(*A "destruct" rule -- every X in C contains A as an element, but
  A:X can hold when X:C does not!  This rule is analogous to "spec". *)
val major::prems = goalw Set.thy [Inter_def]
    "[| A : Inter(C);  X:C |] ==> A:X";
by (rtac (major RS INT_D) 1);
by (resolve_tac prems 1);
qed "InterD";

(*"Classical" elimination rule -- does not require proving X:C *)
val major::prems = goalw Set.thy [Inter_def]
    "[| A : Inter(C);  A:X ==> R;  X~:C ==> R |] ==> R";
by (rtac (major RS INT_E) 1);
by (REPEAT (eresolve_tac prems 1));
qed "InterE";

(*** Powerset ***)

qed_goalw "PowI" Set.thy [Pow_def] "!!A B. A <= B ==> A : Pow(B)"
 (fn _ => [ (etac CollectI 1) ]);

qed_goalw "PowD" Set.thy [Pow_def] "!!A B. A : Pow(B)  ==>  A<=B"
 (fn _=> [ (etac CollectD 1) ]);

val Pow_bottom = empty_subsetI RS PowI;        (* {}: Pow(B) *)
val Pow_top = subset_refl RS PowI;             (* A : Pow(A) *)
