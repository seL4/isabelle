(*  Title: 	ZF/subset
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Derived rules involving subsets
Union and Intersection as lattice operations
*)

(*** cons ***)

val cons_subsetI = prove_goal ZF.thy "[| a:C; B<=C |] ==> cons(a,B) <= C"
 (fn prems=>
  [ (cut_facts_tac prems 1),
    (REPEAT (ares_tac [subsetI] 1
     ORELSE eresolve_tac  [consE,ssubst,subsetD] 1)) ]);

val subset_consI = prove_goal ZF.thy "B <= cons(a,B)"
 (fn _=> [ (rtac subsetI 1), (etac consI2 1) ]);

(*Useful for rewriting!*)
val cons_subset_iff = prove_goal ZF.thy "cons(a,B)<=C <-> a:C & B<=C"
 (fn _=> [ (fast_tac upair_cs 1) ]);

(*A safe special case of subset elimination, adding no new variables 
  [| cons(a,B) <= C; [| a : C; B <= C |] ==> R |] ==> R *)
val cons_subsetE = standard (cons_subset_iff RS iffD1 RS conjE);

val subset_empty_iff = prove_goal ZF.thy "A<=0 <-> A=0"
 (fn _=> [ (fast_tac (upair_cs addIs [equalityI]) 1) ]);

val subset_cons_iff = prove_goal ZF.thy
    "C<=cons(a,B) <-> C<=B | (a:C & C-{a} <= B)"
 (fn _=> [ (fast_tac upair_cs 1) ]);

(*** succ ***)

val subset_succI = prove_goal ZF.thy "i <= succ(i)"
 (fn _=> [ (rtac subsetI 1), (etac succI2 1) ]);

(*But if j is an ordinal or is transitive, then i:j implies i<=j! 
  See ordinal/Ord_succ_subsetI*)
val succ_subsetI = prove_goalw ZF.thy [succ_def]
    "[| i:j;  i<=j |] ==> succ(i)<=j"
 (fn prems=>
  [ (REPEAT (ares_tac (prems@[cons_subsetI]) 1)) ]);

val succ_subsetE = prove_goalw ZF.thy [succ_def] 
    "[| succ(i) <= j;  [| i:j;  i<=j |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS cons_subsetE) 1),
    (REPEAT (ares_tac prems 1)) ]);

(*** singletons ***)

val singleton_subsetI = prove_goal ZF.thy
    "a:C ==> {a} <= C"
 (fn prems=>
  [ (REPEAT (resolve_tac (prems@[cons_subsetI,empty_subsetI]) 1)) ]);

val singleton_subsetD = prove_goal ZF.thy
    "{a} <= C  ==>  a:C"
 (fn prems=> [ (REPEAT (ares_tac (prems@[cons_subsetE]) 1)) ]);

(*** Big Union -- least upper bound of a set  ***)

val Union_subset_iff = prove_goal ZF.thy "Union(A) <= C <-> (ALL x:A. x <= C)"
 (fn _ => [ fast_tac upair_cs 1 ]);

val Union_upper = prove_goal ZF.thy
    "B:A ==> B <= Union(A)"
 (fn prems=> [ (REPEAT (ares_tac (prems@[subsetI,UnionI]) 1)) ]);

val Union_least = prove_goal ZF.thy
    "[| !!x. x:A ==> x<=C |] ==> Union(A) <= C"
 (fn [prem]=>
  [ (rtac (ballI RS (Union_subset_iff RS iffD2)) 1),
    (etac prem 1) ]);

(*** Union of a family of sets  ***)

goal ZF.thy "A <= (UN i:I. B(i)) <-> A = (UN i:I. A Int B(i))";
by (fast_tac (upair_cs addSIs [equalityI] addSEs [equalityE]) 1);
val subset_UN_iff_eq = result();

val UN_subset_iff = prove_goal ZF.thy
     "(UN x:A.B(x)) <= C <-> (ALL x:A. B(x) <= C)"
 (fn _ => [ fast_tac upair_cs 1 ]);

val UN_upper = prove_goal ZF.thy
    "!!x A. x:A ==> B(x) <= (UN x:A.B(x))"
 (fn _ => [ etac (RepFunI RS Union_upper) 1 ]);

val UN_least = prove_goal ZF.thy
    "[| !!x. x:A ==> B(x)<=C |] ==> (UN x:A.B(x)) <= C"
 (fn [prem]=>
  [ (rtac (ballI RS (UN_subset_iff RS iffD2)) 1),
    (etac prem 1) ]);


(*** Big Intersection -- greatest lower bound of a nonempty set ***)

val Inter_subset_iff = prove_goal ZF.thy
     "!!a A. a: A  ==>  C <= Inter(A) <-> (ALL x:A. C <= x)"
 (fn _ => [ fast_tac upair_cs 1 ]);

val Inter_lower = prove_goal ZF.thy "B:A ==> Inter(A) <= B"
 (fn prems=>
  [ (REPEAT (resolve_tac (prems@[subsetI]) 1
     ORELSE etac InterD 1)) ]);

val Inter_greatest = prove_goal ZF.thy
    "[| a:A;  !!x. x:A ==> C<=x |] ==> C <= Inter(A)"
 (fn [prem1,prem2]=>
  [ (rtac ([prem1, ballI] MRS (Inter_subset_iff RS iffD2)) 1),
    (etac prem2 1) ]);

(*** Intersection of a family of sets  ***)

val INT_lower = prove_goal ZF.thy
    "x:A ==> (INT x:A.B(x)) <= B(x)"
 (fn [prem] =>
  [ rtac (prem RS RepFunI RS Inter_lower) 1 ]);

val INT_greatest = prove_goal ZF.thy
    "[| a:A;  !!x. x:A ==> C<=B(x) |] ==> C <= (INT x:A.B(x))"
 (fn [nonempty,prem] =>
  [ rtac (nonempty RS RepFunI RS Inter_greatest) 1,
    REPEAT (eresolve_tac [RepFunE, prem, ssubst] 1) ]);


(*** Finite Union -- the least upper bound of 2 sets ***)

val Un_subset_iff = prove_goal ZF.thy "A Un B <= C <-> A <= C & B <= C"
 (fn _ => [ fast_tac upair_cs 1 ]);

val Un_upper1 = prove_goal ZF.thy "A <= A Un B"
 (fn _ => [ (REPEAT (ares_tac [subsetI,UnI1] 1)) ]);

val Un_upper2 = prove_goal ZF.thy "B <= A Un B"
 (fn _ => [ (REPEAT (ares_tac [subsetI,UnI2] 1)) ]);

val Un_least = prove_goal ZF.thy "!!A B C. [| A<=C;  B<=C |] ==> A Un B <= C"
 (fn _ =>
  [ (rtac (Un_subset_iff RS iffD2) 1),
    (REPEAT (ares_tac [conjI] 1)) ]);

(*** Finite Intersection -- the greatest lower bound of 2 sets *)

val Int_subset_iff = prove_goal ZF.thy "C <= A Int B <-> C <= A & C <= B"
 (fn _ => [ fast_tac upair_cs 1 ]);

val Int_lower1 = prove_goal ZF.thy "A Int B <= A"
 (fn _ => [ (REPEAT (ares_tac [subsetI] 1 ORELSE etac IntE 1)) ]);

val Int_lower2 = prove_goal ZF.thy "A Int B <= B"
 (fn _ => [ (REPEAT (ares_tac [subsetI] 1 ORELSE etac IntE 1)) ]);

val Int_greatest = prove_goal ZF.thy
                             "!!A B C. [| C<=A;  C<=B |] ==> C <= A Int B"
 (fn prems=>
  [ (rtac (Int_subset_iff RS iffD2) 1),
    (REPEAT (ares_tac [conjI] 1)) ]);

(*** Set difference *)

val Diff_subset = prove_goal ZF.thy "A-B <= A"
 (fn _ => [ (REPEAT (ares_tac [subsetI] 1 ORELSE etac DiffE 1)) ]);

val Diff_contains = prove_goal ZF.thy
    "[| C<=A;  C Int B = 0 |] ==> C <= A-B"
 (fn prems=>
  [ (cut_facts_tac prems 1),
    (rtac subsetI 1),
    (REPEAT (ares_tac [DiffI,IntI,notI] 1
     ORELSE eresolve_tac [subsetD,equals0D] 1)) ]);

(** Collect **)

val Collect_subset = prove_goal ZF.thy "Collect(A,P) <= A"
 (fn _ => [ (REPEAT (ares_tac [subsetI] 1 ORELSE etac CollectD1 1)) ]);

(** RepFun **)

val prems = goal ZF.thy "[| !!x. x:A ==> f(x): B |] ==> {f(x). x:A} <= B";
by (rtac subsetI 1);
by (etac RepFunE 1);
by (etac ssubst 1);
by (eresolve_tac prems 1);
val RepFun_subset = result();
