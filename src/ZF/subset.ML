(*  Title:      ZF/subset
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Derived rules involving subsets
Union and Intersection as lattice operations
*)

(*** cons ***)

qed_goal "cons_subsetI" thy "!!a. [| a:C; B<=C |] ==> cons(a,B) <= C"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "subset_consI" thy "B <= cons(a,B)"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "cons_subset_iff" thy "cons(a,B)<=C <-> a:C & B<=C"
 (fn _ => [ Fast_tac 1 ]);

(*A safe special case of subset elimination, adding no new variables 
  [| cons(a,B) <= C; [| a : C; B <= C |] ==> R |] ==> R *)
bind_thm ("cons_subsetE", cons_subset_iff RS iffD1 RS conjE);

qed_goal "subset_empty_iff" thy "A<=0 <-> A=0"
 (fn _=> [ (fast_tac (!claset addIs [equalityI]) 1) ]);

qed_goal "subset_cons_iff" thy
    "C<=cons(a,B) <-> C<=B | (a:C & C-{a} <= B)"
 (fn _=> [ (Fast_tac 1) ]);

(*** succ ***)

qed_goal "subset_succI" thy "i <= succ(i)"
 (fn _=> [ (Fast_tac 1) ]);

(*But if j is an ordinal or is transitive, then i:j implies i<=j! 
  See ordinal/Ord_succ_subsetI*)
qed_goalw "succ_subsetI" thy [succ_def]
    "!!i j. [| i:j;  i<=j |] ==> succ(i)<=j"
 (fn _=> [ (Fast_tac 1) ]);

qed_goalw "succ_subsetE" thy [succ_def] 
    "[| succ(i) <= j;  [| i:j;  i<=j |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS cons_subsetE) 1),
    (REPEAT (ares_tac prems 1)) ]);

(*** singletons ***)

qed_goal "singleton_subsetI" thy "!!a c. a:C ==> {a} <= C"
 (fn _=> [ (Fast_tac 1) ]);

qed_goal "singleton_subsetD" thy "!!a C. {a} <= C  ==>  a:C"
 (fn _=> [ (Fast_tac 1) ]);

(*** Big Union -- least upper bound of a set  ***)

qed_goal "Union_subset_iff" thy "Union(A) <= C <-> (ALL x:A. x <= C)"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Union_upper" thy
    "!!B A. B:A ==> B <= Union(A)"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Union_least" thy
    "[| !!x. x:A ==> x<=C |] ==> Union(A) <= C"
 (fn [prem]=>
  [ (rtac (ballI RS (Union_subset_iff RS iffD2)) 1),
    (etac prem 1) ]);

(*** Union of a family of sets  ***)

goal thy "A <= (UN i:I. B(i)) <-> A = (UN i:I. A Int B(i))";
by (fast_tac (!claset addSIs [equalityI] addSEs [equalityE]) 1);
qed "subset_UN_iff_eq";

qed_goal "UN_subset_iff" thy
     "(UN x:A.B(x)) <= C <-> (ALL x:A. B(x) <= C)"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "UN_upper" thy
    "!!x A. x:A ==> B(x) <= (UN x:A.B(x))"
 (fn _ => [ etac (RepFunI RS Union_upper) 1 ]);

qed_goal "UN_least" thy
    "[| !!x. x:A ==> B(x)<=C |] ==> (UN x:A.B(x)) <= C"
 (fn [prem]=>
  [ (rtac (ballI RS (UN_subset_iff RS iffD2)) 1),
    (etac prem 1) ]);


(*** Big Intersection -- greatest lower bound of a nonempty set ***)

qed_goal "Inter_subset_iff" thy
     "!!a A. a: A  ==>  C <= Inter(A) <-> (ALL x:A. C <= x)"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Inter_lower" thy "!!B A. B:A ==> Inter(A) <= B"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Inter_greatest" thy
    "[| a:A;  !!x. x:A ==> C<=x |] ==> C <= Inter(A)"
 (fn [prem1,prem2]=>
  [ (rtac ([prem1, ballI] MRS (Inter_subset_iff RS iffD2)) 1),
    (etac prem2 1) ]);

(*** Intersection of a family of sets  ***)

qed_goal "INT_lower" thy
    "!!x. x:A ==> (INT x:A.B(x)) <= B(x)"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "INT_greatest" thy
    "[| a:A;  !!x. x:A ==> C<=B(x) |] ==> C <= (INT x:A.B(x))"
 (fn [nonempty,prem] =>
  [ rtac (nonempty RS RepFunI RS Inter_greatest) 1,
    REPEAT (eresolve_tac [RepFunE, prem, ssubst] 1) ]);


(*** Finite Union -- the least upper bound of 2 sets ***)

qed_goal "Un_subset_iff" thy "A Un B <= C <-> A <= C & B <= C"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Un_upper1" thy "A <= A Un B"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Un_upper2" thy "B <= A Un B"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Un_least" thy "!!A B C. [| A<=C;  B<=C |] ==> A Un B <= C"
 (fn _ => [ Fast_tac 1 ]);


(*** Finite Intersection -- the greatest lower bound of 2 sets *)

qed_goal "Int_subset_iff" thy "C <= A Int B <-> C <= A & C <= B"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Int_lower1" thy "A Int B <= A"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Int_lower2" thy "A Int B <= B"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Int_greatest" thy "!!A B C. [| C<=A;  C<=B |] ==> C <= A Int B"
 (fn _ => [ Fast_tac 1 ]);


(*** Set difference *)

qed_goal "Diff_subset" thy "A-B <= A"
 (fn _ => [ Fast_tac 1 ]);

qed_goal "Diff_contains" thy
    "!!C. [| C<=A;  C Int B = 0 |] ==> C <= A-B"
 (fn _ => [ (fast_tac (!claset addSEs [equalityE]) 1) ]);


(** Collect **)

qed_goal "Collect_subset" thy "Collect(A,P) <= A"
 (fn _ => [ Fast_tac 1 ]);


(** RepFun **)

val prems = goal thy "[| !!x. x:A ==> f(x): B |] ==> {f(x). x:A} <= B";
by (fast_tac (!claset addIs prems) 1);
qed "RepFun_subset";

val subset_SIs =
    [subset_refl, cons_subsetI, subset_consI, 
     Union_least, UN_least, Un_least, 
     Inter_greatest, Int_greatest, RepFun_subset,
     Un_upper1, Un_upper2, Int_lower1, Int_lower2];


(*A claset for subset reasoning*)
val subset_cs = !claset 
    delrules [subsetI, subsetCE]
    addSIs subset_SIs
    addIs  [Union_upper, Inter_lower]
    addSEs [cons_subsetE];

