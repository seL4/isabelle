(*  Title:      ZF/subset
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Derived rules involving subsets
Union and Intersection as lattice operations
*)

(*** cons ***)

Goal "[| a:C; B<=C |] ==> cons(a,B) <= C";
by (Blast_tac 1);
qed "cons_subsetI";

Goal "B <= cons(a,B)";
by (Blast_tac 1);
qed "subset_consI";

Goal "cons(a,B)<=C <-> a:C & B<=C";
by (Blast_tac 1);
qed "cons_subset_iff";
AddIffs [cons_subset_iff];

(*A safe special case of subset elimination, adding no new variables 
  [| cons(a,B) <= C; [| a : C; B <= C |] ==> R |] ==> R *)
bind_thm ("cons_subsetE", cons_subset_iff RS iffD1 RS conjE);

Goal "A<=0 <-> A=0";
by (Blast_tac 1) ;
qed "subset_empty_iff";

Goal "C<=cons(a,B) <-> C<=B | (a:C & C-{a} <= B)";
by (Blast_tac 1) ;
qed "subset_cons_iff";

(*** succ ***)

Goal "i <= succ(i)";
by (Blast_tac 1) ;
qed "subset_succI";

(*But if j is an ordinal or is transitive, then i:j implies i<=j! 
  See ordinal/Ord_succ_subsetI*)
Goalw [succ_def] "[| i:j;  i<=j |] ==> succ(i)<=j";
by (Blast_tac 1) ;
qed "succ_subsetI";

val major::prems= Goalw [succ_def]  
    "[| succ(i) <= j;  [| i:j;  i<=j |] ==> P \
\    |] ==> P";
by (rtac (major RS cons_subsetE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "succ_subsetE";

(*** singletons ***)

Goal "a:C ==> {a} <= C";
by (Blast_tac 1) ;
qed "singleton_subsetI";

Goal "{a} <= C  ==>  a:C";
by (Blast_tac 1) ;
qed "singleton_subsetD";

(*** Big Union -- least upper bound of a set  ***)

Goal "Union(A) <= C <-> (ALL x:A. x <= C)";
by (Blast_tac 1);
qed "Union_subset_iff";

Goal "B:A ==> B <= Union(A)";
by (Blast_tac 1);
qed "Union_upper";

val [prem]= Goal
    "[| !!x. x:A ==> x<=C |] ==> Union(A) <= C";
by (rtac (ballI RS (Union_subset_iff RS iffD2)) 1);
by (etac prem 1) ;
qed "Union_least";

(*** Union of a family of sets  ***)

Goal "A <= (UN i:I. B(i)) <-> A = (UN i:I. A Int B(i))";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "subset_UN_iff_eq";

Goal "(UN x:A. B(x)) <= C <-> (ALL x:A. B(x) <= C)";
by (Blast_tac 1);
qed "UN_subset_iff";

Goal "x:A ==> B(x) <= (UN x:A. B(x))";
by (etac (RepFunI RS Union_upper) 1);
qed "UN_upper";

val [prem]= Goal
    "[| !!x. x:A ==> B(x)<=C |] ==> (UN x:A. B(x)) <= C";
by (rtac (ballI RS (UN_subset_iff RS iffD2)) 1);
by (etac prem 1) ;
qed "UN_least";


(*** Big Intersection -- greatest lower bound of a nonempty set ***)

Goal "a: A  ==>  C <= Inter(A) <-> (ALL x:A. C <= x)";
by (Blast_tac 1);
qed "Inter_subset_iff";

Goal "B:A ==> Inter(A) <= B";
by (Blast_tac 1);
qed "Inter_lower";

val [prem1,prem2]= Goal
    "[| a:A;  !!x. x:A ==> C<=x |] ==> C <= Inter(A)";
by (rtac ([prem1, ballI] MRS (Inter_subset_iff RS iffD2)) 1);
by (etac prem2 1) ;
qed "Inter_greatest";

(*** Intersection of a family of sets  ***)

Goal "x:A ==> (INT x:A. B(x)) <= B(x)";
by (Blast_tac 1);
qed "INT_lower";

val [nonempty,prem] = Goal
    "[| a:A;  !!x. x:A ==> C<=B(x) |] ==> C <= (INT x:A. B(x))";
by (rtac (nonempty RS RepFunI RS Inter_greatest) 1);
by (REPEAT (eresolve_tac [RepFunE, prem, ssubst] 1));
qed "INT_greatest";


(*** Finite Union -- the least upper bound of 2 sets ***)

Goal "A Un B <= C <-> A <= C & B <= C";
by (Blast_tac 1);
qed "Un_subset_iff";

Goal "A <= A Un B";
by (Blast_tac 1);
qed "Un_upper1";

Goal "B <= A Un B";
by (Blast_tac 1);
qed "Un_upper2";

Goal "[| A<=C;  B<=C |] ==> A Un B <= C";
by (Blast_tac 1);
qed "Un_least";


(*** Finite Intersection -- the greatest lower bound of 2 sets *)

Goal "C <= A Int B <-> C <= A & C <= B";
by (Blast_tac 1);
qed "Int_subset_iff";

Goal "A Int B <= A";
by (Blast_tac 1);
qed "Int_lower1";

Goal "A Int B <= B";
by (Blast_tac 1);
qed "Int_lower2";

Goal "[| C<=A;  C<=B |] ==> C <= A Int B";
by (Blast_tac 1);
qed "Int_greatest";


(*** Set difference *)

Goal "A-B <= A";
by (Blast_tac 1);
qed "Diff_subset";

Goal "[| C<=A;  C Int B = 0 |] ==> C <= A-B";
by (Blast_tac 1);
qed "Diff_contains";

Goal "B <= A - cons(c,C)  <->  B<=A-C & c ~: B";
by (Blast_tac 1);
qed "subset_Diff_cons_iff";



(** Collect **)

Goal "Collect(A,P) <= A";
by (Blast_tac 1);
qed "Collect_subset";


(** RepFun **)

val prems = Goal "[| !!x. x:A ==> f(x): B |] ==> {f(x). x:A} <= B";
by (blast_tac (claset() addIs prems) 1);
qed "RepFun_subset";

bind_thms ("subset_SIs",
    [subset_refl, cons_subsetI, subset_consI, 
     Union_least, UN_least, Un_least, 
     Inter_greatest, Int_greatest, RepFun_subset,
     Un_upper1, Un_upper2, Int_lower1, Int_lower2]);


(*A claset for subset reasoning*)
val subset_cs = claset() 
    delrules [subsetI, subsetCE]
    addSIs subset_SIs
    addIs  [Union_upper, Inter_lower]
    addSEs [cons_subsetE];

