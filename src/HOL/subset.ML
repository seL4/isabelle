(*  Title:      HOL/subset.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Derived rules involving subsets.  Union and Intersection as lattice
operations.
*)

(* legacy ML bindings *)

val Ball_def = thm "Ball_def";
val Bex_def = thm "Bex_def";
val Collect_mem_eq = thm "Collect_mem_eq";
val Compl_def = thm "Compl_def";
val INTER_def = thm "INTER_def";
val Int_def = thm "Int_def";
val Inter_def = thm "Inter_def";
val Pow_def = thm "Pow_def";
val UNION_def = thm "UNION_def";
val UNIV_def = thm "UNIV_def";
val Un_def = thm "Un_def";
val Union_def = thm "Union_def";
val empty_def = thm "empty_def";
val image_def = thm "image_def";
val insert_def = thm "insert_def";
val mem_Collect_eq = thm "mem_Collect_eq";
val psubset_def = thm "psubset_def";
val set_diff_def = thm "set_diff_def";
val subset_def = thm "subset_def";
val CollectI = thm "CollectI";
val CollectD = thm "CollectD";
val set_ext = thm "set_ext";
val Collect_cong = thm "Collect_cong";
val CollectE = thm "CollectE";
val ballI = thm "ballI";
val strip = thms "strip";
val bspec = thm "bspec";
val ballE = thm "ballE";
val bexI = thm "bexI";
val rev_bexI = thm "rev_bexI";
val bexCI = thm "bexCI";
val bexE = thm "bexE";
val ball_triv = thm "ball_triv";
val bex_triv = thm "bex_triv";
val bex_triv_one_point1 = thm "bex_triv_one_point1";
val bex_triv_one_point2 = thm "bex_triv_one_point2";
val bex_one_point1 = thm "bex_one_point1";
val bex_one_point2 = thm "bex_one_point2";
val ball_one_point1 = thm "ball_one_point1";
val ball_one_point2 = thm "ball_one_point2";
val ball_cong = thm "ball_cong";
val bex_cong = thm "bex_cong";
val subsetI = thm "subsetI";
val subsetD = thm "subsetD";
val rev_subsetD = thm "rev_subsetD";
val subsetCE = thm "subsetCE";
val contra_subsetD = thm "contra_subsetD";
val subset_refl = thm "subset_refl";
val subset_trans = thm "subset_trans";
val subset_antisym = thm "subset_antisym";
val equalityI = thm "equalityI";
val equalityD1 = thm "equalityD1";
val equalityD2 = thm "equalityD2";
val equalityE = thm "equalityE";
val equalityCE = thm "equalityCE";
val setup_induction = thm "setup_induction";
val eqset_imp_iff = thm "eqset_imp_iff";
val UNIV_I = thm "UNIV_I";
val UNIV_witness = thm "UNIV_witness";
val subset_UNIV = thm "subset_UNIV";
val ball_UNIV = thm "ball_UNIV";
val bex_UNIV = thm "bex_UNIV";
val empty_iff = thm "empty_iff";
val emptyE = thm "emptyE";
val empty_subsetI = thm "empty_subsetI";
val equals0I = thm "equals0I";
val equals0D = thm "equals0D";
val ball_empty = thm "ball_empty";
val bex_empty = thm "bex_empty";
val UNIV_not_empty = thm "UNIV_not_empty";
val Pow_iff = thm "Pow_iff";
val PowI = thm "PowI";
val PowD = thm "PowD";
val Pow_bottom = thm "Pow_bottom";
val Pow_top = thm "Pow_top";
val Compl_iff = thm "Compl_iff";
val ComplI = thm "ComplI";
val ComplD = thm "ComplD";
val ComplE = thm "ComplE";
val Un_iff = thm "Un_iff";
val UnI1 = thm "UnI1";
val UnI2 = thm "UnI2";
val UnCI = thm "UnCI";
val UnE = thm "UnE";
val Int_iff = thm "Int_iff";
val IntI = thm "IntI";
val IntD1 = thm "IntD1";
val IntD2 = thm "IntD2";
val IntE = thm "IntE";
val Diff_iff = thm "Diff_iff";
val DiffI = thm "DiffI";
val DiffD1 = thm "DiffD1";
val DiffD2 = thm "DiffD2";
val DiffE = thm "DiffE";
val insert_iff = thm "insert_iff";
val insertI1 = thm "insertI1";
val insertI2 = thm "insertI2";
val insertE = thm "insertE";
val insertCI = thm "insertCI";
val subset_insert_iff = thm "subset_insert_iff";
val singletonI = thm "singletonI";
val singletonD = thm "singletonD";
val singletonE = thm "singletonE";
val singleton_iff = thm "singleton_iff";
val singleton_inject = thm "singleton_inject";
val singleton_insert_inj_eq = thm "singleton_insert_inj_eq";
val singleton_insert_inj_eq' = thm "singleton_insert_inj_eq'";
val subset_singletonD = thm "subset_singletonD";
val singleton_conv = thm "singleton_conv";
val singleton_conv2 = thm "singleton_conv2";
val diff_single_insert = thm "diff_single_insert";
val UN_iff = thm "UN_iff";
val UN_I = thm "UN_I";
val UN_E = thm "UN_E";
val UN_cong = thm "UN_cong";
val INT_iff = thm "INT_iff";
val INT_I = thm "INT_I";
val INT_D = thm "INT_D";
val INT_E = thm "INT_E";
val INT_cong = thm "INT_cong";
val Union_iff = thm "Union_iff";
val UnionI = thm "UnionI";
val UnionE = thm "UnionE";
val Inter_iff = thm "Inter_iff";
val InterI = thm "InterI";
val InterD = thm "InterD";
val InterE = thm "InterE";
val image_eqI = thm "image_eqI";
val imageI = thm "imageI";
val rev_image_eqI = thm "rev_image_eqI";
val imageE = thm "imageE";
val image_Un = thm "image_Un";
val image_iff = thm "image_iff";
val image_subset_iff = thm "image_subset_iff";
val subset_image_iff = thm "subset_image_iff";
val image_subsetI = thm "image_subsetI";
val range_eqI = thm "range_eqI";
val rangeI = thm "rangeI";
val rangeE = thm "rangeE";
val split_if_eq1 = thm "split_if_eq1";
val split_if_eq2 = thm "split_if_eq2";
val split_if_mem1 = thm "split_if_mem1";
val split_if_mem2 = thm "split_if_mem2";
val split_ifs = thms "split_ifs";
val mem_simps = thms "mem_simps";
val psubsetI = thm "psubsetI";
val psubset_insert_iff = thm "psubset_insert_iff";
val psubset_eq = thm "psubset_eq";
val psubset_imp_subset = thm "psubset_imp_subset";
val psubset_subset_trans = thm "psubset_subset_trans";
val subset_psubset_trans = thm "subset_psubset_trans";
val psubset_imp_ex_mem = thm "psubset_imp_ex_mem";
val atomize_ball = thm "atomize_ball";


(*** insert ***)

Goal "B <= insert a B";
by (rtac subsetI 1);
by (etac insertI2 1) ;
qed "subset_insertI";

Goal "x ~: A ==> (A <= insert x B) = (A <= B)";
by (Blast_tac 1);
qed "subset_insert";

(*** Big Union -- least upper bound of a set  ***)

Goal "B:A ==> B <= Union(A)";
by (REPEAT (ares_tac [subsetI,UnionI] 1));
qed "Union_upper";

val [prem] = Goal "[| !!X. X:A ==> X<=C |] ==> Union(A) <= C";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, UnionE, prem RS subsetD] 1));
qed "Union_least";

(** General union **)

Goal "a:A ==> B(a) <= (UN x:A. B(x))";
by (Blast_tac 1);
qed "UN_upper";

val [prem] = Goal "[| !!x. x:A ==> B(x)<=C |] ==> (UN x:A. B(x)) <= C";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, UN_E, prem RS subsetD] 1));
qed "UN_least";


(*** Big Intersection -- greatest lower bound of a set ***)

Goal "B:A ==> Inter(A) <= B";
by (Blast_tac 1);
qed "Inter_lower";

val [prem] = Goal "[| !!X. X:A ==> C<=X |] ==> C <= Inter(A)";
by (rtac (InterI RS subsetI) 1);
by (REPEAT (eresolve_tac [asm_rl, prem RS subsetD] 1));
qed "Inter_greatest";

Goal "a:A ==> (INT x:A. B(x)) <= B(a)";
by (Blast_tac 1);
qed "INT_lower";

val [prem] = Goal "[| !!x. x:A ==> C<=B(x) |] ==> C <= (INT x:A. B(x))";
by (rtac (INT_I RS subsetI) 1);
by (REPEAT (eresolve_tac [asm_rl, prem RS subsetD] 1));
qed "INT_greatest";

(*** Finite Union -- the least upper bound of 2 sets ***)

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

Goal "A Int B <= A";
by (Blast_tac 1);
qed "Int_lower1";

Goal "A Int B <= B";
by (Blast_tac 1);
qed "Int_lower2";

Goal "[| C<=A;  C<=B |] ==> C <= A Int B";
by (Blast_tac 1);
qed "Int_greatest";

(*** Set difference ***)

Goal "A-B <= (A::'a set)";
by (Blast_tac 1) ;
qed "Diff_subset";

(*** Monotonicity ***)

Goal "mono(f) ==> f(A) Un f(B) <= f(A Un B)";
by (rtac Un_least 1);
by (etac (Un_upper1 RSN (2,monoD)) 1);
by (etac (Un_upper2 RSN (2,monoD)) 1);
qed "mono_Un";

Goal "mono(f) ==> f(A Int B) <= f(A) Int f(B)";
by (rtac Int_greatest 1);
by (etac (Int_lower1 RSN (2,monoD)) 1);
by (etac (Int_lower2 RSN (2,monoD)) 1);
qed "mono_Int";
