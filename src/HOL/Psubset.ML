(*  Title:      Psubset.ML
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Properties of subsets and empty sets.
*)

open Psubset;

(*********)

(*** Rules for subsets ***)

goal Set.thy "A <= B =  (! t.t:A --> t:B)";
by (Blast_tac 1);
qed "subset_iff";

goalw thy [psubset_def] "!!A::'a set. [| A <= B; A ~= B |] ==> A<B";
by (Blast_tac 1);
qed "psubsetI";


goalw thy [psubset_def] "((A::'a set) <= B) = ((A < B) | (A=B))";
by (Blast_tac 1);
qed "subset_iff_psubset_eq";


goal Set.thy "!!a. insert a A ~= insert a B ==> A ~= B";
by (Blast_tac 1);
qed "insert_lim";

(* This is an adaptation of the proof for the "<=" version in Finite. *) 

goalw thy [psubset_def]
"!!B. finite B ==> !A. A < B --> card(A) < card(B)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (Blast_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (case_tac "x:A" 1);
(*1*)
by (dtac mk_disjoint_insert 1);
by (etac exE 1);
by (etac conjE 1);
by (hyp_subst_tac 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (!simpset addsimps [subset_insert_iff,finite_subset]) 1);
by (dtac insert_lim 1);
by (Asm_full_simp_tac 1);
(*2*)
by (rotate_tac ~1 1);
by (asm_full_simp_tac (!simpset addsimps [subset_insert_iff,finite_subset]) 1);
by (case_tac "A=F" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (subgoal_tac "card A <= card F" 1);
by (Asm_simp_tac 2);
by (Auto_tac());
qed_spec_mp "psubset_card" ;


goal Set.thy "(A = B) = ((A <= (B::'a set)) & (B<=A))";
by (Blast_tac 1);
qed "set_eq_subset";


goalw thy [psubset_def] "~ (A < {})";
by (Blast_tac 1);
qed "not_psubset_empty";

AddIffs [not_psubset_empty];

goalw thy [psubset_def]
    "!!x. A < insert x B ==> (x ~: A) & A<=B | x:A & A-{x}<B";
by (Auto_tac());
qed "psubset_insertD";


(*NB we do not have  [| A < B; C < D |] ==> A Un C < B Un D
  even for finite sets: consider A={1}, C={2}, B=D={1,2} *)


