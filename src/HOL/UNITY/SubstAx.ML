(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

LeadsTo relation, restricted to the set of reachable states.
*)

(*Map its type, ['a program, 'a set, 'a set] => bool, to just 'a*)
Blast.overloaded ("SubstAx.LeadsTo", 
		  HOLogic.dest_setT o domain_type o range_type);


(*** Specialized laws for handling invariants ***)

(** Conjoining a safety property **)

Goal "[| reachable F <= C;  LeadsTo F (C Int A) A' |]   \
\     ==> LeadsTo F A A'";
by (asm_full_simp_tac
    (simpset() addsimps [LeadsTo_def, Int_absorb2, Int_assoc RS sym]) 1);
qed "reachable_LeadsToI";

Goal "[| reachable F <= C;  LeadsTo F A A' |]   \
\     ==> LeadsTo F A (C Int A')";
by (asm_full_simp_tac
    (simpset() addsimps [LeadsTo_def, Int_absorb2,
			 Int_assoc RS sym]) 1);
qed "reachable_LeadsToD";


(** Conjoining an invariant **)

(* [| Invariant F C; LeadsTo F (C Int A) A' |] ==> LeadsTo F A A' *)
bind_thm ("Invariant_LeadsToI", 
	  Invariant_includes_reachable RS reachable_LeadsToI);

(* [| Invariant F C; LeadsTo F A A' |] ==> LeadsTo F A (C Int A') *)
bind_thm ("Invariant_LeadsToD", 
	  Invariant_includes_reachable RS reachable_LeadsToD);




(*** Introduction rules: Basis, Trans, Union ***)

Goal "leadsTo (Acts F) A B ==> LeadsTo F A B";
by (simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [psp_stable2, stable_reachable]) 1);
qed "leadsTo_imp_LeadsTo";

Goal "[| LeadsTo F A B;  LeadsTo F B C |] ==> LeadsTo F A C";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_Trans]) 1);
qed "LeadsTo_Trans";

val [prem] = Goalw [LeadsTo_def]
 "(!!A. A : S ==> LeadsTo F A B) ==> LeadsTo F (Union S) B";
by (Simp_tac 1);
by (stac Int_Union 1);
by (blast_tac (claset() addIs [leadsTo_UN,
			       simplify (simpset()) prem]) 1);
qed "LeadsTo_Union";


(*** Derived rules ***)

Goal "LeadsTo F A UNIV";
by (asm_simp_tac (simpset() addsimps [LeadsTo_def, 
				      Int_lower1 RS subset_imp_leadsTo]) 1);
qed "LeadsTo_UNIV";
Addsimps [LeadsTo_UNIV];

(*Useful with cancellation, disjunction*)
Goal "LeadsTo F A (A' Un A') ==> LeadsTo F A A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate";

Goal "LeadsTo F A (A' Un C Un C) ==> LeadsTo F A (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate2";

val prems = 
Goal "(!!i. i : I ==> LeadsTo F (A i) B) ==> LeadsTo F (UN i:I. A i) B";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs (LeadsTo_Union::prems)) 1);
qed "LeadsTo_UN";

(*Binary union introduction rule*)
Goal "[| LeadsTo F A C; LeadsTo F B C |] ==> LeadsTo F (A Un B) C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [LeadsTo_Union]) 1);
qed "LeadsTo_Un";

Goal "A <= B ==> LeadsTo F A B";
by (simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "subset_imp_LeadsTo";

bind_thm ("empty_LeadsTo", empty_subsetI RS subset_imp_LeadsTo);
Addsimps [empty_LeadsTo];

Goal "[| LeadsTo F A A';  A' <= B' |] ==> LeadsTo F A B'";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_R]) 1);
qed_spec_mp "LeadsTo_weaken_R";

Goal "[| LeadsTo F A A';  B <= A |]  \
\     ==> LeadsTo F B A'";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_L]) 1);
qed_spec_mp "LeadsTo_weaken_L";

Goal "[| LeadsTo F A A';   \
\        B  <= A;   A' <= B' |] \
\     ==> LeadsTo F B B'";
by (blast_tac (claset() addIs [LeadsTo_weaken_R, LeadsTo_weaken_L,
			       LeadsTo_Trans]) 1);
qed "LeadsTo_weaken";

Goal "[| reachable F <= C;  LeadsTo F A A';   \
\        C Int B <= A;   C Int A' <= B' |] \
\     ==> LeadsTo F B B'";
by (blast_tac (claset() addDs [reachable_LeadsToI] addIs[LeadsTo_weaken]
                        addIs [reachable_LeadsToD]) 1);
qed "reachable_LeadsTo_weaken";

(** Two theorems for "proof lattices" **)

Goal "[| LeadsTo F A B |] ==> LeadsTo F (A Un B) B";
by (blast_tac (claset() addIs [LeadsTo_Un, subset_imp_LeadsTo]) 1);
qed "LeadsTo_Un_post";

Goal "[| LeadsTo F A B;  LeadsTo F B C |] \
\     ==> LeadsTo F (A Un B) C";
by (blast_tac (claset() addIs [LeadsTo_Un, subset_imp_LeadsTo, 
			       LeadsTo_weaken_L, LeadsTo_Trans]) 1);
qed "LeadsTo_Trans_Un";


(** Distributive laws **)

Goal "LeadsTo F (A Un B) C  = (LeadsTo F A C & LeadsTo F B C)";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Un_distrib";

Goal "LeadsTo F (UN i:I. A i) B  =  (ALL i : I. LeadsTo F (A i) B)";
by (blast_tac (claset() addIs [LeadsTo_UN, LeadsTo_weaken_L]) 1);
qed "LeadsTo_UN_distrib";

Goal "LeadsTo F (Union S) B  =  (ALL A : S. LeadsTo F A B)";
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Union_distrib";


(** More rules using the premise "Invariant F" **)

Goalw [LeadsTo_def, Constrains_def]
     "[| Constrains F (A-A') (A Un A'); transient  (Acts F) (A-A') |]   \
\     ==> LeadsTo F A A'";
by (rtac (ensuresI RS leadsTo_Basis) 1);
by (blast_tac (claset() addIs [transient_strengthen]) 2);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "LeadsTo_Basis";

Goal "[| Invariant F INV;      \
\        Constrains F (INV Int (A-A')) (A Un A'); \
\        transient  (Acts F) (INV Int (A-A')) |]   \
\ ==> LeadsTo F A A'";
by (rtac Invariant_LeadsToI 1);
by (assume_tac 1);
by (rtac LeadsTo_Basis 1);
by (blast_tac (claset() addIs [transient_strengthen]) 2);
by (blast_tac (claset() addIs [Invariant_ConstrainsD RS Constrains_weaken]) 1);
qed "Invariant_LeadsTo_Basis";

Goal "[| Invariant F INV;      \
\        LeadsTo F A A';   \
\        INV Int B  <= A;  INV Int A' <= B' |] \
\     ==> LeadsTo F B B'";
by (REPEAT (ares_tac [Invariant_includes_reachable, 
		      reachable_LeadsTo_weaken] 1));
qed "Invariant_LeadsTo_weaken";


(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
Goal "[| LeadsTo F (A-B) C; LeadsTo F (A Int B) C |] \
\     ==> LeadsTo F A C";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken]) 1);
qed "LeadsTo_Diff";




val prems = 
Goal "(!! i. i:I ==> LeadsTo F (A i) (A' i)) \
\     ==> LeadsTo F (UN i:I. A i) (UN i:I. A' i)";
by (simp_tac (simpset() addsimps [Union_image_eq RS sym]) 1);
by (blast_tac (claset() addIs [LeadsTo_Union, LeadsTo_weaken_R] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN";


(*Version with no index set*)
val prems = 
Goal "(!! i. LeadsTo F (A i) (A' i)) \
\     ==> LeadsTo F (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN] 
                        addIs prems) 1);
qed "LeadsTo_UN_UN_noindex";

(*Version with no index set*)
Goal "ALL i. LeadsTo F (A i) (A' i) \
\     ==> LeadsTo F (UN i. A i) (UN i. A' i)";
by (blast_tac (claset() addIs [LeadsTo_UN_UN]) 1);
qed "all_LeadsTo_UN_UN";


(*Binary union version*)
Goal "[| LeadsTo F A A'; LeadsTo F B B' |] \
\           ==> LeadsTo F (A Un B) (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un, 
			       LeadsTo_weaken_R]) 1);
qed "LeadsTo_Un_Un";


(** The cancellation law **)

Goal "[| LeadsTo F A (A' Un B); LeadsTo F B B' |]    \
\     ==> LeadsTo F A (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un_Un, 
			       subset_imp_LeadsTo, LeadsTo_Trans]) 1);
qed "LeadsTo_cancel2";

Goal "[| LeadsTo F A (A' Un B); LeadsTo F (B-A') B' |] \
\     ==> LeadsTo F A (A' Un B')";
by (rtac LeadsTo_cancel2 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff2";

Goal "[| LeadsTo F A (B Un A'); LeadsTo F B B' |] \
\     ==> LeadsTo F A (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [LeadsTo_cancel2]) 1);
qed "LeadsTo_cancel1";

Goal "[| LeadsTo F A (B Un A'); LeadsTo F (B-A') B' |] \
\     ==> LeadsTo F A (B' Un A')";
by (rtac LeadsTo_cancel1 1);
by (assume_tac 2);
by (ALLGOALS Asm_simp_tac);
qed "LeadsTo_cancel_Diff1";



(** The impossibility law **)

(*The set "A" may be non-empty, but it contains no reachable states*)
Goal "LeadsTo F A {} ==> reachable F Int A = {}";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (etac leadsTo_empty 1);
qed "LeadsTo_empty";


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
Goal "[| LeadsTo F A A';  Stable F B |] ==> LeadsTo F (A Int B) (A' Int B)";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, Stable_eq_stable]) 1);
by (dtac psp_stable 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps Int_ac) 1);
qed "PSP_stable";

Goal "[| LeadsTo F A A'; Stable F B |] \
\     ==> LeadsTo F (B Int A) (B Int A')";
by (asm_simp_tac (simpset() addsimps PSP_stable::Int_ac) 1);
qed "PSP_stable2";

Goalw [LeadsTo_def, Constrains_def]
     "[| LeadsTo F A A'; Constrains F B B' |] \
\     ==> LeadsTo F (A Int B) ((A' Int B) Un (B' - B))";
by (blast_tac (claset() addDs [psp] addIs [leadsTo_weaken]) 1);
qed "PSP";

Goal "[| LeadsTo F A A'; Constrains F B B' |] \
\     ==> LeadsTo F (B Int A) ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps PSP::Int_ac) 1);
qed "PSP2";

Goalw [Unless_def]
     "[| LeadsTo F A A'; Unless F B B' |] \
\     ==> LeadsTo F (A Int B) ((A' Int B) Un B')";
by (dtac PSP 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [LeadsTo_Diff, LeadsTo_weaken, 
			       subset_imp_LeadsTo]) 1);
qed "PSP_Unless";


(*** Induction rules ***)

(** Meta or object quantifier ????? **)
Goal "[| wf r;     \
\        ALL m. LeadsTo F (A Int f-``{m})                     \
\                           ((A Int f-``(r^-1 ^^ {m})) Un B) |] \
\     ==> LeadsTo F A B";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (etac leadsTo_wf_induct 1);
by (Simp_tac 2);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
qed "LeadsTo_wf_induct";


Goal "[| wf r;     \
\        ALL m:I. LeadsTo F (A Int f-``{m})                   \
\                             ((A Int f-``(r^-1 ^^ {m})) Un B) |] \
\     ==> LeadsTo F A ((A - (f-``I)) Un B)";
by (etac LeadsTo_wf_induct 1);
by Safe_tac;
by (case_tac "m:I" 1);
by (blast_tac (claset() addIs [LeadsTo_weaken]) 1);
by (blast_tac (claset() addIs [subset_imp_LeadsTo]) 1);
qed "Bounded_induct";


Goal "[| ALL m. LeadsTo F (A Int f-``{m})                     \
\                           ((A Int f-``(lessThan m)) Un B) |] \
\     ==> LeadsTo F A B";
by (rtac (wf_less_than RS LeadsTo_wf_induct) 1);
by (Asm_simp_tac 1);
qed "LessThan_induct";

(*Integer version.  Could generalize from #0 to any lower bound*)
val [reach, prem] =
Goal "[| reachable F <= {s. #0 <= f s};  \
\        !! z. LeadsTo F (A Int {s. f s = z})                     \
\                           ((A Int {s. f s < z}) Un B) |] \
\     ==> LeadsTo F A B";
by (res_inst_tac [("f", "nat o f")] (allI RS LessThan_induct) 1);
by (simp_tac (simpset() addsimps [vimage_def]) 1);
by (rtac ([reach, prem] MRS reachable_LeadsTo_weaken) 1);
by (auto_tac (claset(), simpset() addsimps [nat_eq_iff, nat_less_iff]));
qed "integ_0_le_induct";

Goal "[| ALL m:(greaterThan l). LeadsTo F (A Int f-``{m})   \
\                                        ((A Int f-``(lessThan m)) Un B) |] \
\           ==> LeadsTo F A ((A Int (f-``(atMost l))) Un B)";
by (simp_tac (HOL_ss addsimps [Diff_eq RS sym, vimage_Compl, Compl_greaterThan RS sym]) 1);
by (rtac (wf_less_than RS Bounded_induct) 1);
by (Asm_simp_tac 1);
qed "LessThan_bounded_induct";

Goal "[| ALL m:(lessThan l). LeadsTo F (A Int f-``{m})   \
\                              ((A Int f-``(greaterThan m)) Un B) |] \
\     ==> LeadsTo F A ((A Int (f-``(atLeast l))) Un B)";
by (res_inst_tac [("f","f"),("f1", "%k. l - k")]
    (wf_less_than RS wf_inv_image RS LeadsTo_wf_induct) 1);
by (simp_tac (simpset() addsimps [inv_image_def, Image_singleton]) 1);
by (Clarify_tac 1);
by (case_tac "m<l" 1);
by (blast_tac (claset() addIs [not_leE, subset_imp_LeadsTo]) 2);
by (blast_tac (claset() addIs [LeadsTo_weaken_R, diff_less_mono2]) 1);
qed "GreaterThan_bounded_induct";


(*** Completion: Binary and General Finite versions ***)

Goal "[| LeadsTo F A A';  Stable F A';   \
\        LeadsTo F B B';  Stable F B' |] \
\     ==> LeadsTo F (A Int B) (A' Int B')";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, Stable_eq_stable]) 1);
by (blast_tac (claset() addIs [stable_completion, leadsTo_weaken]) 1);
qed "Stable_completion";


Goal "finite I      \
\     ==> (ALL i:I. LeadsTo F (A i) (A' i)) -->  \
\         (ALL i:I. Stable F (A' i)) -->         \
\         LeadsTo F (INT i:I. A i) (INT i:I. A' i)";
by (etac finite_induct 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [Stable_completion, ball_Stable_INT]) 1);
qed_spec_mp "Finite_stable_completion";


Goal "[| LeadsTo F A (A' Un C);  Constrains F A' (A' Un C); \
\        LeadsTo F B (B' Un C);  Constrains F B' (B' Un C) |] \
\     ==> LeadsTo F (A Int B) ((A' Int B') Un C)";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, Constrains_def,
				       Int_Un_distrib]) 1);
by (blast_tac (claset() addIs [completion, leadsTo_weaken]) 1);
qed "Completion";


Goal "[| finite I |] \
\     ==> (ALL i:I. LeadsTo F (A i) (A' i Un C)) -->  \
\         (ALL i:I. Constrains F (A' i) (A' i Un C)) --> \
\         LeadsTo F (INT i:I. A i) ((INT i:I. A' i) Un C)";
by (etac finite_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (dtac ball_Constrains_INT 1);
by (asm_full_simp_tac (simpset() addsimps [Completion]) 1); 
qed "Finite_completion";


(*proves "ensures/leadsTo" properties when the program is specified*)
fun ensures_tac sact = 
    SELECT_GOAL
      (EVERY [REPEAT (Invariant_Int_tac 1),
	      etac Invariant_LeadsTo_Basis 1 
	          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
		  REPEAT (ares_tac [LeadsTo_Basis, ensuresI] 1),
	      res_inst_tac [("act", sact)] transient_mem 2,
                 (*simplify the command's domain*)
	      simp_tac (simpset() addsimps [Domain_def]) 3,
	      constrains_tac 1,
	      ALLGOALS Clarify_tac,
	      ALLGOALS Asm_full_simp_tac]);


