(*  Title:      ZF/UNITY/SubstAx.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

LeadsTo relation, restricted to the set of reachable states.

*)


(*Resembles the previous definition of LeadsTo*)

(* Equivalence with the HOL-like definition *)
Goalw [LeadsTo_def]
"st_set(B)==> A LeadsTo B = {F:program. F:(reachable(F) Int A) leadsTo B}";
by (blast_tac (claset() addDs [psp_stable2, leadsToD2, constrainsD2] 
                        addIs [leadsTo_weaken]) 1);
qed "LeadsTo_eq";

Goalw [LeadsTo_def] "A LeadsTo B <=program";
by Auto_tac;
qed "LeadsTo_type";

(*** Specialized laws for handling invariants ***)

(** Conjoining an Always property **)
Goal "F : Always(I) ==> (F:(I Int A) LeadsTo A') <-> (F: A LeadsTo A')";
by (asm_full_simp_tac
    (simpset() addsimps [LeadsTo_def, Always_eq_includes_reachable,
              Int_absorb2, Int_assoc RS sym, leadsToD2]) 1);
qed "Always_LeadsTo_pre";

Goalw [LeadsTo_def] "F:Always(I) ==> (F : A LeadsTo (I Int A')) <-> (F : A LeadsTo A')";
by (asm_full_simp_tac (simpset() addsimps [Always_eq_includes_reachable, 
          Int_absorb2, Int_assoc RS sym,leadsToD2]) 1);
qed "Always_LeadsTo_post";

(* Like 'Always_LeadsTo_pre RS iffD1', but with premises in the good order *)
Goal "[| F:Always(C); F : (C Int A) LeadsTo A' |] ==> F: A LeadsTo A'";
by (blast_tac (claset() addIs [Always_LeadsTo_pre RS iffD1]) 1);
qed "Always_LeadsToI";

(* Like 'Always_LeadsTo_post RS iffD2', but with premises in the good order *)
Goal "[| F:Always(C);  F:A LeadsTo A' |] ==> F : A LeadsTo (C Int A')";
by (blast_tac (claset() addIs [Always_LeadsTo_post RS iffD2]) 1);
qed "Always_LeadsToD";

(*** Introduction rules: Basis, Trans, Union ***)

Goal "F : A Ensures B ==> F : A LeadsTo B";
by (auto_tac (claset(), simpset() addsimps 
                   [Ensures_def, LeadsTo_def]));
qed "LeadsTo_Basis";

Goal "[| F : A LeadsTo B;  F : B LeadsTo C |] ==> F : A LeadsTo C";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [leadsTo_Trans]) 1);
qed "LeadsTo_Trans";

val [major, program] = Goalw [LeadsTo_def]
"[|(!!A. A:S ==> F : A LeadsTo B); F:program|]==>F:Union(S) LeadsTo B";
by (cut_facts_tac [program] 1);
by Auto_tac;
by (stac Int_Union_Union2 1);
by (rtac leadsTo_UN 1);
by (dtac major 1);
by Auto_tac;
qed "LeadsTo_Union";

(*** Derived rules ***)

Goal "F : A leadsTo B ==> F : A LeadsTo B";
by (forward_tac [leadsToD2] 1);
by (Clarify_tac 1);
by (asm_simp_tac (simpset() addsimps [LeadsTo_eq]) 1);
by (blast_tac (claset() addIs [leadsTo_weaken_L]) 1);
qed "leadsTo_imp_LeadsTo";

(*Useful with cancellation, disjunction*)
Goal "F : A LeadsTo (A' Un A') ==> F : A LeadsTo A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate";

Goal "F : A LeadsTo (A' Un C Un C) ==> F : A LeadsTo (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "LeadsTo_Un_duplicate2";

val [major, program] = Goalw [LeadsTo_def] 
"[|(!!i. i:I ==> F : A(i) LeadsTo B); F:program|]==>F:(UN i:I. A(i)) LeadsTo B";
by (cut_facts_tac [program] 1);
by (asm_simp_tac (simpset() delsimps UN_simps addsimps [Int_UN_distrib]) 1);
by (rtac leadsTo_UN 1);
by (dtac major 1);
by Auto_tac;
qed "LeadsTo_UN";

(*Binary union introduction rule*)
Goal "[| F : A LeadsTo C; F : B LeadsTo C |] ==> F : (A Un B) LeadsTo C";
by (stac Un_eq_Union 1);
by (rtac LeadsTo_Union 1);
by (auto_tac (claset() addDs [LeadsTo_type RS subsetD], simpset()));
qed "LeadsTo_Un";

(*Lets us look at the starting state*)
val [major, program] = Goal 
"[|(!!s. s:A ==> F:{s} LeadsTo B); F:program|]==>F:A LeadsTo B";
by (cut_facts_tac [program] 1);
by (stac (UN_singleton RS sym) 1 THEN rtac LeadsTo_UN 1);
by (forward_tac [major] 1);
by Auto_tac;
qed "single_LeadsTo_I";

Goal "[| A <= B; F:program |] ==> F : A LeadsTo B";
by (asm_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "subset_imp_LeadsTo";

Goal "F:0 LeadsTo A <-> F:program";
by (auto_tac (claset() addDs [LeadsTo_type RS subsetD]
                       addIs [empty_subsetI RS subset_imp_LeadsTo], simpset()));
qed "empty_LeadsTo";
AddIffs [empty_LeadsTo];

Goal "F : A LeadsTo state <-> F:program";
by (auto_tac (claset() addDs [LeadsTo_type RS subsetD], 
              simpset() addsimps [LeadsTo_eq]));
qed "LeadsTo_state";
AddIffs [LeadsTo_state];

Goalw [LeadsTo_def]
 "[| F:A LeadsTo A';  A'<=B'|] ==> F : A LeadsTo B'";
by (auto_tac (claset() addIs[leadsTo_weaken_R], simpset()));
qed_spec_mp "LeadsTo_weaken_R";

Goalw [LeadsTo_def] "[| F : A LeadsTo A'; B <= A |] ==> F : B LeadsTo A'";
by (auto_tac (claset() addIs[leadsTo_weaken_L], simpset()));
qed_spec_mp "LeadsTo_weaken_L";

Goal "[| F : A LeadsTo A'; B<=A; A'<=B' |] ==> F : B LeadsTo B'";
by (blast_tac (claset() addIs [LeadsTo_weaken_R, 
                    LeadsTo_weaken_L, LeadsTo_Trans]) 1);
qed "LeadsTo_weaken";

Goal 
"[| F:Always(C);  F:A LeadsTo A'; C Int B <= A;   C Int A' <= B' |] \
\     ==> F : B LeadsTo B'";
by (blast_tac (claset() addDs [Always_LeadsToI]
                        addIs [LeadsTo_weaken, Always_LeadsToD]) 1);
qed "Always_LeadsTo_weaken";

(** Two theorems for "proof lattices" **)

Goal "F : A LeadsTo B ==> F:(A Un B) LeadsTo B";
by (blast_tac (claset() addDs [LeadsTo_type RS subsetD]
                         addIs [LeadsTo_Un, subset_imp_LeadsTo]) 1);
qed "LeadsTo_Un_post";

Goal "[| F : A LeadsTo B;  F : B LeadsTo C |] \
\     ==> F : (A Un B) LeadsTo C";
by (blast_tac (claset() addIs [LeadsTo_Un, subset_imp_LeadsTo, 
                               LeadsTo_weaken_L, LeadsTo_Trans]
                        addDs [LeadsTo_type RS subsetD]) 1);
qed "LeadsTo_Trans_Un";

(** Distributive laws **)
Goal "(F : (A Un B) LeadsTo C)  <-> (F : A LeadsTo C & F : B LeadsTo C)";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Un_distrib";

Goal "(F : (UN i:I. A(i)) LeadsTo B) <->  (ALL i : I. F : A(i) LeadsTo B) & F:program";
by (blast_tac (claset() addDs [LeadsTo_type RS subsetD]
                        addIs [LeadsTo_UN, LeadsTo_weaken_L]) 1);
qed "LeadsTo_UN_distrib";

Goal "(F:Union(S) LeadsTo B)  <->  (ALL A : S. F : A LeadsTo B) & F:program";
by (blast_tac (claset() addDs [LeadsTo_type RS subsetD] 
                        addIs [LeadsTo_Union, LeadsTo_weaken_L]) 1);
qed "LeadsTo_Union_distrib";

(** More rules using the premise "Always(I)" **)

Goal "[| F:(A-B) Co (A Un B);  F:transient (A-B) |] ==> F : A Ensures B";
by (asm_full_simp_tac
    (simpset() addsimps [Ensures_def, Constrains_eq_constrains]) 1);
by (blast_tac (claset() addIs [ensuresI, constrains_weaken, 
                               transient_strengthen]
                        addDs [constrainsD2]) 1);
qed "EnsuresI";

Goal "[| F : Always(I); F : (I Int (A-A')) Co (A Un A'); \
\        F : transient (I Int (A-A')) |]   \
\ ==> F : A LeadsTo A'";
by (rtac Always_LeadsToI 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [EnsuresI, LeadsTo_Basis,
                               Always_ConstrainsD RS Constrains_weaken, 
                               transient_strengthen]) 1);
qed "Always_LeadsTo_Basis";

(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
Goal "[| F : (A-B) LeadsTo C;  F : (A Int B) LeadsTo C |] ==> F : A LeadsTo C";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken]) 1);
qed "LeadsTo_Diff";

val [major, minor] = Goal 
"[|(!!i. i:I ==> F: A(i) LeadsTo A'(i)); F:program |] \
\     ==> F : (UN i:I. A(i)) LeadsTo (UN i:I. A'(i))";
by (cut_facts_tac [minor] 1);
by (rtac LeadsTo_Union 1);
by (ALLGOALS(Clarify_tac));
by (forward_tac [major] 1);
by (blast_tac (claset()  addIs [LeadsTo_weaken_R]) 1);
qed "LeadsTo_UN_UN";

(*Binary union version*)
Goal "[| F:A LeadsTo A'; F:B LeadsTo B' |] ==> F:(A Un B) LeadsTo (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un, LeadsTo_weaken_R]) 1);
qed "LeadsTo_Un_Un";

(** The cancellation law **)

Goal "[| F: A LeadsTo(A' Un B); F: B LeadsTo B' |] ==> F:A LeadsTo (A' Un B')";
by (blast_tac (claset() addIs [LeadsTo_Un_Un, subset_imp_LeadsTo, LeadsTo_Trans]
                        addDs [LeadsTo_type RS subsetD]) 1);
qed "LeadsTo_cancel2";

Goal "A Un (B - A) = A Un B";
by Auto_tac;
qed "Un_Diff";

Goal "[| F : A LeadsTo (A' Un B); F : (B-A') LeadsTo B' |] ==> F : A LeadsTo (A' Un B')";
by (rtac LeadsTo_cancel2 1);
by (assume_tac 2);
by (asm_simp_tac (simpset() addsimps [Un_Diff]) 1);
qed "LeadsTo_cancel_Diff2";

Goal "[| F : A LeadsTo (B Un A'); F : B LeadsTo B' |] ==> F : A LeadsTo (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [LeadsTo_cancel2]) 1);
qed "LeadsTo_cancel1";

Goal "(B - A) Un A = B Un A";
by Auto_tac;
qed "Diff_Un2";

Goal "[| F : A LeadsTo (B Un A'); F : (B-A') LeadsTo B' |] ==> F : A LeadsTo (B' Un A')";
by (rtac LeadsTo_cancel1 1);
by (assume_tac 2);
by (asm_simp_tac (simpset() addsimps [Diff_Un2]) 1);
qed "LeadsTo_cancel_Diff1";

(** The impossibility law **)

(*The set "A" may be non-empty, but it contains no reachable states*)
Goal "F : A LeadsTo 0 ==> F : Always (state -A)";
by (full_simp_tac (simpset() 
           addsimps [LeadsTo_def,Always_eq_includes_reachable]) 1);
by (cut_facts_tac [reachable_type] 1);
by (auto_tac (claset() addSDs [leadsTo_empty], simpset()));
qed "LeadsTo_empty";

(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
Goal "[| F : A LeadsTo A';  F : Stable(B) |]==> F:(A Int B) LeadsTo (A' Int B)";
by (asm_full_simp_tac (simpset() addsimps [LeadsTo_def, Stable_eq_stable]) 1);
by (Clarify_tac 1);
by (dtac psp_stable 1);
by (REPEAT(asm_full_simp_tac (simpset() addsimps (Int_absorb::Int_ac)) 1));
qed "PSP_Stable";

Goal "[| F : A LeadsTo A'; F : Stable(B) |] ==> F : (B Int A) LeadsTo (B Int A')";
by (asm_simp_tac (simpset() addsimps PSP_Stable::Int_ac) 1);
qed "PSP_Stable2";

Goal "[| F:A LeadsTo A'; F:B Co B'|]==> F : (A Int B') LeadsTo ((A' Int B) Un (B' - B))";
by (full_simp_tac (simpset() addsimps [LeadsTo_def, Constrains_eq_constrains]) 1);
by (blast_tac (claset() addDs [psp] addIs [leadsTo_weaken]) 1);
qed "PSP";

Goal "[| F : A LeadsTo A'; F : B Co B' |]==> F:(B' Int A) LeadsTo ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps PSP::Int_ac) 1);
qed "PSP2";

Goal
"[| F : A LeadsTo A'; F : B Unless B'|]==> F:(A Int B) LeadsTo ((A' Int B) Un B')";
by (rewrite_goals_tac [Unless_def]);
by (dtac PSP 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [LeadsTo_Diff, LeadsTo_weaken, subset_imp_LeadsTo]) 1);
qed "PSP_Unless";

(*** Induction rules ***)

(** Meta or object quantifier ????? **)
Goal "[| wf(r);     \
\        ALL m:I. F : (A Int f-``{m}) LeadsTo                     \
\                           ((A Int f-``(converse(r) `` {m})) Un B); \
\        field(r)<=I; A<=f-``I; F:program |] \
\     ==> F : A LeadsTo B";
by (full_simp_tac (simpset() addsimps [LeadsTo_def]) 1);
by Safe_tac;
by (eres_inst_tac [("I", "I"), ("f", "f")] leadsTo_wf_induct 1);
by (ALLGOALS(Clarify_tac));
by (dres_inst_tac [("x", "m")] bspec 2);
by Safe_tac;
by (res_inst_tac 
[("A'", "reachable(F) Int (A Int f -``(converse(r)``{m}) Un B)")]leadsTo_weaken_R 2);
by (asm_simp_tac (simpset() addsimps [Int_assoc]) 2);
by (asm_simp_tac (simpset() addsimps [Int_assoc]) 3);
by (REPEAT(Blast_tac 1));
qed "LeadsTo_wf_induct";



Goal "[| ALL m:nat. F:(A Int f-``{m}) LeadsTo ((A Int f-``lessThan(m,nat)) Un B); \
\     A<=f-``nat; F:program |] ==> F : A LeadsTo B";
by (res_inst_tac [("A1", "nat"), ("I", "nat")] (wf_less_than RS LeadsTo_wf_induct) 1);
by (ALLGOALS(asm_full_simp_tac 
          (simpset() addsimps [nat_less_than_field])));
by (Clarify_tac 1);
by (ALLGOALS(asm_full_simp_tac 
    (simpset() addsimps [rewrite_rule [vimage_def] Image_inverse_less_than])));
qed "LessThan_induct";


(****** 
 To be ported ??? I am not sure.

  integ_0_le_induct
  LessThan_bounded_induct
  GreaterThan_bounded_induct

*****)

(*** Completion: Binary and General Finite versions ***)

Goal "[| F : A LeadsTo (A' Un C);  F : A' Co (A' Un C); \
\        F : B LeadsTo (B' Un C);  F : B' Co (B' Un C) |] \
\     ==> F : (A Int B) LeadsTo ((A' Int B') Un C)";
by (full_simp_tac
    (simpset() addsimps [LeadsTo_def, Constrains_eq_constrains, 
                         Int_Un_distrib]) 1);
by Safe_tac;
by (REPEAT(Blast_tac 2));
by (blast_tac (claset() addIs [completion, leadsTo_weaken]) 1);
qed "Completion";

Goal "[| I:Fin(X);F:program |] \
\     ==> (ALL i:I. F : (A(i)) LeadsTo (A'(i) Un C)) -->  \
\         (ALL i:I. F : (A'(i)) Co (A'(i) Un C)) --> \
\         F : (INT i:I. A(i)) LeadsTo ((INT i:I. A'(i)) Un C)";
by (etac Fin_induct 1);
by (auto_tac (claset(), simpset() delsimps INT_simps
                                  addsimps [Inter_0]));
by (rtac Completion 1);
by (asm_simp_tac (simpset() delsimps INT_simps addsimps INT_extend_simps) 4);
by (rtac Constrains_INT 4);
by (REPEAT(Blast_tac 1));
val lemma = result();

val prems = Goal
     "[| I:Fin(X); !!i. i:I ==> F : A(i) LeadsTo (A'(i) Un C); \
\        !!i. i:I ==> F : A'(i) Co (A'(i) Un C); \
\        F:program |]   \
\     ==> F : (INT i:I. A(i)) LeadsTo ((INT i:I. A'(i)) Un C)";
by (blast_tac (claset() addIs (lemma RS mp RS mp)::prems) 1);
qed "Finite_completion";

Goalw [Stable_def]
     "[| F : A LeadsTo A';  F : Stable(A');   \
\        F : B LeadsTo B';  F : Stable(B') |] \
\   ==> F : (A Int B) LeadsTo (A' Int B')";
by (res_inst_tac [("C1", "0")] (Completion RS LeadsTo_weaken_R) 1);
by (Asm_full_simp_tac 5);
by (rtac subset_refl 5);
by Auto_tac;
qed "Stable_completion";

val prems = Goalw [Stable_def]
     "[| I:Fin(X); \
\        (!!i. i:I ==> F : A(i) LeadsTo A'(i)); \
\        (!!i. i:I ==>F: Stable(A'(i)));   F:program  |] \
\     ==> F : (INT i:I. A(i)) LeadsTo (INT i:I. A'(i))";
by (res_inst_tac [("C1", "0")] (Finite_completion RS LeadsTo_weaken_R) 1);
by (ALLGOALS(Simp_tac));
by (rtac subset_refl 5);
by (REPEAT(blast_tac (claset() addIs prems) 1));
qed "Finite_stable_completion";


(*proves "ensures/leadsTo" properties when the program is specified*)
fun ensures_tac sact = 
    SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
              etac Always_LeadsTo_Basis 1 
                  ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
                  REPEAT (ares_tac [LeadsTo_Basis, leadsTo_Basis,
                                    EnsuresI, ensuresI] 1),
              (*now there are two subgoals: co & transient*)
              simp_tac (simpset() addsimps !program_defs_ref) 2,
              res_inst_tac [("act", sact)] transientI 2,
                 (*simplify the command's domain*)
              simp_tac (simpset() addsimps [domain_def]) 3, 
              (* proving the domain part *)
             Clarify_tac 3, dtac swap 3, Force_tac 4,
             rtac ReplaceI 3, Force_tac 3, Force_tac 4,
             Asm_full_simp_tac 3, rtac conjI 3, Simp_tac 4,
             REPEAT (rtac update_type2 3),
             constrains_tac 1,
             ALLGOALS Clarify_tac,
             ALLGOALS (asm_full_simp_tac 
            (simpset() addsimps [st_set_def])),
                        ALLGOALS Clarify_tac,
            ALLGOALS (Asm_full_simp_tac)]);

