(*  Title:      HOL/UNITY/WFair.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

(*** transient ***)

Goalw [transient_def]
"F:transient(A) ==> F:program & A:condition";
by Auto_tac;
qed "transientD";

Goalw [stable_def, constrains_def, transient_def]
    "[| F : stable(A); F : transient(A) |] ==> A = 0";
by Auto_tac;
by (Blast_tac 1);
qed "stable_transient_empty";

Goalw [transient_def]
    "[| F : transient(A); B<=A |] ==> F : transient(B)";
by Safe_tac;
by (res_inst_tac [("x", "act")] bexI 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Blast_tac 1);
by (auto_tac (claset(), 
   simpset() addsimps [condition_def]));
qed "transient_strengthen";

Goalw [transient_def]
"[| act:Acts(F); A <= domain(act); act``A <= state-A; \
\       F:program; A:condition |] ==> F : transient(A)";
by (Blast_tac 1);
qed "transientI";

val major::prems = 
Goalw [transient_def]
    "[| F:transient(A); \
\  !!act. [| act:Acts(F);  A <= domain(act); act``A <= state-A |] ==> P |] \
\    ==> P";
by (rtac (major RS CollectE) 1);
by (blast_tac (claset() addIs prems) 1);
qed "transientE";

Goalw [transient_def] "transient(state) = 0";
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (dtac ActsD 1);
by (asm_full_simp_tac (simpset() addsimps [Diff_cancel]) 1);
by (blast_tac (claset() addSDs [state_subset_not_empty]) 1);
qed "transient_state";

Goalw [transient_def] "transient(0) = program";
by (rtac equalityI 1);
by Safe_tac;
by (subgoal_tac "Id:Acts(x)" 1);
by (Asm_simp_tac 2);
by (res_inst_tac [("x", "Id")] bexI 1);
by (ALLGOALS(Blast_tac));
qed "transient_empty";

Addsimps [transient_empty, transient_state];

(*** ensures ***)

Goalw [ensures_def]
    "[| F : (A-B) co (A Un B); F : transient(A-B) |] \
\          ==> F : A ensures B";
by (Blast_tac 1);
qed "ensuresI";

(** From Misra's notes, Progress chapter, exercise number 4 **)
Goal "[| F:A co A Un B; F: transient(A) |] ==> F: A ensures B";
by (dres_inst_tac [("B", "A-B")] constrains_weaken_L 1);
by (dres_inst_tac [("B", "A-B")] transient_strengthen 2);
by (auto_tac (claset(), simpset() addsimps [ensures_def]));
qed "ensuresI2";


Goalw [ensures_def]
    "F : A ensures B ==> F : (A-B) co (A Un B) & F : transient (A-B)";
by (Blast_tac 1);
qed "ensuresD";

Goalw [ensures_def, constrains_def]
 "F : A ensures B ==> F:program & A:condition & B:condition";
by Auto_tac;
qed "ensuresD2";

Goalw [ensures_def]
    "[| F : A ensures A'; A'<=B';  B':condition |] ==> F : A ensures B'";
by (Clarify_tac 1);
by (blast_tac (claset()  
          addIs [transient_strengthen, constrains_weaken]
          addDs [constrainsD2]) 1);   
qed "ensures_weaken_R";

(*The L-version (precondition strengthening) fails, but we have this*)
Goalw [ensures_def]
    "[| F : stable(C);  F : A ensures B |]   \
\   ==> F : (C Int A) ensures (C Int B)";
by (asm_full_simp_tac (simpset() addsimps [ensures_def,
                                  Int_Un_distrib2,
                                  Diff_Int_distrib RS sym]) 1);
by (Clarify_tac 1);
by (blast_tac (claset() 
        addIs [transient_strengthen, 
               stable_constrains_Int, constrains_weaken] 
        addDs [constrainsD2]) 1);
qed "stable_ensures_Int"; 

Goal "[| F : stable(A);  F : transient(C); \
\                A <= B Un C; B:condition|] ==> F : A ensures B";
by (asm_full_simp_tac (simpset() 
               addsimps [ensures_def, stable_def]) 1);
by (Clarify_tac 1);
by (blast_tac (claset()  addIs [transient_strengthen, 
                                constrains_weaken] 
                         addDs [constrainsD2]) 1);
qed "stable_transient_ensures";

Goal "(A ensures B) = (A unless B) Int transient (A-B)";
by (simp_tac (simpset() 
       addsimps [ensures_def, unless_def]) 1);
qed "ensures_eq";

(*** leadsTo ***)

val leads_lhs_subset = leads.dom_subset RS subsetD RS SigmaD1;
val leads_rhs_subset = leads.dom_subset RS subsetD RS SigmaD2;

Goalw [leadsTo_def]
 "F: A leadsTo B ==> F:program & A:condition & B:condition";
by (blast_tac (claset() addDs [leads_lhs_subset,
                               leads_rhs_subset]) 1);
qed "leadsToD";

Goalw [leadsTo_def] 
  "F : A ensures B ==> F : A leadsTo B";
by (blast_tac (claset() addDs [ensuresD2]
                        addIs [leads.Basis]) 1);
qed "leadsTo_Basis";                       

AddIs [leadsTo_Basis];
Addsimps [leadsTo_Basis];

Goalw [leadsTo_def]
     "[| F : A leadsTo B;  F : B leadsTo C |] ==> F : A leadsTo C";
by (blast_tac (claset() addIs [leads.Trans]) 1);
qed "leadsTo_Trans";

(* To be move to State.thy *)

Goalw [condition_def]
    "A:condition ==> state<=A <-> A=state";
by Auto_tac;
qed "state_upper";
Addsimps [state_upper];


Goalw [transient_def]
    "F : transient(A) ==> F : A leadsTo (state - A )";
by (rtac (ensuresI RS leadsTo_Basis) 1);
by (ALLGOALS(Clarify_tac));
by (blast_tac (claset() addIs [transientI]) 2);
by (rtac constrains_weaken 1);
by Auto_tac;
qed "transient_imp_leadsTo";

(*Useful with cancellation, disjunction*)

Goal "F : A leadsTo (A' Un A') ==> F : A leadsTo A'";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate";

Goal "F : A leadsTo (A' Un C Un C) ==> F : A leadsTo (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate2";

(*The Union introduction rule as we should have liked to state it*)
Goalw [leadsTo_def]
    "[|  ALL A:S. F : A leadsTo B; F:program; B:condition |]\
\ ==> F : Union(S) leadsTo B";
by (Clarify_tac 1);
by (blast_tac (claset() addIs [leads.Union] 
                        addDs [leads_lhs_subset]) 1);
bind_thm ("leadsTo_Union", ballI RS result());

Goalw [leadsTo_def]
 "[| ALL A:S. F: (A Int C) leadsTo B;  F:program; B:condition |] \
 \ ==> F : (Union(S) Int C) leadsTo B";
by (Clarify_tac 1);
by (simp_tac (simpset()  addsimps [Int_Union_Union]) 1);
by (blast_tac (claset() addIs [leads.Union] 
                        addDs [leads_lhs_subset, leads_rhs_subset]) 1);
bind_thm ("leadsTo_Union_Int", ballI RS result());

Goalw [leadsTo_def]
"[| ALL i:I. F : (A(i)) leadsTo B; F:program; B:condition |] \
\   ==> F:(UN i:I. A(i)) leadsTo B";
by (Clarify_tac 1);
by (simp_tac (simpset()  addsimps [Int_Union_Union]) 1);
by (blast_tac (claset() addIs [leads.Union] 
                        addDs [leads_lhs_subset, leads_rhs_subset]) 1);
bind_thm ("leadsTo_UN",  ballI RS result());

(*Binary union introduction rule*)
Goal "[| F: A leadsTo C; F: B leadsTo C |] ==> F : (A Un B) leadsTo C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [leadsTo_Union] 
                        addDs [leadsToD]) 1);
qed "leadsTo_Un";


Goal "[| ALL x:A. F:{x} leadsTo B; \
\        F:program; B:condition |] ==> F : A leadsTo B";
by (res_inst_tac [("b", "A")] (UN_singleton RS subst) 1);
by (blast_tac (claset() addIs [leadsTo_UN]) 1);
bind_thm("single_leadsTo_I", ballI RS result());


(*The INDUCTION rule as we should have liked to state it*)
val major::prems = Goalw [leadsTo_def]
  "[| F: za leadsTo zb; \
\     !!A B. F : A ensures B ==> P(A, B); \
\     !!A B C. [| F: A leadsTo B; P(A, B); \
\                 F: B leadsTo C; P(B, C) |] \
\              ==> P(A, C); \
\     !!B S. [| ALL A:S. F:A leadsTo B & P(A, B); B:condition |] \
\        ==> P(Union(S), B) \
\  |] ==> P(za, zb)";
by (cut_facts_tac [major] 1);
by (rtac (major RS CollectD2 RS leads.induct) 1);
by (auto_tac (claset() addIs prems, simpset()));
qed "leadsTo_induct";

Goal 
"[| A<=B; F:program; B:condition |] \
\   ==> F : A ensures B";
by (rewrite_goals_tac [ensures_def, constrains_def, 
                       transient_def, condition_def]);
by (Clarify_tac 1);
by Safe_tac;
by (res_inst_tac [("x", "Id")] bexI 5);
by (REPEAT(blast_tac (claset() addDs [Id_in_Acts]) 1));
qed "subset_imp_ensures";

bind_thm ("subset_imp_leadsTo", subset_imp_ensures RS leadsTo_Basis);
bind_thm ("leadsTo_refl", subset_refl RS subset_imp_leadsTo);

bind_thm ("empty_leadsTo", empty_subsetI RS subset_imp_leadsTo);

Addsimps [empty_leadsTo];

Goalw [condition_def]
  "[| F:program; A:condition |] ==> F: A leadsTo state";
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "leadsTo_state";
Addsimps [leadsTo_state];

(* A nicer induction rule; without ensures *)
val [major,impl,basis,trans,unionp] = Goal
  "[| F: za leadsTo zb; \
\     !!A B. [| A<=B; B:condition |] ==> P(A, B); \
\     !!A B. [| F:A co A Un B; F:transient(A) |] ==> P(A, B); \
\     !!A B C. [| F: A leadsTo B; P(A, B); \
\                 F: B leadsTo C; P(B, C) |] \
\              ==> P(A, C); \
\     !!B S. [| ALL A:S. F:A leadsTo B & P(A, B); B:condition |] \
\        ==> P(Union(S), B) \
\  |] ==> P(za, zb)";
by (cut_facts_tac [major] 1);
by (etac leadsTo_induct 1);
by (auto_tac (claset() addIs [trans,unionp], simpset()));
by (rewrite_goal_tac [ensures_def] 1);
by Auto_tac;
by (forward_tac [constrainsD2] 1);
by (dres_inst_tac [("B'", "(A-B) Un B")] constrains_weaken_R 1);
by Auto_tac;
by (forward_tac [ensuresI2 RS leadsTo_Basis] 1);
by (dtac basis 2);
by (subgoal_tac "A Int B <= B " 3);
by Auto_tac;
by (dtac impl 1);
by Auto_tac;
by (res_inst_tac [("a", "Union({A - B, A Int B})"), ("P", "%x. P(x, ?u)")] subst 1);
by (rtac unionp 2);
by (auto_tac (claset() addIs [subset_imp_leadsTo], simpset()));
qed "leadsTo_induct2";



(** Variant induction rule: on the preconditions for B **)
(*Lemma is the weak version: can't see how to do it in one step*)
val major::prems = Goal
  "[| F : za leadsTo zb;  \
\     P(zb); \
\     !!A B. [| F : A ensures B;  P(B) |] ==> P(A); \
\     !!S. [| ALL A:S. P(A) |] ==> P(Union(S)) \
\  |] ==> P(za)";
(*by induction on this formula*)
by (subgoal_tac "P(zb) --> P(za)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (blast_tac (claset() addIs leadsTo_refl::prems) 1);
by (rtac (major RS leadsTo_induct) 1);
by (REPEAT (blast_tac (claset() addIs prems) 1));
qed "lemma";


val [major, cond, ensuresp, unionp] = Goal
  "[| F : za leadsTo zb;  \
\     P(zb); \
\     !!A B. [| F : A ensures B;  F : B leadsTo zb;  P(B) |] ==> P(A); \
\     !!S. ALL A:S. F : A leadsTo zb & P(A) ==> P(Union(S)) \
\  |] ==> P(za)";
by (cut_facts_tac [major] 1);
by (subgoal_tac "(F : za leadsTo zb) & P(za)" 1);
by (etac conjunct2 1);
by (rtac (major RS lemma) 1);
by (blast_tac (claset() addDs [leadsToD]
                        addIs [leadsTo_Union,unionp]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans,ensuresp]) 2);
by (blast_tac (claset() addIs [conjI,leadsTo_refl,cond] 
                        addDs [leadsToD]) 1);
qed "leadsTo_induct_pre";


Goal 
"[| F : A leadsTo A'; A'<=B'; B':condition |]\
\  ==> F : A leadsTo B'";
by (blast_tac (claset()  addIs [subset_imp_leadsTo, 
                                leadsTo_Trans]
                         addDs [leadsToD]) 1);
qed "leadsTo_weaken_R";


Goal "[| F : A leadsTo A'; B<=A |] ==> F : B leadsTo A'";
by (blast_tac (claset() 
        addIs [leadsTo_Trans, subset_imp_leadsTo]
        addDs [leadsToD]) 1);
qed_spec_mp "leadsTo_weaken_L";

(*Distributes over binary unions*)
Goal "F:(A Un B) leadsTo C  <->  (F:A leadsTo C & F : B leadsTo C)";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken_L]) 1);
qed "leadsTo_Un_distrib";

Goal "[| F:program; B:condition |] \
\==> F : (UN i:I. A(i)) leadsTo B  <->  (ALL i : I. F : (A(i)) leadsTo B)";
by (blast_tac (claset() addIs [leadsTo_UN, leadsTo_weaken_L]) 1);
qed "leadsTo_UN_distrib";

Goal "[| F:program; B:condition |]   \
\==> F : (Union(S)) leadsTo B <->  (ALL A:S. F : A leadsTo B)";
by (blast_tac (claset() addIs [leadsTo_Union, leadsTo_weaken_L]) 1);
qed "leadsTo_Union_distrib";

Goal 
"[| F : A leadsTo A'; B<=A; A'<=B'; B':condition |] \
\   ==> F : B leadsTo B'";
by (subgoal_tac "B:condition & A':condition" 1);
by (force_tac (claset() addSDs [leadsToD],
               simpset() addsimps [condition_def]) 2);
by (blast_tac (claset() 
     addIs [leadsTo_weaken_R, leadsTo_weaken_L, leadsTo_Trans]) 1);
qed "leadsTo_weaken";

(*Set difference: maybe combine with leadsTo_weaken_L?*)
Goal "[| F : (A-B) leadsTo C; F : B leadsTo C|]   ==> F : A leadsTo C";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken]
                        addDs [leadsToD]) 1);
qed "leadsTo_Diff";


Goal "[| ALL i:I. F : (A(i)) leadsTo (A'(i)); F:program |] \
\   ==> F:(UN i:I. A(i)) leadsTo (UN i:I. A'(i))";
by (rtac leadsTo_Union 1);
by (ALLGOALS(Clarify_tac));
by (REPEAT(blast_tac (claset()
      addIs [leadsTo_weaken_R] addDs [leadsToD]) 1));
qed "leadsTo_UN_UN";

(*Binary union version*)
Goal "[| F : A leadsTo A'; F : B leadsTo B' |] \
\     ==> F : (A Un B) leadsTo (A' Un B')";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken_R]
                        addDs [leadsToD]) 1);
qed "leadsTo_Un_Un";


(** The cancellation law **)

Goal "[| F : A leadsTo (A' Un B); F : B leadsTo B' |] \
\     ==> F : A leadsTo (A' Un B')";
by (blast_tac (claset() 
      addIs [leadsTo_Trans, leadsTo_Un_Un, leadsTo_refl]
      addDs  [leadsToD]) 1);
qed "leadsTo_cancel2";

Goal "[| F : A leadsTo (A' Un B); F : (B-A') leadsTo B' |] \
\     ==> F : A leadsTo (A' Un B')";
by (rtac leadsTo_cancel2 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [leadsTo_weaken_R]
                        addDs [leadsToD]) 1);
qed "leadsTo_cancel_Diff2";


Goal "[| F : A leadsTo (B Un A'); F : B leadsTo B' |] \
\   ==> F : A leadsTo (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [leadsTo_cancel2]) 1);
qed "leadsTo_cancel1";

Goal "[| F : A leadsTo (B Un A'); F : (B-A') leadsTo B' |] \
\   ==> F : A leadsTo (B' Un A')";
by (rtac leadsTo_cancel1 1);
by (assume_tac 2);
by (blast_tac (claset() 
        addIs [leadsTo_weaken_R]
        addDs [leadsToD]) 1);
qed "leadsTo_cancel_Diff1";

(** The impossibility law **)

Goal
   "F : A leadsTo 0 ==> A=0";
by (etac leadsTo_induct_pre 1);
by (rewrite_goals_tac 
     [ensures_def, constrains_def, transient_def]);
by Auto_tac;
by (auto_tac (claset() addSDs [Acts_type],
              simpset() addsimps 
               [actionSet_def, condition_def]));
by (blast_tac (claset() addSDs [bspec]) 1);
qed "leadsTo_empty";



(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
Goalw [stable_def]
   "[| F : A leadsTo A'; F : stable(B) |] ==> \
\  F:(A Int B) leadsTo (A' Int B)";
by (etac leadsTo_induct 1);
by (rtac leadsTo_Union_Int 3);
by (blast_tac (claset() addIs [leadsTo_Union_Int]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (rtac leadsTo_Basis 1);
by (asm_full_simp_tac (simpset() 
         addsimps [ensures_def, Diff_Int_distrib RS sym, 
                   Diff_Int_distrib2 RS sym, Int_Un_distrib RS sym]) 1);
by (REPEAT(blast_tac (claset() 
               addIs [transient_strengthen,constrains_Int]
               addDs [constrainsD2]) 1));
qed "psp_stable";


Goal
   "[| F : A leadsTo A'; F : stable(B) |] \
\ ==> F : (B Int A) leadsTo (B Int A')";
by (asm_simp_tac (simpset() 
             addsimps psp_stable::Int_ac) 1);
qed "psp_stable2";


Goalw [ensures_def, constrains_def]
   "[| F : A ensures A'; F : B co B' |] \
\   ==> F : (A Int B') ensures ((A' Int B) Un (B' - B))";
(*speeds up the proof*)
by (Clarify_tac 1);  
by (blast_tac (claset() addIs [transient_strengthen]) 1);
qed "psp_ensures";

Goal "[| F : A leadsTo A'; F : B co B' |] \
\     ==> F : (A Int B') leadsTo ((A' Int B) Un (B' - B))";
by (subgoal_tac "F:program & A:condition & \
                \ A':condition & B:condition & B':condition" 1);
by (blast_tac (claset() addDs [leadsToD, constrainsD2]) 2);
by (etac leadsTo_induct 1);
by (blast_tac (claset() addIs [leadsTo_Union_Int]) 3);
(*Transitivity case has a delicate argument involving "cancellation"*)
by (rtac leadsTo_Un_duplicate2 2);
by (etac leadsTo_cancel_Diff1 2);
by (asm_full_simp_tac (simpset() addsimps [Int_Diff, Diff_triv]) 2);
by (blast_tac (claset() addIs [leadsTo_weaken_L] 
                        addDs [constrains_imp_subset]) 2);
(*Basis case*)
by (blast_tac (claset() addIs [psp_ensures]) 1);
qed "psp";


Goal "[| F : A leadsTo A'; F : B co B' |] \
\   ==> F : (B' Int A) leadsTo ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps psp::Int_ac) 1);
qed "psp2";



Goalw [unless_def]
   "[| F : A leadsTo A';  F : B unless B' |] \
\   ==> F : (A Int B) leadsTo ((A' Int B) Un B')";
by (subgoal_tac "F:program & A:condition & A':condition &\
                \            B:condition & B':condition" 1);
by (blast_tac (claset() addDs [leadsToD, constrainsD2]) 2);
by (dtac psp 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [leadsTo_weaken]) 1);
qed "psp_unless";

(*** Proving the induction rules ***)
(** The most general rule: r is any wf relation; f is any variant function **)
Goal "[| wf(r); \
\        m:I; \
\        field(r)<=I; \
\        F:program; B:condition;\
\        ALL m:I. F : (A Int f-``{m}) leadsTo                     \
\                   ((A Int f-``(converse(r)``{m})) Un B) |] \
\     ==> F : (A Int f-``{m}) leadsTo B";
by (eres_inst_tac [("a","m")] wf_induct2 1);
by (ALLGOALS(Asm_simp_tac));
by (subgoal_tac "F : (A Int (f-``(converse(r)``{x}))) leadsTo B" 1);
by (stac vimage_eq_UN 2);
by (asm_simp_tac (simpset() addsimps [Int_UN_distrib]) 2);
by (blast_tac (claset() addIs [leadsTo_cancel1, leadsTo_Un_duplicate]) 1);
by (case_tac "converse(r)``{x}=0" 1);
by (auto_tac (claset() addSEs [not_emptyE] addSIs [leadsTo_UN], simpset()));
qed "lemma1";

(** Meta or object quantifier ? **)
Goal "[| wf(r); \
\        field(r)<=I; \
\        A<=f-``I;\ 
\        F:program; A:condition; B:condition; \
\        ALL m:I. F : (A Int f-``{m}) leadsTo                     \
\                   ((A Int f-``(converse(r)``{m})) Un B) |] \
\     ==> F : A leadsTo B";
by (res_inst_tac [("b", "A")] subst 1);
by (res_inst_tac [("I", "I")] leadsTo_UN 2);
by (REPEAT (assume_tac 2));
by (Clarify_tac 2);
by (eres_inst_tac [("I", "I")] lemma1 2);
by (REPEAT (assume_tac 2));
by (rtac equalityI 1);
by Safe_tac;
by (thin_tac "field(r)<=I" 1);
by (dres_inst_tac [("c", "x")] subsetD 1);
by Safe_tac;
by (res_inst_tac [("b", "x")] UN_I 1);
by Auto_tac;
qed "leadsTo_wf_induct";

Goalw [field_def] "field(less_than(nat)) = nat";
by (simp_tac (simpset() addsimps [less_than_equals]) 1);
by (rtac equalityI 1);
by (force_tac (claset() addSEs [rangeE], simpset()) 1);
by (Clarify_tac 1);
by (thin_tac "x~:range(?y)" 1);
by (etac nat_induct 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [domain_def])));
by (res_inst_tac [("x", "<succ(xa),succ(succ(xa))>")] ReplaceI 2);
by (res_inst_tac [("x", "<0,1>")] ReplaceI 1);
by (REPEAT(force_tac (claset() addIs [splitI], simpset()) 1));
qed "nat_less_than_field";

(*Alternative proof is via the lemma F : (A Int f-`(lessThan m)) leadsTo B*)
Goal
 "[| A<=f-``nat;\ 
\    F:program; A:condition; B:condition; \
\    ALL m:nat. F:(A Int f-``{m}) leadsTo ((A Int f-``lessThan(m,nat)) Un B) |] \
\     ==> F : A leadsTo B";
by (res_inst_tac [("A1", "nat")]
        (wf_less_than RS leadsTo_wf_induct) 1);
by (Clarify_tac 6);
by (ALLGOALS(asm_full_simp_tac 
          (simpset() addsimps [nat_less_than_field])));
by (Clarify_tac 1);
by (ALLGOALS(asm_full_simp_tac 
    (simpset() addsimps [rewrite_rule [vimage_def] Image_inverse_less_than])));
qed "lessThan_induct";


(*** wlt ****)

(*Misra's property W3*)
Goalw [wlt_def] 
"[| F:program; B:condition |] ==> F:wlt(F, B) leadsTo B";
by (blast_tac (claset() addSIs [leadsTo_Union]) 1);
qed "wlt_leadsTo";

Goalw [wlt_def] "F : A leadsTo B ==> A <= wlt(F, B)";
by (blast_tac (claset() addSIs [leadsTo_Union]
                        addDs  [leadsToD]) 1);
qed "leadsTo_subset";

(*Misra's property W2*)
Goal "[| F:program; B:condition |] ==> \
\ F : A leadsTo B <-> (A <= wlt(F,B))";
by (blast_tac (claset() 
   addSIs [leadsTo_subset, wlt_leadsTo RS leadsTo_weaken_L]) 1);
qed "leadsTo_eq_subset_wlt";

(*Misra's property W4*)
Goal "[| F:program; B:condition |] ==> B <= wlt(F,B)";
by (asm_simp_tac (simpset() 
         addsimps [leadsTo_eq_subset_wlt RS iff_sym,
                   subset_imp_leadsTo]) 1);
qed "wlt_increasing";

(*Used in the Trans case below*)
Goalw [constrains_def]
   "[| B <= A2; \
\      F : (A1 - B) co (A1 Un B); \
\      F : (A2 - C) co (A2 Un C) |] \
\   ==> F : (A1 Un A2 - C) co (A1 Un A2 Un C)";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "lemma1";



(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
(* slightly different from the HOL one: B here is bounded *)
Goal "F : A leadsTo A' \
\     ==> EX B:condition. A<=B & F:B leadsTo A' & F : (B-A') co (B Un A')";
by (forward_tac [leadsToD] 1);
by (etac leadsTo_induct 1);
(*Basis*)
by (blast_tac (claset() addDs [ensuresD, constrainsD2]) 1);
(*Trans*)
by (Clarify_tac 1);
by (res_inst_tac [("x", "Ba Un Bb")] bexI 1);
by (blast_tac (claset() addIs [lemma1,leadsTo_Un_Un, leadsTo_cancel1,
                               leadsTo_Un_duplicate]) 1);
by (Blast_tac 1);
(*Union*)
by (clarify_tac (claset() addSDs [ball_conj_distrib RS iffD1]) 1);
by (subgoal_tac "EX y. y:Pi(S, %A. {Ba:condition. A<=Ba & \
                          \         F:Ba leadsTo B & F:Ba - B co Ba Un B})" 1);
by (rtac AC_ball_Pi 2);
by (Clarify_tac 2);
by (rotate_tac 3 2);
by (blast_tac (claset() addSDs [bspec]) 2);
by (Clarify_tac 1);
by (res_inst_tac [("x", "UN A:S. y`A")] bexI 1);
by Safe_tac;
by (res_inst_tac [("I1", "S")] (constrains_UN RS constrains_weaken) 3);
by (rtac leadsTo_Union 2);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [condition_def]) 7);
by (asm_full_simp_tac (simpset() addsimps [condition_def]) 6);
by (REPEAT(blast_tac (claset() addDs [apply_type]) 1));
qed "leadsTo_123";


(*Misra's property W5*)
Goal "[| F:program; B:condition |] ==>F : (wlt(F, B) - B) co (wlt(F,B))";
by (cut_inst_tac [("F","F")] (wlt_leadsTo RS leadsTo_123) 1);
by (assume_tac 1);
by (assume_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "Ba = wlt(F,B)" 1);
by (blast_tac (claset() addDs [leadsTo_eq_subset_wlt RS iffD1]) 2);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() 
         addsimps [wlt_increasing RS (subset_Un_iff2 RS iffD1)]) 1);
qed "wlt_constrains_wlt";

Goalw [wlt_def, condition_def]
   "wlt(F,B):condition";
by Auto_tac;
qed "wlt_in_condition";

(*** Completion: Binary and General Finite versions ***)

Goal "[| W = wlt(F, (B' Un C));     \
\      F : A leadsTo (A' Un C);  F : A' co (A' Un C);   \
\      F : B leadsTo (B' Un C);  F : B' co (B' Un C) |] \
\   ==> F : (A Int B) leadsTo ((A' Int B') Un C)";
by (subgoal_tac "W:condition" 1);
by (blast_tac (claset() addIs [wlt_in_condition]) 2);
by (subgoal_tac "F : (W-C) co (W Un B' Un C)" 1);
by (blast_tac (claset() addIs [[asm_rl, wlt_constrains_wlt] 
                               MRS constrains_Un RS constrains_weaken]
                        addDs [leadsToD, constrainsD2]) 2);
by (subgoal_tac "F : (W-C) co W" 1);
by (subgoals_tac ["F:program", "(B' Un C):condition"] 2);
by (rotate_tac ~2 2);
by (asm_full_simp_tac 
    (simpset() addsimps 
                [wlt_increasing RS (subset_Un_iff2 RS iffD1), Un_assoc]) 2);
by (REPEAT(blast_tac (claset()  addDs [leadsToD, constrainsD]) 2));
by (subgoal_tac "F : (A Int W - C) leadsTo (A' Int W Un C)" 1);
by (blast_tac (claset() addIs [wlt_leadsTo, psp RS leadsTo_weaken]
                        addDs [leadsToD, constrainsD2]) 2);
(** LEVEL 6 **)
by (subgoal_tac "F : (A' Int W Un C) leadsTo (A' Int B' Un C)" 1);
by (subgoal_tac "A' Int W Un C:condition & A' Int B' Un C:condition" 2);
by (rtac leadsTo_Un_duplicate2 2);
by (blast_tac (claset() 
        addIs  [leadsTo_Un_Un, wlt_leadsTo RS 
                psp2 RS leadsTo_weaken,leadsTo_refl] 
        addDs [leadsToD, constrainsD]) 2);
by (thin_tac "W=wlt(F, B' Un C)" 2);
by (blast_tac (claset() addDs [leadsToD, constrainsD2]) 2);
by (dtac leadsTo_Diff 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo] 
                        addDs [leadsToD, constrainsD2]) 1);
by (subgoal_tac "A Int B <= A Int W" 1);
by (blast_tac (claset() addSDs [leadsTo_subset]
                        addSIs [subset_refl RS Int_mono]) 2);
(** To speed the proof **)
by (subgoal_tac "A Int B :condition & A \
               \ Int W :condition & A' Int B' Un C:condition" 1);
by (blast_tac (claset() addIs [leadsTo_Trans, subset_imp_leadsTo] 
                        addDs [leadsToD, constrainsD2]) 1);
by (blast_tac (claset() addDs [leadsToD, constrainsD2]) 1);
bind_thm("completion", refl RS result());

Goal "[| I:Fin(X); F:program; C:condition |] ==> \
\(ALL i:I. F : (A(i)) leadsTo (A'(i) Un C)) -->  \
\                  (ALL i:I. F : (A'(i)) co (A'(i) Un C)) --> \
\                  F : (INT i:I. A(i)) leadsTo ((INT i:I. A'(i)) Un C)";
by (etac Fin_induct 1);
by Auto_tac;
by (case_tac "y=0" 1);
by Auto_tac;
by (etac not_emptyE 1);
by (subgoal_tac "Inter(cons(A(x), RepFun(y, A)))= A(x) Int Inter(RepFun(y,A)) & \
               \ Inter(cons(A'(x), RepFun(y, A')))= A'(x) Int Inter(RepFun(y,A'))" 1);
by (Blast_tac 2);
by (Asm_simp_tac 1);
by (rtac completion 1);
by (subgoal_tac "Inter(RepFun(y, A')) Un C = (INT x:RepFun(y, A'). x Un C)" 4);
by (Blast_tac 5);
by (Asm_simp_tac 4);
by (rtac constrains_INT 4);
by (REPEAT(Blast_tac 1));
qed "lemma";

val prems = Goal
     "[| I:Fin(X);  \
\        !!i. i:I ==> F : A(i) leadsTo (A'(i) Un C); \
\        !!i. i:I ==> F : A'(i) co (A'(i) Un C); F:program; C:condition |]   \
\     ==> F : (INT i:I. A(i)) leadsTo ((INT i:I. A'(i)) Un C)";
by (blast_tac (claset() addIs (lemma RS mp RS mp)::prems) 1);
qed "finite_completion";

Goalw [stable_def]
     "[| F : A leadsTo A';  F : stable(A');   \
\        F : B leadsTo B';  F : stable(B') |] \
\   ==> F : (A Int B) leadsTo (A' Int B')";
by (res_inst_tac [("C1", "0")] (completion RS leadsTo_weaken_R) 1);
by (REPEAT(blast_tac (claset() addDs [leadsToD, constrainsD2]) 5));
by (ALLGOALS(Asm_full_simp_tac));
qed "stable_completion";


val prems = Goalw [stable_def]
     "[| I:Fin(X); \
\        ALL i:I. F : A(i) leadsTo A'(i); \
\        ALL i:I.  F: stable(A'(i));  F:program |] \
\     ==> F : (INT i:I. A(i)) leadsTo (INT i:I. A'(i))";
by (subgoal_tac "(INT i:I. A'(i)):condition" 1);
by (blast_tac (claset() addDs [leadsToD, constrainsD2]) 2);
by (res_inst_tac [("C1", "0")] (finite_completion RS leadsTo_weaken_R) 1);
by (assume_tac 7);
by (ALLGOALS(Asm_full_simp_tac));
by (ALLGOALS (Blast_tac));
qed "finite_stable_completion";

