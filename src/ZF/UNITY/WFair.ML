(*  Title:      HOL/UNITY/WFair.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

(*** transient ***)

Goalw [transient_def] "transient(A)<=program";
by Auto_tac;
qed "transient_type";

Goalw [transient_def] 
"F:transient(A) ==> F:program & st_set(A)";
by Auto_tac;
qed "transientD2";

Goalw [stable_def, constrains_def, transient_def]
    "[| F : stable(A); F : transient(A) |] ==> A = 0";
by (Asm_full_simp_tac 1);
by (Blast.depth_tac (claset()) 10 1);
qed "stable_transient_empty";

Goalw [transient_def, st_set_def] 
"[|F:transient(A); B<=A|] ==> F:transient(B)";
by Safe_tac;
by (res_inst_tac [("x", "act")] bexI 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Blast_tac 1);
by Auto_tac;
qed "transient_strengthen";

Goalw [transient_def] 
"[|act:Acts(F); A <= domain(act); act``A <= state-A; \
\   F:program; st_set(A)|] ==> F:transient(A)";
by (Blast_tac 1);
qed "transientI";

val major::prems = 
Goalw [transient_def] "[| F:transient(A); \
\  !!act. [| act:Acts(F);  A <= domain(act); act``A <= state-A|]==>P|]==>P";
by (rtac (major RS CollectE) 1);
by (blast_tac (claset() addIs prems) 1);
qed "transientE";

Goalw [transient_def] "transient(state) = 0";
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (cut_inst_tac [("F", "x")] Acts_type 1);
by (asm_full_simp_tac (simpset() addsimps [Diff_cancel]) 1);
by (auto_tac (claset() addIs [st0_in_state], simpset()));
qed "transient_state";

Goalw [transient_def,st_set_def] "state<=B ==> transient(B) = 0";
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (cut_inst_tac [("F", "x")] Acts_type 1);
by (asm_full_simp_tac (simpset() addsimps [Diff_cancel]) 1);
by (subgoal_tac "B=state" 1);
by (auto_tac (claset() addIs [st0_in_state], simpset()));
qed "transient_state2";

Goalw [transient_def] "transient(0) = program";
by (rtac equalityI 1);
by Auto_tac;
qed "transient_empty";

Addsimps [transient_empty, transient_state, transient_state2];

(*** ensures ***)

Goalw [ensures_def, constrains_def] "A ensures B <=program";
by Auto_tac;
qed "ensures_type";

Goalw [ensures_def]
"[|F:(A-B) co (A Un B); F:transient(A-B)|]==>F:A ensures B";
by (auto_tac (claset(), simpset() addsimps [transient_type RS subsetD]));
qed "ensuresI";

(* Added by Sidi, from Misra's notes, Progress chapter, exercise 4 *)
Goal "[| F:A co A Un B; F: transient(A) |] ==> F: A ensures B";
by (dres_inst_tac [("B", "A-B")] constrains_weaken_L 1);
by (dres_inst_tac [("B", "A-B")] transient_strengthen 2);
by (auto_tac (claset(), simpset() addsimps [ensures_def, transient_type RS subsetD]));
qed "ensuresI2";

Goalw [ensures_def] "F:A ensures B ==> F:(A-B) co (A Un B) & F:transient (A-B)";
by Auto_tac;
qed "ensuresD";

Goalw [ensures_def] "[|F:A ensures A'; A'<=B' |] ==> F:A ensures B'";
by (blast_tac (claset()  
          addIs [transient_strengthen, constrains_weaken]) 1);
qed "ensures_weaken_R";

(*The L-version (precondition strengthening) fails, but we have this*) 
Goalw [ensures_def]
     "[| F:stable(C);  F:A ensures B |] ==> F:(C Int A) ensures (C Int B)";
by (simp_tac (simpset() addsimps [Int_Un_distrib RS sym,
                                  Diff_Int_distrib RS sym]) 1);
by (blast_tac (claset() 
        addIs [transient_strengthen, 
               stable_constrains_Int, constrains_weaken]) 1); 
qed "stable_ensures_Int"; 

Goal "[|F:stable(A);  F:transient(C); A<=B Un C|] ==> F : A ensures B";
by (forward_tac [stable_type RS subsetD] 1);
by (asm_full_simp_tac (simpset() addsimps [ensures_def, stable_def]) 1);
by (Clarify_tac 1);
by (blast_tac (claset()  addIs [transient_strengthen, 
                                constrains_weaken]) 1);
qed "stable_transient_ensures";

Goal "(A ensures B) = (A unless B) Int transient (A-B)";
by (auto_tac (claset(), simpset() addsimps [ensures_def, unless_def]));
qed "ensures_eq";

Goal "[| F:program; A<=B  |] ==> F : A ensures B";
by (rewrite_goal_tac [ensures_def,constrains_def,transient_def, st_set_def] 1);
by Auto_tac;
qed "subset_imp_ensures";

(*** leadsTo ***)
val leads_left = leads.dom_subset RS subsetD RS SigmaD1;
val leads_right = leads.dom_subset RS subsetD RS SigmaD2;

Goalw [leadsTo_def]  "A leadsTo B <= program";
by Auto_tac;
qed "leadsTo_type";

Goalw [leadsTo_def, st_set_def] 
"F: A leadsTo B ==> F:program & st_set(A) & st_set(B)";
by (blast_tac (claset() addDs [leads_left, leads_right]) 1);
qed "leadsToD2";

Goalw [leadsTo_def, st_set_def] 
    "[|F:A ensures B; st_set(A); st_set(B)|] ==> F:A leadsTo B";
by (cut_facts_tac [ensures_type] 1);
by (auto_tac (claset() addIs [leads.Basis], simpset()));
qed "leadsTo_Basis";                       
AddIs [leadsTo_Basis];

(* Added by Sidi, from Misra's notes, Progress chapter, exercise number 4 *)
(* [| F:program; A<=B;  st_set(A); st_set(B) |] ==> A leadsTo B *)
bind_thm ("subset_imp_leadsTo", subset_imp_ensures RS leadsTo_Basis);

Goalw [leadsTo_def] "[|F: A leadsTo B;  F: B leadsTo C |]==>F: A leadsTo C";
by (auto_tac (claset() addIs [leads.Trans], simpset()));
qed "leadsTo_Trans";

(* Better when used in association with leadsTo_weaken_R *)
Goalw [transient_def] "F:transient(A) ==> F : A leadsTo (state-A )";
by (rtac (ensuresI RS leadsTo_Basis) 1);
by (ALLGOALS(Clarify_tac));
by (blast_tac (claset() addIs [transientI]) 2);
by (rtac constrains_weaken 1);
by Auto_tac;
qed "transient_imp_leadsTo";

(*Useful with cancellation, disjunction*)
Goal "F : A leadsTo (A' Un A') ==> F : A leadsTo A'";
by (Asm_full_simp_tac 1);
qed "leadsTo_Un_duplicate";

Goal "F : A leadsTo (A' Un C Un C) ==> F : A leadsTo (A' Un C)";
by (asm_full_simp_tac (simpset() addsimps Un_ac) 1);
qed "leadsTo_Un_duplicate2";

(*The Union introduction rule as we should have liked to state it*)
val [major, program,B]= Goalw [leadsTo_def, st_set_def]
"[|(!!A. A:S ==> F:A leadsTo B); F:program; st_set(B)|]==>F:Union(S) leadsTo B";
by (cut_facts_tac [program, B] 1);
by Auto_tac;
by (rtac leads.Union 1);
by Auto_tac;
by (ALLGOALS(dtac major));
by (auto_tac (claset() addDs [leads_left], simpset()));
qed "leadsTo_Union";

val [major,program,B] = Goalw [leadsTo_def, st_set_def] 
"[|(!!A. A:S ==>F:(A Int C) leadsTo B); F:program; st_set(B)|] \
\  ==>F:(Union(S)Int C)leadsTo B";
by (cut_facts_tac [program, B] 1);
by (asm_simp_tac (simpset() delsimps UN_simps  addsimps [Int_Union_Union]) 1);
by (resolve_tac [leads.Union] 1);
by Auto_tac;
by (ALLGOALS(dtac major));
by (auto_tac (claset() addDs [leads_left], simpset()));
qed "leadsTo_Union_Int";

val [major,program,B] = Goalw [leadsTo_def, st_set_def]
"[|(!!i. i:I ==> F : A(i) leadsTo B); F:program; st_set(B)|]==>F:(UN i:I. A(i)) leadsTo B";
by (cut_facts_tac [program, B] 1);
by (asm_simp_tac (simpset()  addsimps [Int_Union_Union]) 1);
by (rtac leads.Union 1);
by Auto_tac;
by (ALLGOALS(dtac major));
by (auto_tac (claset() addDs [leads_left], simpset()));
qed "leadsTo_UN";

(* Binary union introduction rule *)
Goal "[| F: A leadsTo C; F: B leadsTo C |] ==> F : (A Un B) leadsTo C";
by (stac Un_eq_Union 1);
by (blast_tac (claset() addIs [leadsTo_Union] addDs [leadsToD2]) 1);
qed "leadsTo_Un";

val [major, program, B] = Goal 
"[|(!!x. x:A==> F:{x} leadsTo B); F:program; st_set(B) |] ==> F:A leadsTo B";
by (res_inst_tac [("b", "A")] (UN_singleton RS subst) 1);
by (rtac leadsTo_UN 1);
by (auto_tac (claset() addDs prems, simpset() addsimps [major, program, B]));
qed "single_leadsTo_I";

Goal "[| F:program; st_set(A) |] ==> F: A leadsTo A"; 
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
qed "leadsTo_refl";

Goal "F: A leadsTo A <-> F:program & st_set(A)";
by (auto_tac (claset() addIs [leadsTo_refl]
                       addDs [leadsToD2], simpset()));
qed "leadsTo_refl_iff";

Goal "F: 0 leadsTo B <-> (F:program & st_set(B))";
by (auto_tac (claset() addIs [subset_imp_leadsTo]
                       addDs [leadsToD2], simpset()));
qed "empty_leadsTo";
AddIffs [empty_leadsTo];

Goal  "F: A leadsTo state <-> (F:program & st_set(A))";
by (auto_tac (claset() addIs [subset_imp_leadsTo]
                       addDs [leadsToD2, st_setD], simpset()));
qed "leadsTo_state";
AddIffs [leadsTo_state];

Goal "[| F:A leadsTo A'; A'<=B'; st_set(B') |] ==> F : A leadsTo B'";
by (blast_tac (claset() addDs [leadsToD2]
                        addIs [subset_imp_leadsTo,leadsTo_Trans]) 1);
qed "leadsTo_weaken_R";

Goal "[| F:A leadsTo A'; B<=A |] ==> F : B leadsTo A'";
by (ftac leadsToD2 1);
by (blast_tac (claset() addIs [leadsTo_Trans,subset_imp_leadsTo, st_set_subset]) 1);
qed_spec_mp "leadsTo_weaken_L";

Goal "[| F:A leadsTo A'; B<=A; A'<=B'; st_set(B')|]==> F:B leadsTo B'";
by (ftac leadsToD2 1);
by (blast_tac (claset() addIs [leadsTo_weaken_R, leadsTo_weaken_L, 
                               leadsTo_Trans, leadsTo_refl]) 1);
qed "leadsTo_weaken";

(* This rule has a nicer conclusion *)
Goal "[| F:transient(A); state-A<=B; st_set(B)|] ==> F:A leadsTo B";
by (ftac transientD2 1);
by (rtac leadsTo_weaken_R 1);
by (auto_tac (claset(), simpset() addsimps [transient_imp_leadsTo]));
qed "transient_imp_leadsTo2";

(*Distributes over binary unions*)
Goal "F:(A Un B) leadsTo C  <->  (F:A leadsTo C & F : B leadsTo C)";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken_L]) 1);
qed "leadsTo_Un_distrib";

Goal 
"(F:(UN i:I. A(i)) leadsTo B)<-> ((ALL i : I. F: A(i) leadsTo B) & F:program & st_set(B))";
by (blast_tac (claset() addDs [leadsToD2] 
                        addIs [leadsTo_UN, leadsTo_weaken_L]) 1);
qed "leadsTo_UN_distrib";

Goal "(F: Union(S) leadsTo B) <->  (ALL A:S. F : A leadsTo B) & F:program & st_set(B)";
by (blast_tac (claset() addDs [leadsToD2] 
                        addIs [leadsTo_Union, leadsTo_weaken_L]) 1);
qed "leadsTo_Union_distrib";

(*Set difference: maybe combine with leadsTo_weaken_L?*)
Goal "[| F: (A-B) leadsTo C; F: B leadsTo C; st_set(C) |] ==> F: A leadsTo C";
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken]
                        addDs [leadsToD2]) 1);
qed "leadsTo_Diff";

val [major,minor] = Goal 
"[|(!!i. i:I ==> F: A(i) leadsTo A'(i)); F:program |] \
\  ==> F: (UN i:I. A(i)) leadsTo (UN i:I. A'(i))";
by (rtac leadsTo_Union 1);
by (ALLGOALS(Asm_simp_tac));
by Safe_tac;
by (simp_tac (simpset() addsimps [minor]) 2);
by (blast_tac (claset() addDs [leadsToD2, major])2);
by (blast_tac (claset() addIs [leadsTo_weaken_R] addDs [major, leadsToD2]) 1);
qed "leadsTo_UN_UN";

(*Binary union version*)
Goal "[| F: A leadsTo A'; F:B leadsTo B' |] ==> F : (A Un B) leadsTo (A' Un B')";
by (subgoal_tac "st_set(A) & st_set(A') & st_set(B) & st_set(B')" 1);
by (blast_tac (claset() addDs [leadsToD2]) 2);
by (blast_tac (claset() addIs [leadsTo_Un, leadsTo_weaken_R]) 1);
qed "leadsTo_Un_Un";

(** The cancellation law **)
Goal "[|F: A leadsTo (A' Un B); F: B leadsTo B'|] ==> F: A leadsTo (A' Un B')";
by (subgoal_tac "st_set(A) & st_set(A') & st_set(B) & st_set(B') &F:program" 1);
by (blast_tac (claset() addDs [leadsToD2]) 2);
by (blast_tac (claset() addIs [leadsTo_Trans, leadsTo_Un_Un, leadsTo_refl]) 1);
qed "leadsTo_cancel2";

Goal "[|F: A leadsTo (A' Un B); F : (B-A') leadsTo B'|]==> F: A leadsTo (A' Un B')";
by (rtac leadsTo_cancel2 1);
by (assume_tac 2);
by (blast_tac (claset() addDs [leadsToD2] addIs [leadsTo_weaken_R]) 1);
qed "leadsTo_cancel_Diff2";


Goal "[| F : A leadsTo (B Un A'); F : B leadsTo B' |] ==> F:A leadsTo (B' Un A')";
by (asm_full_simp_tac (simpset() addsimps [Un_commute]) 1);
by (blast_tac (claset() addSIs [leadsTo_cancel2]) 1);
qed "leadsTo_cancel1";

Goal "[|F: A leadsTo (B Un A'); F: (B-A') leadsTo B'|]==> F : A leadsTo (B' Un A')";
by (rtac leadsTo_cancel1 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [leadsTo_weaken_R] addDs [leadsToD2]) 1);
qed "leadsTo_cancel_Diff1";

(*The INDUCTION rule as we should have liked to state it*)
val [major, basis_prem, trans_prem, union_prem] = Goalw [leadsTo_def, st_set_def]
  "[| F: za leadsTo zb; \
\     !!A B. [| F: A ensures B; st_set(A); st_set(B) |] ==> P(A, B); \
\     !!A B C. [| F: A leadsTo B; P(A, B); \
\                 F: B leadsTo C; P(B, C) |] \
\              ==> P(A, C); \
\     !!B S. [| ALL A:S. F:A leadsTo B; ALL A:S. P(A, B); st_set(B); ALL A:S. st_set(A)|] \
\        ==> P(Union(S), B) \
\  |] ==> P(za, zb)";
by (cut_facts_tac [major] 1);
by (rtac (major RS CollectD2 RS leads.induct) 1);
by (rtac union_prem 3);
by (rtac trans_prem 2);
by (rtac basis_prem 1);
by Auto_tac;
qed "leadsTo_induct";

(* Added by Sidi, an induction rule without ensures *)
val [major,imp_prem,basis_prem,trans_prem,union_prem] = Goal
  "[| F: za leadsTo zb; \
\     !!A B. [| A<=B; st_set(B) |] ==> P(A, B); \
\     !!A B. [| F:A co A Un B; F:transient(A); st_set(B) |] ==> P(A, B); \
\     !!A B C. [| F: A leadsTo B; P(A, B); \
\                 F: B leadsTo C; P(B, C) |] \
\              ==> P(A, C); \
\     !!B S. [| ALL A:S. F:A leadsTo B; ALL A:S. P(A, B); st_set(B); ALL A:S. st_set(A) |] \
\        ==> P(Union(S), B) \
\  |] ==> P(za, zb)";
by (cut_facts_tac [major] 1);
by (etac leadsTo_induct 1);
by (auto_tac (claset() addIs [trans_prem,union_prem], simpset()));
by (rewrite_goal_tac [ensures_def] 1);
by (Clarify_tac 1);
by (ftac constrainsD2 1);
by (dres_inst_tac [("B'", "(A-B) Un B")] constrains_weaken_R 1);
by (Blast_tac 1);
by (forward_tac [ensuresI2 RS leadsTo_Basis] 1);
by (dtac basis_prem 4);
by (ALLGOALS(Asm_full_simp_tac));
by (forw_inst_tac [("A1", "A"), ("B", "B")] (Int_lower2 RS imp_prem) 1);
by (subgoal_tac "A=Union({A - B, A Int B})" 1);
by (Blast_tac 2);
by (etac ssubst 1);
by (rtac union_prem 1);
by (auto_tac (claset() addIs [subset_imp_leadsTo], simpset()));
qed "leadsTo_induct2";

(** Variant induction rule: on the preconditions for B **)
(*Lemma is the weak version: can't see how to do it in one step*)
val major::prems = Goal
  "[| F : za leadsTo zb;  \
\     P(zb); \
\     !!A B. [| F : A ensures B;  P(B); st_set(A); st_set(B) |] ==> P(A); \
\     !!S. [| ALL A:S. P(A); ALL A:S. st_set(A) |] ==> P(Union(S)) \
\  |] ==> P(za)";
(*by induction on this formula*)
by (subgoal_tac "P(zb) --> P(za)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (blast_tac (claset() addIs leadsTo_refl::prems) 1);
by (rtac (major RS leadsTo_induct) 1);
by (REPEAT (blast_tac (claset() addIs prems) 1));
qed "leadsTo_induct_pre_aux";


val [major, zb_prem, basis_prem, union_prem] = Goal
  "[| F : za leadsTo zb;  \
\     P(zb); \
\     !!A B. [| F : A ensures B;  F : B leadsTo zb;  P(B); st_set(A) |] ==> P(A); \
\     !!S. ALL A:S. F : A leadsTo zb & P(A) & st_set(A) ==> P(Union(S)) \
\  |] ==> P(za)";
by (cut_facts_tac [major] 1);
by (subgoal_tac "(F : za leadsTo zb) & P(za)" 1);
by (etac conjunct2 1);
by (rtac (major RS leadsTo_induct_pre_aux) 1);
by (blast_tac (claset() addDs [leadsToD2]
                        addIs [leadsTo_Union,union_prem]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans,basis_prem, leadsTo_Basis]) 2);
by (blast_tac (claset() addIs [leadsTo_refl,zb_prem] 
                        addDs [leadsToD2]) 1);
qed "leadsTo_induct_pre";

(** The impossibility law **)
Goal
   "F : A leadsTo 0 ==> A=0";
by (etac leadsTo_induct_pre 1);
by (auto_tac (claset(), simpset() addsimps
        [ensures_def, constrains_def, transient_def, st_set_def]));
by (dtac bspec 1);
by (REPEAT(Blast_tac 1));
qed "leadsTo_empty";
Addsimps [leadsTo_empty];

(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
Goalw [stable_def]
   "[| F : A leadsTo A'; F : stable(B) |] ==> F:(A Int B) leadsTo (A' Int B)";
by (etac leadsTo_induct 1);
by (rtac leadsTo_Union_Int 3);
by (ALLGOALS(Asm_simp_tac));
by (REPEAT(blast_tac (claset() addDs [constrainsD2]) 3));
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (rtac leadsTo_Basis 1);
by (asm_full_simp_tac (simpset() 
         addsimps [ensures_def, Diff_Int_distrib RS sym, 
                   Diff_Int_distrib2 RS sym, Int_Un_distrib2 RS sym]) 1);
by (REPEAT(blast_tac (claset() 
               addIs [transient_strengthen,constrains_Int]
               addDs [constrainsD2]) 1));
qed "psp_stable";


Goal "[|F: A leadsTo A'; F : stable(B) |]==>F: (B Int A) leadsTo (B Int A')";
by (asm_simp_tac (simpset() 
             addsimps psp_stable::Int_ac) 1);
qed "psp_stable2";

Goalw [ensures_def, constrains_def, st_set_def]
"[| F: A ensures A'; F: B co B' |]==> F: (A Int B') ensures ((A' Int B) Un (B' - B))";
(*speeds up the proof*)
by (Clarify_tac 1);  
by (blast_tac (claset() addIs [transient_strengthen]) 1);
qed "psp_ensures";

Goal 
"[|F:A leadsTo A'; F: B co B'; st_set(B')|]==> F:(A Int B') leadsTo ((A' Int B) Un (B' - B))";
by (subgoal_tac "F:program & st_set(A) & st_set(A')& st_set(B)" 1);
by (blast_tac (claset() addSDs [constrainsD2, leadsToD2]) 2);
by (etac leadsTo_induct 1);
by (blast_tac (claset() addIs [leadsTo_Union_Int]) 3);
(*Transitivity case has a delicate argument involving "cancellation"*)
by (rtac leadsTo_Un_duplicate2 2);
by (etac leadsTo_cancel_Diff1 2);
by (asm_full_simp_tac (simpset() addsimps [Int_Diff, Diff_triv]) 2);
by (blast_tac (claset() addIs [leadsTo_weaken_L] 
                        addDs [constrains_imp_subset]) 2);
(*Basis case*)
by (blast_tac (claset() addIs [psp_ensures, leadsTo_Basis]) 1);
qed "psp";


Goal "[| F : A leadsTo A'; F : B co B'; st_set(B') |] \
\   ==> F : (B' Int A) leadsTo ((B Int A') Un (B' - B))";
by (asm_simp_tac (simpset() addsimps psp::Int_ac) 1);
qed "psp2";

Goalw [unless_def]
   "[| F : A leadsTo A';  F : B unless B'; st_set(B); st_set(B') |] \
\   ==> F : (A Int B) leadsTo ((A' Int B) Un B')";
by (subgoal_tac "st_set(A)&st_set(A')" 1);
by (blast_tac (claset() addDs [leadsToD2]) 2);
by (dtac psp 1);
by (assume_tac 1);
by (Blast_tac 1);
by (REPEAT(blast_tac (claset() addIs [leadsTo_weaken]) 1));
qed "psp_unless";

(*** Proving the wf induction rules ***)
(** The most general rule: r is any wf relation; f is any variant function **)
Goal "[| wf(r); \
\        m:I; \
\        field(r)<=I; \
\        F:program; st_set(B);\
\        ALL m:I. F : (A Int f-``{m}) leadsTo                     \
\                   ((A Int f-``(converse(r)``{m})) Un B) |] \
\     ==> F : (A Int f-``{m}) leadsTo B";
by (eres_inst_tac [("a","m")] wf_induct2 1);
by (ALLGOALS(Asm_simp_tac));
by (subgoal_tac "F : (A Int (f-``(converse(r)``{x}))) leadsTo B" 1);
by (stac vimage_eq_UN 2);
by (asm_simp_tac (simpset() delsimps UN_simps
			    addsimps [Int_UN_distrib]) 2);
by (blast_tac (claset() addIs [leadsTo_cancel1, leadsTo_Un_duplicate]) 1);
by (auto_tac (claset() addIs [leadsTo_UN], 
              simpset()  delsimps UN_simps addsimps [Int_UN_distrib]));
qed "leadsTo_wf_induct_aux";

(** Meta or object quantifier ? **)
Goal "[| wf(r); \
\        field(r)<=I; \
\        A<=f-``I;\ 
\        F:program; st_set(A); st_set(B); \
\        ALL m:I. F : (A Int f-``{m}) leadsTo                     \
\                   ((A Int f-``(converse(r)``{m})) Un B) |] \
\     ==> F : A leadsTo B";
by (res_inst_tac [("b", "A")] subst 1);
by (res_inst_tac [("I", "I")] leadsTo_UN 2);
by (REPEAT (assume_tac 2));
by (Clarify_tac 2);
by (eres_inst_tac [("I", "I")] leadsTo_wf_induct_aux 2);
by (REPEAT (assume_tac 2));
by (rtac equalityI 1);
by Safe_tac;
by (thin_tac "field(r)<=I" 1);
by (dres_inst_tac [("c", "x")] subsetD 1);
by Safe_tac;
by (res_inst_tac [("b", "x")] UN_I 1);
by Auto_tac;
qed "leadsTo_wf_induct";

Goalw [field_def] "field(measure(nat, %x. x)) = nat";
by (asm_full_simp_tac (simpset() addsimps [measure_def]) 1) ;
by (rtac equalityI 1);
by (force_tac (claset(), simpset()) 1);
by (Clarify_tac 1);
by (thin_tac "x~:range(?y)" 1);
by (etac nat_induct 1);
by (res_inst_tac [("b", "succ(succ(xa))")] domainI 2);
by (res_inst_tac [("b","succ(0)")] domainI 1); 
by (ALLGOALS Asm_full_simp_tac);
qed "nat_measure_field";


Goal "k<A ==> measure(A, %x. x) -`` {k} = k";
by (rtac equalityI 1);
by (auto_tac (claset(), simpset() addsimps [measure_def]));
by (blast_tac (claset() addIs [ltD]) 1); 
by (rtac vimageI 1); 
by (blast_tac (claset() addIs []) 2); 
by (asm_full_simp_tac (simpset() addsimps [lt_Ord, lt_Ord2, Ord_mem_iff_lt]) 1); 
by (blast_tac (claset() addIs [lt_trans]) 1); 
qed "Image_inverse_lessThan";

(*Alternative proof is via the lemma F : (A Int f-`(lessThan m)) leadsTo B*)
Goal
 "[| A<=f-``nat;\ 
\    F:program; st_set(A); st_set(B); \
\    ALL m:nat. F:(A Int f-``{m}) leadsTo ((A Int f -`` m) Un B) |] \
\     ==> F : A leadsTo B";
by (res_inst_tac [("A1", "nat"),("f1", "%x. x")]
        (wf_measure RS leadsTo_wf_induct) 1);
by (Clarify_tac 6);
by (ALLGOALS(asm_full_simp_tac 
          (simpset() addsimps [nat_measure_field]))); 
by (asm_simp_tac (simpset() addsimps [ltI, Image_inverse_lessThan, symmetric vimage_def]) 1); 
qed "lessThan_induct";


(*** wlt ****)

(*Misra's property W3*)
Goalw [wlt_def] "wlt(F,B) <=state";
by Auto_tac;
qed "wlt_type";

Goalw [st_set_def] "st_set(wlt(F, B))";
by (rtac wlt_type 1);
qed "wlt_st_set";
AddIffs [wlt_st_set];

Goalw [wlt_def] "F:wlt(F, B) leadsTo B <-> (F:program & st_set(B))";
by (blast_tac (claset() addDs [leadsToD2] addSIs [leadsTo_Union]) 1);
qed "wlt_leadsTo_iff";

(* [| F:program;  st_set(B) |] ==> F:wlt(F, B) leadsTo B  *)
bind_thm("wlt_leadsTo", conjI RS (wlt_leadsTo_iff RS iffD2));

Goalw [wlt_def] "F : A leadsTo B ==> A <= wlt(F, B)";
by (ftac leadsToD2 1);
by (auto_tac (claset(), simpset() addsimps [st_set_def]));
qed "leadsTo_subset";

(*Misra's property W2*)
Goal "F : A leadsTo B <-> (A <= wlt(F,B) & F:program & st_set(B))";
by Auto_tac;
by (REPEAT(blast_tac (claset() addDs [leadsToD2,leadsTo_subset]
                               addIs [leadsTo_weaken_L, wlt_leadsTo]) 1));
qed "leadsTo_eq_subset_wlt";

(*Misra's property W4*)
Goal "[| F:program; st_set(B) |] ==> B <= wlt(F,B)";
by (rtac leadsTo_subset 1);
by (asm_simp_tac (simpset() 
         addsimps [leadsTo_eq_subset_wlt RS iff_sym,
                   subset_imp_leadsTo]) 1);
qed "wlt_increasing";

(*Used in the Trans case below*)
Goalw [constrains_def, st_set_def]
   "[| B <= A2; \
\      F : (A1 - B) co (A1 Un B); \
\      F : (A2 - C) co (A2 Un C) |] \
\   ==> F : (A1 Un A2 - C) co (A1 Un A2 Un C)";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "leadsTo_123_aux";

(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
(* slightly different from the HOL one: B here is bounded *)
Goal "F : A leadsTo A' \
\     ==> EX B:Pow(state). A<=B & F:B leadsTo A' & F : (B-A') co (B Un A')";
by (ftac leadsToD2 1);
by (etac leadsTo_induct 1);
(*Basis*)
by (blast_tac (claset() addDs [ensuresD, constrainsD2, st_setD]) 1);
(*Trans*)
by (Clarify_tac 1);
by (res_inst_tac [("x", "Ba Un Bb")] bexI 1);
by (blast_tac (claset() addIs [leadsTo_123_aux,leadsTo_Un_Un, leadsTo_cancel1,
                               leadsTo_Un_duplicate]) 1);
by (Blast_tac 1);
(*Union*)
by (clarify_tac (claset() addSDs [ball_conj_distrib RS iffD1]) 1);
by (subgoal_tac "EX y. y:Pi(S, %A. {Ba:Pow(state). A<=Ba & \
                          \         F:Ba leadsTo B & F:Ba - B co Ba Un B})" 1);
by (rtac AC_ball_Pi 2);
by (ALLGOALS(Clarify_tac));
by (rotate_tac 1 2);
by (dres_inst_tac [("x", "x")] bspec 2);
by (REPEAT(Blast_tac 2));
by (res_inst_tac [("x", "UN A:S. y`A")] bexI 1);
by Safe_tac;
by (res_inst_tac [("I1", "S")] (constrains_UN RS constrains_weaken) 3);
by (rtac leadsTo_Union 2);
by (blast_tac (claset() addSDs [apply_type]) 5);  
by (ALLGOALS(Asm_full_simp_tac));
by (REPEAT(force_tac (claset() addSDs [apply_type], simpset()) 1));
qed "leadsTo_123";


(*Misra's property W5*)
Goal "[| F:program; st_set(B) |] ==>F : (wlt(F, B) - B) co (wlt(F,B))";
by (cut_inst_tac [("F","F")] (wlt_leadsTo RS leadsTo_123) 1);
by (assume_tac 1);
by (Blast_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "Ba = wlt(F,B)" 1);
by (blast_tac (claset() addDs [leadsTo_eq_subset_wlt RS iffD1]) 2);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() 
         addsimps [wlt_increasing RS (subset_Un_iff2 RS iffD1)]) 1);
qed "wlt_constrains_wlt";

(*** Completion: Binary and General Finite versions ***)

Goal "[| W = wlt(F, (B' Un C));     \
\      F : A leadsTo (A' Un C);  F : A' co (A' Un C);   \
\      F : B leadsTo (B' Un C);  F : B' co (B' Un C) |] \
\   ==> F : (A Int B) leadsTo ((A' Int B') Un C)";
by (subgoal_tac "st_set(C)&st_set(W)&st_set(W-C)&st_set(A')&st_set(A)\
\                & st_set(B) & st_set(B') & F:program" 1);
by (Asm_simp_tac 2);
by (blast_tac (claset() addSDs [leadsToD2]) 2);
by (subgoal_tac "F : (W-C) co (W Un B' Un C)" 1);
by (blast_tac (claset() addIs [[asm_rl, wlt_constrains_wlt] 
                               MRS constrains_Un RS constrains_weaken]) 2);
by (subgoal_tac "F : (W-C) co W" 1);
by (asm_full_simp_tac (simpset() addsimps  [wlt_increasing RS 
                            (subset_Un_iff2 RS iffD1), Un_assoc]) 2);
by (subgoal_tac "F : (A Int W - C) leadsTo (A' Int W Un C)" 1);
by (blast_tac (claset() addIs [wlt_leadsTo, psp RS leadsTo_weaken]) 2);
(** LEVEL 9 **)
by (subgoal_tac "F : (A' Int W Un C) leadsTo (A' Int B' Un C)" 1);
by (rtac leadsTo_Un_duplicate2 2);
by (rtac leadsTo_Un_Un 2);
by (blast_tac (claset() addIs [leadsTo_refl]) 3);
by (res_inst_tac [("A'1", "B' Un C")] (wlt_leadsTo RS psp2 RS leadsTo_weaken) 2);
by (REPEAT(Blast_tac 2));
(** LEVEL 17 **)
by (dtac leadsTo_Diff 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]
                        addDs [leadsToD2, constrainsD2]) 1); 
by (force_tac (claset(), simpset() addsimps [st_set_def]) 1);
by (subgoal_tac "A Int B <= A Int W" 1);
by (blast_tac (claset() addSDs [leadsTo_subset]
                        addSIs [subset_refl RS Int_mono]) 2);
by (blast_tac (claset() addIs [leadsTo_Trans, subset_imp_leadsTo]) 1); 
qed "completion_aux";
bind_thm("completion", refl RS completion_aux);

Goal "[| I:Fin(X); F:program; st_set(C) |] ==> \
\(ALL i:I. F : (A(i)) leadsTo (A'(i) Un C)) -->  \
\                  (ALL i:I. F : (A'(i)) co (A'(i) Un C)) --> \
\                  F : (INT i:I. A(i)) leadsTo ((INT i:I. A'(i)) Un C)";
by (etac Fin_induct 1); 
by (auto_tac (claset(), simpset() addsimps [Inter_0]));
by (rtac completion 1);
by (auto_tac (claset(), 
              simpset() delsimps INT_simps addsimps INT_extend_simps)); 
by (rtac constrains_INT 1);
by (REPEAT(Blast_tac 1));
qed "lemma";

val prems = Goal
     "[| I:Fin(X);  \
\        !!i. i:I ==> F : A(i) leadsTo (A'(i) Un C); \
\        !!i. i:I ==> F : A'(i) co (A'(i) Un C); F:program; st_set(C)|]   \
\     ==> F : (INT i:I. A(i)) leadsTo ((INT i:I. A'(i)) Un C)";
by (resolve_tac [lemma RS mp RS mp] 1);
by (resolve_tac prems 3);
by (REPEAT(blast_tac (claset() addIs prems) 1));
qed "finite_completion";

Goalw [stable_def]
     "[| F : A leadsTo A';  F : stable(A');   \
\        F : B leadsTo B';  F : stable(B') |] \
\   ==> F : (A Int B) leadsTo (A' Int B')";
by (res_inst_tac [("C1", "0")] (completion RS leadsTo_weaken_R) 1);
by (REPEAT(blast_tac (claset() addDs [leadsToD2, constrainsD2]) 5));
by (ALLGOALS(Asm_full_simp_tac));
qed "stable_completion";


val major::prems = Goalw [stable_def]
     "[| I:Fin(X); \
\        (!!i. i:I ==> F : A(i) leadsTo A'(i)); \
\        (!!i. i:I ==> F: stable(A'(i)));  F:program |] \
\     ==> F : (INT i:I. A(i)) leadsTo (INT i:I. A'(i))";
by (cut_facts_tac [major] 1);
by (subgoal_tac "st_set(INT i:I. A'(i))" 1);
by (blast_tac (claset() addDs [leadsToD2]@prems) 2);
by (res_inst_tac [("C1", "0")] (finite_completion RS leadsTo_weaken_R) 1);
by (Asm_simp_tac 1);
by (assume_tac 6);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps prems)));
by (resolve_tac prems 2);
by (resolve_tac prems 1);
by Auto_tac;
qed "finite_stable_completion";

