(*  Title:      ZF/UNITY/Constrains.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Safety relations: restricted to the set of reachable states.

Proofs ported from HOL.
*)

(*** traces and reachable ***)

Goalw [condition_def]
  "reachable(F):condition";
by (auto_tac (claset() addSDs [reachable.dom_subset RS subsetD]
                       addDs [InitD, ActsD], simpset()));
qed "reachable_type";
Addsimps [reachable_type];
AddIs [reachable_type];

Goal "x:reachable(F) ==> x:state";
by (cut_inst_tac [("F", "F")] reachable_type 1);
by (auto_tac (claset(), simpset() addsimps [condition_def]));
qed "reachableD";

Goal "F:program ==> \
\   reachable(F) = {s:state. EX evs. <s,evs>: traces(Init(F), Acts(F))}";
by (rtac equalityI 1);
by Safe_tac;
by (blast_tac (claset() addDs [reachableD]) 1);
by (etac traces.induct 2);
by (etac reachable.induct 1);
by (ALLGOALS (blast_tac (claset() addIs reachable.intrs @ traces.intrs)));
qed "reachable_equiv_traces";

Goal "Init(F) <= reachable(F)";
by (blast_tac (claset() addIs reachable.intrs) 1);
qed "Init_into_reachable";

Goal "[| F:program; G:program; \
\   Acts(G) <= Acts(F)  |] ==> G:stable(reachable(F))";
by (blast_tac (claset() 
   addIs [stableI, constrainsI, reachable_type] @ reachable.intrs) 1);
qed "stable_reachable";

AddSIs [stable_reachable];
Addsimps [stable_reachable];

(*The set of all reachable states is an invariant...*)
Goalw [invariant_def, initially_def]
   "F:program ==> F:invariant(reachable(F))";
by (blast_tac (claset() addIs [reachable_type]@reachable.intrs) 1);
qed "invariant_reachable";

(*...in fact the strongest invariant!*)
Goal "F : invariant(A) ==> reachable(F) <= A";
by (full_simp_tac 
 (simpset() addsimps [stable_def, constrains_def, invariant_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset()  addIs reachable.intrs) 1));
qed "invariant_includes_reachable";

(*** Co ***)

(*F : B co B' ==> F : (reachable F Int B) co (reachable F Int B')*)
val lemma = subset_refl RSN (3, rewrite_rule 
            [stable_def] stable_reachable RS constrains_Int);
Goal "F:B co B' ==> F: (reachable(F) Int B) co (reachable(F) Int B')";
by (blast_tac (claset() addSIs [lemma]
                        addDs [constrainsD2]) 1);
qed "constrains_reachable_Int";

(*Resembles the previous definition of Constrains*)
Goalw [Constrains_def]
     "A Co B = \
\ {F:program. F : (reachable(F)  Int  A) co (reachable(F)  Int  B) & \
\  A:condition & B:condition}";
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (subgoal_tac "reachable(x) Int B:condition" 2);
by (blast_tac (claset() addDs [constrains_reachable_Int]
                        addIs [constrains_weaken]) 2);
by (subgoal_tac "reachable(x) Int B:condition" 1);
by (blast_tac (claset() addDs [constrains_reachable_Int]
                        addIs [constrains_weaken]) 1);
by (REPEAT(blast_tac (claset() addIs [reachable_type]) 1));
qed "Constrains_eq_constrains";

Goalw [Constrains_def] 
 "F : A co A' ==> F : A Co A'";
by (blast_tac (claset() addIs [constrains_weaken_L]
                        addDs [constrainsD2]) 1);
qed "constrains_imp_Constrains";

Goalw [stable_def, Stable_def] 
"F : stable(A) ==> F : Stable(A)";
by (etac constrains_imp_Constrains 1);
qed "stable_imp_Stable";


val prems = Goal
    "[|(!!act s s'. [| act: Acts(F);  <s,s'>:act; s:A |] \
\  ==> s':A');  F:program; A:condition; A':condition |]  ==> F:A Co A'";
by (rtac constrains_imp_Constrains 1);
by (blast_tac (claset() addIs (constrainsI::prems)) 1);
qed "ConstrainsI";

Goalw [Constrains_def] 
 "F:A Co B ==> F:program & A:condition & B:condition";
by (Blast_tac 1);
qed "ConstrainsD";

Goal "[| F:program; B:condition |] ==> F : 0 Co B";
by (blast_tac (claset() addIs 
        [constrains_imp_Constrains, constrains_empty]) 1);
qed "Constrains_empty";

Goal "[| F:program; A:condition |] ==> F : A Co state";
by (blast_tac (claset() addIs 
       [constrains_imp_Constrains, constrains_state2]) 1);
qed "Constrains_state";
Addsimps [Constrains_empty, Constrains_state];

val Constrains_def2 =  Constrains_eq_constrains RS  eq_reflection;

Goalw  [Constrains_def2] 
        "[| F : A Co A'; A'<=B'; B':condition |] ==> F : A Co B'";
by (Clarify_tac 1);
by (blast_tac (claset() 
     addIs [reachable_type, constrains_weaken_R]) 1);
qed "Constrains_weaken_R";


Goalw [condition_def]
   "[| A<=B; B:condition |] ==>A:condition";
by (Blast_tac 1);
qed "condition_subset_mono";


Goalw  [Constrains_def2] 
    "[| F : A Co A'; B<=A |] ==> F : B Co A'";
by (Clarify_tac 1);
by (forward_tac [condition_subset_mono] 1);
by (assume_tac 1);
by (blast_tac (claset() 
     addIs [reachable_type, constrains_weaken_L]) 1);
qed "Constrains_weaken_L";  

Goalw [Constrains_def]
   "[| F : A Co A'; B<=A; A'<=B'; B':condition |] ==> F : B Co B'";
by (Clarify_tac 1);
by (forward_tac [condition_subset_mono] 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [reachable_type, constrains_weaken]) 1);
qed "Constrains_weaken";

(** Union **)

Goalw [Constrains_def2]
    "[| F : A Co A'; F : B Co B' |]   \
\    ==> F : (A Un B) Co (A' Un B')";
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Int_Un_distrib2 RS sym]) 1);
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "Constrains_Un";

Goalw [Constrains_def2]
     "[| F:program; \
\     ALL i:I. F : A(i) Co A'(i)  |] \
\     ==> F : (UN i:I. A(i)) Co (UN i:I. A'(i))";
by (rtac CollectI 1);
by Safe_tac;
by (simp_tac (simpset() addsimps [Int_UN_distrib]) 1);
by (blast_tac (claset() addIs [constrains_UN, CollectD2 RS conjunct1]) 1);
by (rewrite_goals_tac [condition_def]);
by (ALLGOALS(Blast_tac));
qed "Constrains_UN";

(** Intersection **)

Goal "A Int (B Int C) = (A Int B) Int (A Int C)";
by (Blast_tac 1);
qed "Int_duplicate";

Goalw [Constrains_def]
    "[| F : A Co A'; F : B Co B' |]   \
\    ==> F : (A Int B) Co (A' Int B')";
by (Step_tac 1);
by (subgoal_tac "reachable(F) Int (A Int B) = \
                 \ (reachable(F) Int A) Int (reachable(F) Int B)" 1);
by (Blast_tac 2);
by (Asm_simp_tac 1);
by (rtac constrains_Int  1);
by (ALLGOALS(Asm_simp_tac));
qed "Constrains_Int";

Goal 
     "[| F:program; \
\         ALL i:I. F: A(i) Co A'(i)  |] \
\     ==> F : (INT i:I. A(i)) Co (INT i:I. A'(i))";
by (case_tac "I=0" 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_def]) 1);
by (subgoal_tac "reachable(F) Int Inter(RepFun(I, A)) = (INT i:I. reachable(F) Int A(i))" 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_def]) 2);
by (Blast_tac 2);
by (asm_full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (Step_tac 1);
by (rtac constrains_INT 1);
by (ALLGOALS(Asm_full_simp_tac));
by (ALLGOALS(Blast_tac));
qed "Constrains_INT";

Goal "F : A Co A' ==> reachable(F) Int A <= A'";
by (asm_full_simp_tac (simpset() addsimps 
          [Constrains_def, reachable_type]) 1);
by (blast_tac (claset() addDs [constrains_imp_subset]) 1);
qed "Constrains_imp_subset";

Goal "[| F : A Co B; F : B Co C |] ==> F : A Co C";
by (full_simp_tac (simpset() addsimps [Constrains_eq_constrains]) 1);
by (blast_tac (claset() addIs [constrains_trans, constrains_weaken]) 1);
qed "Constrains_trans";

Goal "[| F : A Co (A' Un B); F : B Co B' |] ==> F : A Co (A' Un B')";
by (full_simp_tac (simpset()
    addsimps [Constrains_eq_constrains, Int_Un_distrib2 RS sym]) 1);
by (Step_tac 1);
by (blast_tac (claset() addIs [constrains_cancel]) 1);
qed "Constrains_cancel";

(*** Stable ***)

(*Useful because there's no Stable_weaken.  [Tanja Vos]*)
Goal "[| F: Stable(A); A = B |] ==> F : Stable(B)";
by (Blast_tac 1);
qed "Stable_eq";

Goal "A:condition ==> F : Stable(A) <->  (F : stable(reachable(F) Int A))";
by (simp_tac (simpset() addsimps [Stable_def, Constrains_eq_constrains, 
                                  stable_def]) 1);
by (blast_tac (claset() addDs [constrainsD2]) 1);
qed "Stable_eq_stable";

Goalw [Stable_def] "F : A Co A ==> F : Stable(A)";
by (assume_tac 1);
qed "StableI";

Goalw [Stable_def] "F : Stable(A) ==> F : A Co A";
by (assume_tac 1);
qed "StableD";

Goalw [Stable_def]
    "[| F : Stable(A); F : Stable(A') |] ==> F : Stable(A Un A')";
by (blast_tac (claset() addIs [Constrains_Un]) 1);
qed "Stable_Un";

Goalw [Stable_def]
    "[| F : Stable(A); F : Stable(A') |] ==> F : Stable (A Int A')";
by (blast_tac (claset() addIs [Constrains_Int]) 1);
qed "Stable_Int";

Goalw [Stable_def]
    "[| F : Stable(C); F : A Co (C Un A') |]   \
\    ==> F : (C Un A) Co (C Un A')";
by (subgoal_tac "C Un A' :condition & C Un A:condition" 1);
by (blast_tac (claset() addIs [Constrains_Un RS Constrains_weaken_R]) 1);
by (blast_tac (claset() addDs [ConstrainsD]) 1);
qed "Stable_Constrains_Un";


Goalw [Stable_def]
    "[| F : Stable(C); F : (C Int A) Co A' |]   \
\    ==> F : (C Int A) Co (C Int A')";
by (blast_tac (claset() addDs [ConstrainsD]
            addIs [Constrains_Int RS Constrains_weaken]) 1);
qed "Stable_Constrains_Int";

val [major, prem] = Goalw [Stable_def]
    "[| F:program; \
\       (!!i. i:I ==> F : Stable(A(i))) |]==> F : Stable (UN i:I. A(i))";
by (cut_facts_tac [major] 1);
by (blast_tac (claset() addIs [major, Constrains_UN, prem]) 1);
qed "Stable_UN";

val [major, prem] = Goalw [Stable_def]
    "[| F:program; \
\       (!!i. i:I ==> F:Stable(A(i))) |]==> F : Stable (INT i:I. A(i))";
by (cut_facts_tac [major] 1);
by (blast_tac (claset() addIs [major, Constrains_INT, prem]) 1);
qed "Stable_INT";

Goal "F:program ==>F : Stable (reachable(F))";
by (asm_simp_tac (simpset() 
    addsimps [Stable_eq_stable, Int_absorb, subset_refl]) 1);
qed "Stable_reachable";

Goalw [Stable_def]
"F:Stable(A) ==> F:program & A:condition";
by (blast_tac (claset() addDs [ConstrainsD]) 1);
qed "StableD2";

(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be !!m instead of ALL m ?  Would make it harder to use
     in forward proof. ***)

Goalw [condition_def]
  "Collect(state,P):condition";
by Auto_tac;
qed "Collect_in_condition";
AddIffs [Collect_in_condition];

Goalw [Constrains_def]  
    "[| ALL m:M. F : {s:S. x(s) = m} Co B(m); F:program |] \
\    ==> F : {s:S. x(s):M} Co (UN m:M. B(m))";
by Safe_tac;
by (res_inst_tac [("S1", "reachable(F) Int S")]
             (elimination RS constrains_weaken_L) 1);
by Auto_tac;
by (rtac constrains_weaken_L 1);
by (auto_tac (claset(), simpset() addsimps [condition_def]));
qed "Elimination";

(* As above, but for the special case of S=state *)

Goal
 "[| ALL m:M. F : {s:state. x(s) = m} Co B(m); F:program |] \
\    ==> F : {s:state. x(s):M} Co (UN m:M. B(m))";
by (blast_tac (claset() addIs [Elimination]) 1);
qed "Elimination2";

(** Unless **)

Goalw [Unless_def]
"F:A Unless B ==> F:program & A:condition & B:condition";
by (blast_tac (claset() addDs [ConstrainsD]) 1);
qed "UnlessD";

(*** Specialized laws for handling Always ***)

(** Natural deduction rules for "Always A" **)
Goalw [Always_def, initially_def]
      "Always(A) = initially(A) Int Stable(A)";
by (blast_tac (claset() addDs [StableD2]) 1);
qed "Always_eq";

val Always_def2 = Always_eq RS eq_reflection;

Goalw [Always_def]
"[| Init(F)<=A;  F : Stable(A) |] ==> F : Always(A)";
by (asm_simp_tac (simpset() addsimps [StableD2]) 1);
qed "AlwaysI";

Goal "F : Always(A) ==> Init(F)<=A & F : Stable(A)";
by (asm_full_simp_tac (simpset() addsimps [Always_def]) 1);
qed "AlwaysD";

bind_thm ("AlwaysE", AlwaysD RS conjE);
bind_thm ("Always_imp_Stable", AlwaysD RS conjunct2);


(*The set of all reachable states is Always*)
Goal "F : Always(A) ==> reachable(F) <= A";
by (full_simp_tac 
    (simpset() addsimps [Stable_def, Constrains_def, constrains_def, 
                         Always_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Always_includes_reachable";

Goalw [Always_def2, invariant_def2, Stable_def, stable_def]
     "F : invariant(A) ==> F : Always(A)";
by (blast_tac (claset() addIs [constrains_imp_Constrains]) 1);
qed "invariant_imp_Always";

bind_thm ("Always_reachable", invariant_reachable RS invariant_imp_Always);

Goal "Always(A) = {F:program. F : invariant(reachable(F) Int A) & A:condition}";
by (simp_tac (simpset() addsimps [Always_def, invariant_def, Stable_def, 
                                  Constrains_eq_constrains, stable_def]) 1);
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (REPEAT(blast_tac (claset() addDs [constrainsD] 
                        addIs reachable.intrs@[reachable_type]) 1));
qed "Always_eq_invariant_reachable";

(*the RHS is the traditional definition of the "always" operator*)
Goal "Always(A) = {F:program. reachable(F) <= A & A:condition}";
br equalityI 1;
by (ALLGOALS(Clarify_tac));
by (auto_tac (claset() addDs [invariant_includes_reachable],
              simpset() addsimps [subset_Int_iff, invariant_reachable,
                                  Always_eq_invariant_reachable]));
qed "Always_eq_includes_reachable";

Goalw [Always_def]
"F:Always(A)==> F:program & A:condition";
by (blast_tac (claset() addDs [StableD2]) 1);
qed "AlwaysD2";

Goal "Always(state) = program";
br equalityI 1;
by (ALLGOALS(Clarify_tac));
by (blast_tac (claset() addDs [AlwaysD2]) 1);
by (auto_tac (claset() addDs [reachableD], 
             simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_state_eq";
Addsimps [Always_state_eq];

Goal "[| state <= A; F:program; A:condition |] ==> F : Always(A)";
by (auto_tac (claset(), simpset() 
    addsimps [Always_eq_includes_reachable]));
by (auto_tac (claset() addSDs [reachableD],  
              simpset() addsimps [condition_def]));
qed "state_AlwaysI";

Goal "A:condition ==> Always(A) = (UN I: Pow(A). invariant(I))";
by (simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (REPEAT(blast_tac (claset() 
         addIs [invariantI, impOfSubs Init_into_reachable, 
         impOfSubs invariant_includes_reachable]
                        addDs [invariantD2]) 1));
qed "Always_eq_UN_invariant";

Goal "[| F : Always(A); A <= B; B:condition |] ==> F : Always(B)";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_weaken";


(*** "Co" rules involving Always ***)
val Int_absorb2 = rewrite_rule [iff_def] subset_Int_iff RS conjunct1 RS mp;

Goal "[| F:Always(INV); A:condition |] \
 \  ==> (F:(INV Int A) Co A') <-> (F : A Co A')";
by (asm_simp_tac
    (simpset() addsimps [Always_includes_reachable RS Int_absorb2,
                         Constrains_def, Int_assoc RS sym]) 1);
by (blast_tac (claset() addDs [AlwaysD2]) 1);
qed "Always_Constrains_pre";

Goal "[| F : Always(INV); A':condition |] \
\  ==> (F : A Co (INV Int A')) <->(F : A Co A')";
by (asm_simp_tac
    (simpset() addsimps [Always_includes_reachable RS Int_absorb2,
                         Constrains_eq_constrains, Int_assoc RS sym]) 1);
by (blast_tac (claset() addDs [AlwaysD2]) 1);
qed "Always_Constrains_post";

(* [| F : Always INV;  F : (INV Int A) Co A' |] ==> F : A Co A' *)
bind_thm ("Always_ConstrainsI", Always_Constrains_pre RS iffD1);

(* [| F : Always INV;  F : A Co A' |] ==> F : A Co (INV Int A') *)
bind_thm ("Always_ConstrainsD", Always_Constrains_post RS iffD2);

(*The analogous proof of Always_LeadsTo_weaken doesn't terminate*)
Goal "[| F : Always(C);  F : A Co A';   \
\        C Int B <= A;   C Int A' <= B'; B:condition; B':condition |] \
\     ==> F : B Co B'";
by (rtac Always_ConstrainsI 1);
by (assume_tac 1);
by (assume_tac 1);
by (dtac Always_ConstrainsD 1);
by (assume_tac 2);
by (blast_tac (claset() addDs [ConstrainsD]) 1);
by (blast_tac (claset() addIs [Constrains_weaken]) 1);
qed "Always_Constrains_weaken";


(** Conjoining Always properties **)

Goal "[| A:condition; B:condition |] ==> \
\ Always(A Int B) = Always(A) Int Always(B)";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_Int_distrib";

(* the premise i:I is need since INT is formally not defined for I=0 *)
Goal "[| i:I; ALL i:I. A(i):condition |] \
\  ==>Always(INT i:I. A(i)) = (INT i:I. Always(A(i)))";
by (rtac equalityI 1);
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_INT_distrib";


Goal "[| F : Always(A);  F : Always(B) |] ==> F : Always(A Int B)";
by (asm_simp_tac (simpset() addsimps
                 [Always_Int_distrib,AlwaysD2]) 1);
qed "Always_Int_I";

(*Allows a kind of "implication introduction"*)
Goal "F : Always(A) ==> (F : Always (state-A Un B)) <-> (F : Always(B))";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_Compl_Un_eq";

(*Delete the nearest invariance assumption (which will be the second one
  used by Always_Int_I) *)
val Always_thin =
    read_instantiate_sg (sign_of thy)
                [("V", "?F : Always(?A)")] thin_rl;

(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
val Always_Int_tac = dtac Always_Int_I THEN' assume_tac THEN' etac Always_thin;

(*Combines a list of invariance THEOREMS into one.*)
val Always_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS Always_Int_I);

(*** Increasing ***)

Goalw [Increasing_on_def]
"[| F:Increasing_on(A, f, r); a:A |] ==> F: Stable({s:state. <a,f`s>:r})";
by (Blast_tac 1);
qed "Increasing_onD";

Goalw [Increasing_on_def]
"F:Increasing_on(A, f, r) ==> F:program & f:state->A & part_order(A,r)";
by (auto_tac (claset(), simpset() addsimps [INT_iff]));
qed "Increasing_onD2";

Goalw [Increasing_on_def, Stable_def, Constrains_def, stable_def, constrains_def, part_order_def]
     "!!f. g:mono_map(A,r,A,r) \
\  ==> Increasing_on(A, f, r) <= Increasing_on(A, g O f, r)";
by (asm_full_simp_tac (simpset() addsimps [INT_iff,condition_def, mono_map_def]) 1);
by (auto_tac (claset() addIs [comp_fun], simpset() addsimps [mono_map_def]));
by (force_tac (claset() addSDs [bspec, ActsD],  simpset()) 1);
by (subgoal_tac "xd:state" 1);
by (blast_tac (claset() addSDs [ActsD]) 2);
by (subgoal_tac "f`xe:A & f`xd:A" 1);
by (blast_tac (claset() addDs [apply_type]) 2);
by (rotate_tac 3 1);
by (dres_inst_tac [("x", "f`xe")] bspec 1);
by (Asm_simp_tac 1);
by (REPEAT(etac conjE 1));
by (rotate_tac ~3 1);
by (dres_inst_tac [("x", "xc")] bspec 1);
by (Asm_simp_tac 1);
by (dres_inst_tac [("c", "xd")] subsetD 1);
by (rtac imageI 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [refl_def]) 1);
by (dres_inst_tac [("x", "f`xe")] bspec 1);
by (dres_inst_tac [("x", "f`xd")] bspec 2);
by (ALLGOALS(Asm_simp_tac));
by (dres_inst_tac [("b", "g`(f`xe)")] trans_onD 1);
by Auto_tac;
qed "mono_Increasing_on_comp";

Goalw [increasing_on_def, Increasing_on_def]
     "F : increasing_on(A, f,r) ==> F : Increasing_on(A, f,r)";
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 1);
by (blast_tac (claset() addIs [stable_imp_Stable]) 1);
qed "increasing_on_imp_Increasing_on";

bind_thm("Increasing_on_constant",  increasing_on_constant RS increasing_on_imp_Increasing_on);
Addsimps [Increasing_on_constant];

Goalw [Increasing_on_def, nat_order_def]
     "[| F:Increasing_on(nat,f, nat_order); z:nat |] \
\  ==> F: Stable({s:state. z < f`s})";
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 1);
by Safe_tac;
by (dres_inst_tac [("x", "succ(z)")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [apply_type, Collect_conj_eq]));
by (subgoal_tac "{x: state . f ` x : nat} = state" 1);
by Auto_tac;
qed "strict_Increasing_onD";

(*To allow expansion of the program's definition when appropriate*)
val program_defs_ref = ref ([] : thm list);

(*proves "co" properties when the program is specified*)

fun constrains_tac i = 
   SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
              REPEAT (etac Always_ConstrainsI 1
                      ORELSE
                      resolve_tac [StableI, stableI,
                                   constrains_imp_Constrains] 1),
              rtac constrainsI 1,
              full_simp_tac (simpset() addsimps !program_defs_ref) 1,
              ALLGOALS Clarify_tac,
              REPEAT (FIRSTGOAL (etac disjE)),
              ALLGOALS Clarify_tac,
              REPEAT (FIRSTGOAL (etac disjE)),
              ALLGOALS Clarify_tac,
              ALLGOALS Asm_full_simp_tac,
              ALLGOALS Clarify_tac]) i;

(*For proving invariants*)
fun always_tac i = 
    rtac AlwaysI i THEN Force_tac i THEN constrains_tac i;
