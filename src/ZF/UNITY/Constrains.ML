(*  Title:      ZF/UNITY/Constrains.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Safety relations: restricted to the set of reachable states.

Proofs ported from HOL.
*)

(*** traces and reachable ***)

Goal  "reachable(F) <= state";
by (cut_inst_tac [("F", "F")] Init_type 1);
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (cut_inst_tac [("F", "F")] reachable.dom_subset 1);
by (Blast_tac 1);
qed "reachable_type";

Goalw [st_set_def] "st_set(reachable(F))";
by (resolve_tac [reachable_type] 1);
qed "st_set_reachable";
AddIffs [st_set_reachable];

Goal "reachable(F) Int state = reachable(F)";
by (cut_facts_tac [reachable_type] 1);
by Auto_tac;
qed "reachable_Int_state";
AddIffs [reachable_Int_state];

Goal "state Int reachable(F) = reachable(F)";
by (cut_facts_tac [reachable_type] 1);
by Auto_tac;
qed "state_Int_reachable";
AddIffs [state_Int_reachable];

Goal 
"F:program ==> reachable(F)={s:state. EX evs. <s,evs>:traces(Init(F), Acts(F))}";
by (rtac equalityI 1);
by Safe_tac;
by (blast_tac (claset() addDs [reachable_type RS subsetD]) 1);
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
   addIs [stableI, constrainsI, st_setI,
          reachable_type RS subsetD] @ reachable.intrs) 1);
qed "stable_reachable";

AddSIs [stable_reachable];
Addsimps [stable_reachable];

(*The set of all reachable states is an invariant...*)
Goalw [invariant_def, initially_def]
   "F:program ==> F:invariant(reachable(F))";
by (blast_tac (claset() addIs [reachable_type RS subsetD]@reachable.intrs) 1);
qed "invariant_reachable";

(*...in fact the strongest invariant!*)
Goal "F:invariant(A) ==> reachable(F) <= A";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (cut_inst_tac [("F", "F")] Init_type 1);
by (cut_inst_tac [("F", "F")] reachable_type 1);
by (full_simp_tac (simpset() addsimps [stable_def, constrains_def, 
                                       invariant_def, initially_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset()  addIs reachable.intrs) 1));
qed "invariant_includes_reachable";

(*** Co ***)

Goal "F:B co B'==>F:(reachable(F) Int B) co (reachable(F) Int B')";
by (forward_tac [constrains_type RS subsetD] 1);
by (forward_tac [[asm_rl, asm_rl, subset_refl] MRS stable_reachable] 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [stable_def, constrains_Int])));
qed "constrains_reachable_Int";

(*Resembles the previous definition of Constrains*)
Goalw [Constrains_def]
"A Co B = {F:program. F:(reachable(F) Int A) co (reachable(F)  Int  B)}";
by (blast_tac (claset() addDs [constrains_reachable_Int, 
                                      constrains_type RS subsetD]
                        addIs [constrains_weaken]) 1);
qed "Constrains_eq_constrains";
val Constrains_def2 =  Constrains_eq_constrains RS  eq_reflection;

Goalw [Constrains_def] 
 "F:A co A' ==> F:A Co A'";
by (blast_tac (claset() addIs [constrains_weaken_L] addDs [constrainsD2]) 1);
qed "constrains_imp_Constrains";

val prems = Goalw [Constrains_def, constrains_def, st_set_def]
"[|(!!act s s'. [| act: Acts(F); <s,s'>:act; s:A |] ==> s':A'); F:program|]==>F:A Co A'";
by (auto_tac (claset(), simpset() addsimps prems));
by (blast_tac (claset() addDs [reachable_type RS subsetD]) 1);
qed "ConstrainsI";

Goalw [Constrains_def] 
 "A Co B <= program";
by (Blast_tac 1);
qed "Constrains_type";

Goal "F : 0 Co B <-> F:program";
by (auto_tac (claset() addDs [Constrains_type RS subsetD]
                       addIs [constrains_imp_Constrains], simpset()));
qed "Constrains_empty";
AddIffs [Constrains_empty];

Goalw [Constrains_def] "F : A Co state <-> F:program";
by (auto_tac (claset() addDs [Constrains_type RS subsetD]
                       addIs [constrains_imp_Constrains], simpset()));
qed "Constrains_state";
AddIffs [Constrains_state];

Goalw  [Constrains_def2] 
        "[| F : A Co A'; A'<=B' |] ==> F : A Co B'";
by (blast_tac (claset()  addIs [constrains_weaken_R]) 1);
qed "Constrains_weaken_R";

Goalw  [Constrains_def2] 
    "[| F : A Co A'; B<=A |] ==> F : B Co A'";
by (blast_tac (claset() addIs [constrains_weaken_L, st_set_subset]) 1);
qed "Constrains_weaken_L";  

Goalw [Constrains_def2]
   "[| F : A Co A'; B<=A; A'<=B' |] ==> F : B Co B'";
by (blast_tac (claset() addIs [constrains_weaken, st_set_subset]) 1);
qed "Constrains_weaken";

(** Union **)
Goalw [Constrains_def2] 
"[| F : A Co A'; F : B Co B' |] ==> F : (A Un B) Co (A' Un B')";
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [Int_Un_distrib]) 1);
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "Constrains_Un";

val [major, minor] = Goalw [Constrains_def2]
"[|(!!i. i:I==>F:A(i) Co A'(i)); F:program|] ==> F:(UN i:I. A(i)) Co (UN i:I. A'(i))";
by (cut_facts_tac [minor] 1);
by (auto_tac (claset() addDs [major]
                       addIs [constrains_UN],
              simpset() delsimps UN_simps addsimps [Int_UN_distrib]));
qed "Constrains_UN";

(** Intersection **)

Goalw [Constrains_def]
"[| F : A Co A'; F : B Co B'|]==> F:(A Int B) Co (A' Int B')";
by (subgoal_tac "reachable(F) Int (A Int B) = \
              \ (reachable(F) Int A) Int (reachable(F) Int B)" 1);
by (ALLGOALS(force_tac (claset() addIs [constrains_Int], simpset())));
qed "Constrains_Int";

val [major,minor] = Goal 
"[| (!!i. i:I ==>F: A(i) Co A'(i)); F:program  |] \
\  ==> F:(INT i:I. A(i)) Co (INT i:I. A'(i))";
by (cut_facts_tac [minor] 1);
by (case_tac "I=0" 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_def]) 1);
by (subgoal_tac "reachable(F) Int Inter(RepFun(I, A)) = (INT i:I. reachable(F) Int A(i))" 1);
by (force_tac (claset(), simpset() addsimps [Inter_def]) 2);
by (asm_full_simp_tac (simpset() addsimps [Constrains_def]) 1);
by (subgoal_tac "reachable(F) Int Inter(RepFun(I, A)) = (INT i:I. reachable(F) Int A(i))" 1);
by (Force_tac 2);
by (asm_simp_tac (simpset() delsimps INT_simps) 1);
by (rtac constrains_INT 1);
by (etac not_emptyE 1);
by (dresolve_tac [major] 1);
by (rewrite_goal_tac [Constrains_def] 1);
by (ALLGOALS(Asm_full_simp_tac));
qed "Constrains_INT";

Goalw [Constrains_def] "F : A Co A' ==> reachable(F) Int A <= A'";
by (blast_tac (claset() addDs [constrains_imp_subset]) 1);
qed "Constrains_imp_subset";

Goalw [Constrains_def2]
 "[| F : A Co B; F : B Co C |] ==> F : A Co C";
by (blast_tac (claset() addIs [constrains_trans, constrains_weaken]) 1);
qed "Constrains_trans";

Goalw [Constrains_def2]
"[| F : A Co (A' Un B); F : B Co B' |] ==> F : A Co (A' Un B')";
by (full_simp_tac (simpset() addsimps [Int_Un_distrib]) 1);
by (blast_tac (claset() addIs [constrains_cancel]) 1);
qed "Constrains_cancel";

(*** Stable ***)
(* Useful because there's no Stable_weaken.  [Tanja Vos] *)

Goalw [stable_def, Stable_def] 
"F : stable(A) ==> F : Stable(A)";
by (etac constrains_imp_Constrains 1);
qed "stable_imp_Stable";

Goal "[| F: Stable(A); A = B |] ==> F : Stable(B)";
by (Blast_tac 1);
qed "Stable_eq";

Goal
"F : Stable(A) <->  (F:stable(reachable(F) Int A))";
by (auto_tac (claset() addDs [constrainsD2], 
              simpset() addsimps [Stable_def, stable_def, Constrains_def2]));
qed "Stable_eq_stable";

Goalw [Stable_def] "F:A Co A ==> F : Stable(A)";
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
by (blast_tac (claset() addIs [Constrains_Un RS Constrains_weaken_R]) 1);
qed "Stable_Constrains_Un";

Goalw [Stable_def]
    "[| F : Stable(C); F : (C Int A) Co A' |]   \
\    ==> F : (C Int A) Co (C Int A')";
by (blast_tac (claset() addIs [Constrains_Int RS Constrains_weaken]) 1);
qed "Stable_Constrains_Int";

val [major,minor] = Goalw [Stable_def]
"[| (!!i. i:I ==> F : Stable(A(i))); F:program |]==> F : Stable (UN i:I. A(i))";
by (cut_facts_tac [minor] 1);
by (blast_tac (claset() addIs [Constrains_UN,major]) 1);
qed "Stable_UN";

val [major,minor] = Goalw [Stable_def]
"[|(!!i. i:I ==> F:Stable(A(i))); F:program |]==> F : Stable (INT i:I. A(i))";
by (cut_facts_tac [minor] 1);
by (blast_tac (claset() addIs [Constrains_INT, major]) 1);
qed "Stable_INT";

Goal "F:program ==>F : Stable (reachable(F))";
by (asm_simp_tac (simpset() 
    addsimps [Stable_eq_stable, Int_absorb]) 1);
qed "Stable_reachable";

Goalw [Stable_def]
"Stable(A) <= program";
by (rtac Constrains_type 1);
qed "Stable_type";

(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be !!m instead of ALL m ?  Would make it harder to use
     in forward proof. ***)

Goalw [Constrains_def]  
"[| ALL m:M. F : ({s:A. x(s) = m}) Co (B(m)); F:program |] \
\    ==> F : ({s:A. x(s):M}) Co (UN m:M. B(m))";
by Auto_tac;
by (res_inst_tac [("A1","reachable(F)Int A")] (elimination RS constrains_weaken_L) 1);
by (auto_tac (claset() addIs [constrains_weaken_L], simpset()));
qed "Elimination";

(* As above, but for the special case of A=state *)
Goal
 "[| ALL m:M. F : {s:state. x(s) = m} Co B(m); F:program |] \
\    ==> F : {s:state. x(s):M} Co (UN m:M. B(m))";
by (blast_tac (claset() addIs [Elimination]) 1);
qed "Elimination2";

(** Unless **)

Goalw [Unless_def] "A Unless B <=program";
by (rtac Constrains_type 1);
qed "Unless_type";

(*** Specialized laws for handling Always ***)

(** Natural deduction rules for "Always A" **)

Goalw [Always_def, initially_def]
"[| Init(F)<=A;  F : Stable(A) |] ==> F : Always(A)";
by (forward_tac [Stable_type RS subsetD] 1);
by Auto_tac;
qed "AlwaysI";

Goal "F : Always(A) ==> Init(F)<=A & F : Stable(A)";
by (asm_full_simp_tac (simpset() addsimps [Always_def, initially_def]) 1);
qed "AlwaysD";

bind_thm ("AlwaysE", AlwaysD RS conjE);
bind_thm ("Always_imp_Stable", AlwaysD RS conjunct2);

(*The set of all reachable states is Always*)
Goal "F : Always(A) ==> reachable(F) <= A";
by (full_simp_tac (simpset() addsimps 
        [Stable_def, Constrains_def, constrains_def, Always_def, initially_def]) 1);
by (rtac subsetI 1);
by (etac reachable.induct 1);
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "Always_includes_reachable";

Goalw [Always_def, invariant_def, Stable_def, stable_def]
     "F : invariant(A) ==> F : Always(A)";
by (blast_tac (claset() addIs [constrains_imp_Constrains]) 1);
qed "invariant_imp_Always";

bind_thm ("Always_reachable", invariant_reachable RS invariant_imp_Always);

Goal "Always(A) = {F:program. F : invariant(reachable(F) Int A)}";
by (simp_tac (simpset() addsimps [Always_def, invariant_def, Stable_def, 
                                  Constrains_def2, stable_def, initially_def]) 1);
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (REPEAT(blast_tac (claset() addIs reachable.intrs@[reachable_type]) 1));
qed "Always_eq_invariant_reachable";

(*the RHS is the traditional definition of the "always" operator*)
Goal "Always(A) = {F:program. reachable(F) <= A}";
br equalityI 1;
by (ALLGOALS(Clarify_tac));
by (auto_tac (claset() addDs [invariant_includes_reachable],
              simpset() addsimps [subset_Int_iff, invariant_reachable,
                                  Always_eq_invariant_reachable]));
qed "Always_eq_includes_reachable";

Goalw [Always_def, initially_def] "Always(A) <= program";
by Auto_tac;
qed "Always_type";

Goal "Always(state) = program";
br equalityI 1;
by (auto_tac (claset() addDs [Always_type RS subsetD, 
                              reachable_type RS subsetD], 
              simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_state_eq";
Addsimps [Always_state_eq];

Goal "F:program ==> F : Always(state)";
by (auto_tac (claset() addDs [reachable_type RS subsetD], simpset() 
    addsimps [Always_eq_includes_reachable]));
qed "state_AlwaysI";

Goal "st_set(A) ==> Always(A) = (UN I: Pow(A). invariant(I))";
by (simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (REPEAT(blast_tac (claset() 
         addIs [invariantI, impOfSubs Init_into_reachable, 
         impOfSubs invariant_includes_reachable]
                        addDs [invariant_type RS subsetD]) 1));
qed "Always_eq_UN_invariant";

Goal "[| F : Always(A); A <= B |] ==> F : Always(B)";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_weaken";


(*** "Co" rules involving Always ***)
val Int_absorb2 = rewrite_rule [iff_def] subset_Int_iff RS conjunct1 RS mp;

Goal "F:Always(I) ==> (F:(I Int A) Co A') <-> (F : A Co A')";
by (asm_simp_tac
    (simpset() addsimps [Always_includes_reachable RS Int_absorb2,
                         Constrains_def, Int_assoc RS sym]) 1);
qed "Always_Constrains_pre";

Goal "F:Always(I) ==> (F : A Co (I Int A')) <->(F : A Co A')";
by (asm_simp_tac
    (simpset() addsimps [Always_includes_reachable RS Int_absorb2,
                         Constrains_eq_constrains, Int_assoc RS sym]) 1);
qed "Always_Constrains_post";

Goal "[| F : Always(I);  F : (I Int A) Co A' |] ==> F : A Co A'";
by (blast_tac (claset() addIs [Always_Constrains_pre RS iffD1]) 1);
qed "Always_ConstrainsI";

(* [| F : Always(I);  F : A Co A' |] ==> F : A Co (I Int A') *)
bind_thm ("Always_ConstrainsD", Always_Constrains_post RS iffD2);

(*The analogous proof of Always_LeadsTo_weaken doesn't terminate*)
Goal 
"[|F:Always(C); F:A Co A'; C Int B<=A; C Int A'<=B'|]==>F:B Co B'";
by (rtac Always_ConstrainsI 1);
by (dtac Always_ConstrainsD 2);
by (ALLGOALS(Asm_simp_tac));
by (blast_tac (claset() addIs [Constrains_weaken]) 1);
qed "Always_Constrains_weaken";

(** Conjoining Always properties **)
Goal "Always(A Int B) = Always(A) Int Always(B)";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_Int_distrib";

(* the premise i:I is need since INT is formally not defined for I=0 *)
Goal "i:I==>Always(INT i:I. A(i)) = (INT i:I. Always(A(i)))";
by (rtac equalityI 1);
by (auto_tac (claset(), simpset() addsimps
              [Inter_iff, Always_eq_includes_reachable]));
qed "Always_INT_distrib";


Goal "[| F:Always(A);  F:Always(B) |] ==> F:Always(A Int B)";
by (asm_simp_tac (simpset() addsimps [Always_Int_distrib]) 1);
qed "Always_Int_I";

(*Allows a kind of "implication introduction"*)
Goal "[| F:Always(A) |] ==> (F : Always(C-A Un B)) <-> (F : Always(B))";
by (auto_tac (claset(), simpset() addsimps [Always_eq_includes_reachable]));
qed "Always_Diff_Un_eq";

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

Goalw [Increasing_def] "Increasing(A,r,f) <= program";
by (auto_tac (claset() addDs [Stable_type RS subsetD]
                       addSDs [bspec], simpset() addsimps [INT_iff]));
qed "Increasing_type";

Goalw [Increasing_def]
"[| F:Increasing(A, r, f); a:A |] ==> F: Stable({s:state. <a,f`s>:r})";
by (Blast_tac 1);
qed "IncreasingD";

Goalw [Increasing_def]
"F:Increasing(A, r, f) ==> F:program & (EX a. a:A)";
by (auto_tac (claset(), simpset() addsimps [INT_iff]));
by (blast_tac (claset() addDs [Stable_type RS subsetD]) 1);
qed "IncreasingD2";

Goalw [increasing_def, Increasing_def]
     "F : increasing(A, r, f) ==> F : Increasing(A, r, f)";
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 1);
by (blast_tac (claset() addIs [stable_imp_Stable]) 1);
qed "increasing_imp_Increasing";

Goal
"F:Increasing(A, r, lam x:state. c) <-> F:program & (EX a. a:A)";
by (auto_tac (claset() addDs [IncreasingD2]
                       addIs [increasing_imp_Increasing], simpset()));
qed "Increasing_constant";
AddIffs [Increasing_constant];

Goalw [Increasing_def, Stable_def, stable_def, Constrains_def, 
        constrains_def, part_order_def, st_set_def]
"[| g:mono_map(A,r,A,r); part_order(A, r); f:state->A |] \
\  ==> Increasing(A, r,f) <= Increasing(A, r,g O f)";
by (case_tac "A=0" 1);
by (Asm_full_simp_tac 1);
by (etac not_emptyE 1);
by (Clarify_tac 1);
by (cut_inst_tac [("F", "xa")] Acts_type 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_iff, mono_map_def]) 1);
by Auto_tac;
by (dres_inst_tac [("psi", "ALL x:A. ALL xa:A. ?u(x,xa)")] asm_rl 1); 
by (dres_inst_tac [("x", "f`xf")] bspec 1);
by Auto_tac;
by (dres_inst_tac [("psi", "ALL x:A. ALL xa:A. ?u(x,xa)")] asm_rl 1); 
by (dres_inst_tac [("x", "act")] bspec 1);
by Auto_tac;
by (dres_inst_tac [("psi", "Acts(?u) <= ?v")] asm_rl 1);
by (dres_inst_tac [("psi", "?u <= state")] asm_rl 1);
by (dres_inst_tac [("c", "xe")] subsetD 1);
by (rtac imageI 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [refl_def, apply_type]) 1);
by (dres_inst_tac [("x1", "f`xf"), ("x", "f`xe")] (bspec RS bspec) 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [apply_type])));
by (res_inst_tac [("b", "g ` (f ` xf)")] trans_onD 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [apply_type])));
qed "mono_Increasing_comp";

Goalw [Increasing_def]
     "[| F:Increasing(nat, {<m,n>:nat*nat. m le n}, f); f:state->nat; k:nat |] \
\  ==> F: Stable({s:state. k < f`s})";
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 1);
by Safe_tac;
by (dres_inst_tac [("x", "succ(k)")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [apply_type, Collect_conj_eq]));
by (subgoal_tac "{x: state . f`x : nat} = state" 1);
by Auto_tac;
qed "strict_IncreasingD";

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
              (* Three subgoals *)
              rewrite_goal_tac [st_set_def] 3,
              REPEAT (Force_tac 2),
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
