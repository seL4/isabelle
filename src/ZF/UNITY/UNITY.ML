(*  Title:      ZF/UNITY/UNITY.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)
From Misra, "A Logic for Concurrent Programming", 1994

Proofs ported from HOL
*)

(** SKIP **)
Goal "SKIP:program";
by (auto_tac (claset(), simpset() addsimps 
    [SKIP_def, program_def, mk_program_def, actionSet_def, cons_absorb]));
qed "SKIP_type";
AddIffs [SKIP_type];
AddTCs  [SKIP_type];

(** programify: coersion from anything to program **)

Goalw [programify_def]
"F:program ==> programify(F)=F";
by Auto_tac;
qed "programify_program";
Addsimps [programify_program];

Goalw [programify_def]
"programify(F):program";
by Auto_tac;
qed "programify_in_program";
AddIffs [programify_in_program];
AddTCs  [programify_in_program];

(** Collapsing rules: to remove programify from expressions **)
Goalw [programify_def]
"programify(programify(F))=programify(F)";
by Auto_tac;
qed "programify_idem";
Addsimps [programify_idem];

Goal
"Init(programify(F)) = Init(F)";
by (simp_tac (simpset() addsimps [Init_def]) 1);
qed "Init_programify";

Goal
"Acts(programify(F)) = Acts(F)";
by (simp_tac (simpset() addsimps [Acts_def]) 1);
qed "Acts_programify";

Goal
"AllowedActs(programify(F)) = AllowedActs(F)";
by (simp_tac (simpset() addsimps [AllowedActs_def]) 1);
qed "AllowedActs_programify";

Addsimps [Init_programify,Acts_programify,AllowedActs_programify];

(** program inspectors **)

Goal  "F:program ==>Id:RawActs(F)";
by (auto_tac (claset(), simpset() 
        addsimps [program_def, RawActs_def]));
qed "Id_in_RawActs";

Goal "Id:Acts(F)";
by (simp_tac (simpset() 
      addsimps [Id_in_RawActs, Acts_def]) 1);
qed "Id_in_Acts";

Goal  "F:program ==>Id:RawAllowedActs(F)";
by (auto_tac (claset(), simpset() 
         addsimps [program_def, RawAllowedActs_def]));
qed "Id_in_RawAllowedActs";

Goal   "Id:AllowedActs(F)";
by (simp_tac (simpset() 
     addsimps [Id_in_RawAllowedActs, AllowedActs_def]) 1);
qed "Id_in_AllowedActs";

AddIffs [Id_in_Acts, Id_in_AllowedActs];
AddTCs [Id_in_Acts, Id_in_AllowedActs];

Goal "cons(Id, Acts(F)) = Acts(F)";
by (simp_tac (simpset() addsimps [cons_absorb]) 1);
qed "cons_Id_Acts";

Goal "cons(Id, AllowedActs(F)) = AllowedActs(F)";
by (simp_tac (simpset() addsimps [cons_absorb]) 1);
qed "cons_Id_AllowedActs";

Addsimps [cons_Id_Acts, cons_Id_AllowedActs];

(** inspectors's types **)
Goal
"F:program ==> RawInit(F):condition";
by (auto_tac (claset(), simpset() 
        addsimps [program_def, RawInit_def]));
qed "RawInit_type";

Goal "Init(F):condition";
by (simp_tac (simpset() 
    addsimps [RawInit_type, Init_def]) 1);
qed "Init_type";

Goal
"F:program ==> RawActs(F):actionSet";
by (auto_tac (claset(), simpset() 
       addsimps [program_def, RawActs_def, actionSet_def]));
qed "RawActs_type";

Goal
"Acts(F):actionSet";
by (simp_tac (simpset() 
    addsimps [RawActs_type, Acts_def]) 1);
qed "Acts_type";

Goal
"F:program ==> RawAllowedActs(F):actionSet";
by (auto_tac (claset(), simpset() 
         addsimps [program_def, RawAllowedActs_def, actionSet_def]));
qed "RawAllowedActs_type";

Goal
"AllowedActs(F): actionSet";
by (simp_tac (simpset() 
     addsimps [RawAllowedActs_type, AllowedActs_def]) 1);
qed "AllowedActs_type";

AddIffs [Init_type, Acts_type, AllowedActs_type];
AddTCs  [Init_type, Acts_type, AllowedActs_type];

Goal "x:Init(F) ==> x:state";
by (cut_inst_tac [("F", "F")] Init_type 1);
by (auto_tac (claset(), simpset() addsimps [condition_def]));
qed "InitD";

Goal "act:Acts(F) ==> act<=state*state";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (rewrite_goals_tac [actionSet_def]);
by Auto_tac;
qed "ActsD";


Goal "act:AllowedActs(F) ==> act<=state*state";
by (cut_inst_tac [("F", "F")] AllowedActs_type 1);
by (rewrite_goals_tac [actionSet_def]);
by Auto_tac;
qed "AllowedActsD";

(** More simplification rules involving state 
    and Init, Acts, and AllowedActs **)

Goal "state <= Init(F) <-> Init(F)=state";
by (cut_inst_tac [("F", "F")] Init_type 1);
by (auto_tac (claset(), 
      simpset() addsimps [condition_def]));
qed "Init_state_eq";

Goal "action <= Acts(F) <-> Acts(F)=action";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (auto_tac (claset(), 
      simpset() addsimps [actionSet_def]));
qed "Acts_action_eq";

Goal "action <= AllowedActs(F) <-> AllowedActs(F)=action";
by (cut_inst_tac [("F", "F")] AllowedActs_type 1);
by (auto_tac (claset(), 
      simpset() addsimps [actionSet_def]));
qed "AllowedActs_action_eq";

(** Eliminating `Int state' from expressions  **)
Goal
"Init(F) Int state = Init(F)";
by (cut_inst_tac [("F", "F")] Init_type 1);
by (auto_tac (claset(), 
      simpset() addsimps [condition_def]));
qed "Init_Int_state";

Goal 
"state Int Init(F) = Init(F)";
by (stac (Int_commute) 1);
by (simp_tac (simpset() 
      addsimps [Init_Int_state]) 1);
qed "Init_Int_state2";

Goal
"Acts(F) Int action = Acts(F)";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (auto_tac (claset(), 
      simpset() addsimps [actionSet_def]));
qed "Acts_Int_action";

Goal
"action Int Acts(F) = Acts(F)";
by (simp_tac (simpset() addsimps 
         [Int_commute, Acts_Int_action]) 1);
qed "Acts_Int_action2";

Goal
"AllowedActs(F) Int action = AllowedActs(F)";
by (cut_inst_tac [("F", "F")] AllowedActs_type 1);
by (auto_tac (claset(), 
      simpset() addsimps [actionSet_def]));
qed "AllowedActs_Int_action";

Goal
"action Int AllowedActs(F) = AllowedActs(F)";
by (simp_tac (simpset() addsimps 
         [Int_commute, AllowedActs_Int_action]) 1);
qed  "AllowedActs_Int_action2";

Addsimps 
[Init_state_eq, Acts_action_eq, AllowedActs_action_eq,
 Init_Int_state, Init_Int_state2, Acts_Int_action, Acts_Int_action2,
 AllowedActs_Int_action,AllowedActs_Int_action2];

(** mk_program **)

Goal "mk_program(init, acts, allowed):program";
by (auto_tac (claset(), simpset() 
  addsimps [program_def, mk_program_def, condition_def, actionSet_def]));
qed "mk_program_type";
AddIffs [mk_program_type];
AddTCs [mk_program_type];

Goal "RawInit(mk_program(init, acts, allowed)) = init Int state";
by (auto_tac (claset(), simpset() 
       addsimps [RawInit_def, mk_program_def]));
qed "RawInit_eq";

Goal "Init(mk_program(init, acts, allowed)) = init Int state";
by (auto_tac (claset(), simpset() 
        addsimps [Init_def, RawInit_eq]));
qed "Init_eq";
Addsimps [Init_eq];

Goalw [RawActs_def]
"RawActs(mk_program(init, acts, allowed)) \
\  = cons(Id, acts Int Pow(state*state))";
by (auto_tac (claset(), simpset() 
      addsimps [mk_program_def]));
qed "RawActs_eq";

Goalw [Acts_def]
"Acts(mk_program(init, acts, allowed))  \
 \ = cons(Id, acts  Int Pow(state*state))";
by (auto_tac (claset(), 
      simpset() addsimps [RawActs_eq]));
qed "Acts_eq";
Addsimps [Acts_eq];

Goalw [RawAllowedActs_def]
"RawAllowedActs(mk_program(init, acts, allowed)) \
\  = cons(Id, allowed Int action)";
by (auto_tac (claset(), 
       simpset() addsimps [mk_program_def]));
qed "RawAllowedActs_eq";

Goalw [AllowedActs_def]
"AllowedActs(mk_program(init, acts, allowed)) \
\  = cons(Id, allowed Int action)";
by (auto_tac (claset(), 
      simpset() addsimps [RawAllowedActs_eq]));
qed "AllowedActs_eq";
Addsimps [AllowedActs_eq];


(**Init, Acts, and AlowedActs  of SKIP **)

Goal "RawInit(SKIP) = state";
by (auto_tac (claset(), simpset() 
             addsimps [SKIP_def, RawInit_eq]));
qed "RawInit_SKIP";

Goal "Init(SKIP) = state";
by (simp_tac (simpset() 
   addsimps [Init_def, RawInit_SKIP]) 1);
qed "Init_SKIP";
Addsimps [Init_SKIP];

Goal "RawActs(SKIP) = {Id}";
by (auto_tac (claset(), simpset() 
      addsimps [SKIP_def, RawActs_eq]));
qed "RawActs_SKIP";


Goal "Acts(SKIP) = {Id}";
by (simp_tac (simpset() 
    addsimps [Acts_def, RawActs_SKIP]) 1);
qed "Acts_SKIP";
Addsimps [Acts_SKIP];

Goal "RawAllowedActs(SKIP) = action";
by (auto_tac (claset(), simpset() 
    addsimps [SKIP_def, RawAllowedActs_eq]));
qed "RawAllowedActs_SKIP";

Goal "AllowedActs(SKIP) = action";
by (simp_tac (simpset() 
    addsimps [AllowedActs_def, RawAllowedActs_SKIP]) 1);
qed "AllowedActs_SKIP";
Addsimps [AllowedActs_SKIP];

(** Equality for UNITY programs **)

Goal 
"F:program ==> mk_program(RawInit(F), RawActs(F), RawAllowedActs(F))=F";
by (auto_tac (claset(), simpset() addsimps 
                   [program_def, mk_program_def, RawInit_def,
                    RawActs_def, RawAllowedActs_def, actionSet_def, condition_def]));
by (REPEAT(Blast_tac 1));
qed "raw_surjective_mk_program";

Goal
  "mk_program(Init(F), Acts(F), AllowedActs(F)) = programify(F)";
by (auto_tac (claset(), simpset() addsimps 
                        [Init_def, Acts_def, AllowedActs_def,
                         raw_surjective_mk_program]));
qed "surjective_mk_program";


Goal "[|Init(F) = Init(G); Acts(F) = Acts(G); \
\ AllowedActs(F) = AllowedActs(G); F:program; G:program |] ==> F = G";
by (stac (programify_program RS sym) 1);
by (rtac sym 2);
by (stac  (programify_program RS sym) 2);
by (stac (surjective_mk_program RS sym) 3);
by (stac (surjective_mk_program RS sym) 3);
by (ALLGOALS(Asm_simp_tac));
qed "program_equalityI";

val [major,minor] =
Goal "[| F = G; \
\        [| Init(F) = Init(G); Acts(F) = Acts(G); AllowedActs(F) = AllowedActs(G) |]\
\        ==> P |] ==> P";
by (rtac minor 1);
by (auto_tac (claset(), simpset() addsimps [major]));
qed "program_equalityE";


Goal "[| F:program; G:program |] ==>(F=G)  <->  \
\     (Init(F) = Init(G) & Acts(F) = Acts(G) & AllowedActs(F) = AllowedActs(G))";
by (blast_tac (claset() addIs [program_equalityI, program_equalityE]) 1);
qed "program_equality_iff";

Addsimps [surjective_mk_program];

(*** These rules allow "lazy" definition expansion 

...skipping 1 line

***)

Goal "F == mk_program (init,acts,allowed) ==> Init(F) = init Int state";
by Auto_tac;
qed "def_prg_Init";


Goal "F == mk_program (init,acts,allowed) ==> Acts(F) = cons(Id, acts Int action)";
by Auto_tac;
qed "def_prg_Acts";


Goal "F == mk_program (init,acts,allowed) ==> \
\    AllowedActs(F) = cons(Id, allowed Int action)";
by Auto_tac;
qed "def_prg_AllowedActs";


val [rew] = goal thy
    "[| F == mk_program (init,acts,allowed) |] \
\    ==> Init(F) = init Int state & Acts(F) = cons(Id, acts Int action)";
by (rewtac rew);
by Auto_tac;
qed "def_prg_simps";


(*An action is expanded only if a pair of states is being tested against it*)
Goal "[| act == {<s,s'>:A*B. P(s, s')} |] ==> \
\ (<s,s'>:act) <-> (<s,s'>:A*B & P(s, s'))";
by Auto_tac;
qed "def_act_simp";

fun simp_of_act def = def RS def_act_simp;

(*A set is expanded only if an element is being tested against it*)
Goal "A == B ==> (x : A) <-> (x : B)";
by Auto_tac;
qed "def_set_simp";

fun simp_of_set def = def RS def_set_simp;

(*** co ***)

val prems = Goalw [constrains_def]
    "[|(!!act s s'. [| act: Acts(F);  <s,s'>:act; s:A|] ==> s':A'); \
    \   F:program; A:condition; A':condition |]  ==> F:A co A'";
by (blast_tac(claset() addIs prems) 1);
qed "constrainsI";

Goalw [constrains_def]
   "F:A co B ==> ALL act:Acts(F). act``A<=B";
by (Blast_tac 1);
qed "constrainsD";

Goalw [constrains_def]
  "F:A co B ==> F:program & A:condition & B:condition";
by (Blast_tac 1);
qed "constrainsD2";

Goalw [constrains_def] 
     "[| F:program; B:condition |] ==> F : 0 co B";
by (Blast_tac 1);
qed "constrains_empty";

Goalw [constrains_def]
    "[| F:program; A:condition |] ==>(F : A co 0) <-> (A=0)";
by (auto_tac (claset() addSDs [bspec], 
              simpset() addsimps [condition_def]));
qed "constrains_empty2";

Goalw [constrains_def]
"[| F:program; B:condition |] ==> (F: state co B) <-> (B = state)";
by (auto_tac (claset() addSDs [bspec] addDs [ActsD], 
              simpset() addsimps [condition_def]));
qed "constrains_state";


Goalw [constrains_def] 
          "[| F:program; A:condition |] ==> F : A co state";
by (auto_tac (claset() addDs [ActsD], simpset()));
qed "constrains_state2";

Addsimps [constrains_empty, constrains_empty2, 
         constrains_state, constrains_state2];

(*monotonic in 2nd argument*)
Goalw [constrains_def]
    "[| F:A co A'; A'<=B'; B':condition |] ==> F : A co B'";
by (Blast_tac 1);
qed "constrains_weaken_R";

(*anti-monotonic in 1st argument*)
Goalw [constrains_def, condition_def]
    "[| F : A co A'; B<=A |] ==> F : B co A'";
by (Blast_tac 1);
qed "constrains_weaken_L";

Goal
   "[| F : A co A'; B<=A; A'<=B'; B':condition |] ==> F : B co B'";
by (dtac constrains_weaken_R 1);
by (dtac constrains_weaken_L 3);
by (REPEAT(Blast_tac 1));
qed "constrains_weaken";

(** Union **)

Goalw [constrains_def]
    "[| F : A co A'; F:B co B' |] ==> F:(A Un B) co (A' Un B')";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "constrains_Un";

Goalw [constrains_def]
    "[| F : A co A'; F:B co B' |] ==> F:(A Un B) co (A' Un B')";
by Auto_tac;
by (asm_full_simp_tac 
        (simpset() addsimps [condition_def]) 1);
by (Blast_tac 1);
qed "constrains_Un";

Goalw [constrains_def]
    "[| ALL i:I. F:A(i) co A'(i); F:program |] ==> \
\  F:(UN i:I. A(i)) co (UN i:I. A'(i))";
by (Clarify_tac 1);
by (Blast_tac 1);
bind_thm ("constrains_UN", ballI RS result());


Goalw [constrains_def]
     "(A Un B) co C = (A co C) Int (B co C)";
by (rtac equalityI 1);
by (ALLGOALS(Asm_full_simp_tac));
by (ALLGOALS(Blast_tac));
qed "constrains_Un_distrib";


Goalw [constrains_def]
   "i:I ==> (UN i:I. A(i)) co B = (INT i:I. A(i) co B)";
by (rtac equalityI 1);
by Safe_tac;
by (ALLGOALS(Asm_full_simp_tac));
by (ALLGOALS(Blast_tac));
qed "constrains_UN_distrib";

Goalw [constrains_def]
 "[| A:condition; B:condition |] \ 
\  ==> C co (A Int B) = (C co A) Int (C co B)";
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(Blast_tac));
qed "constrains_Int_distrib";

Goalw [constrains_def] "[| i:I; ALL i:I. B(i):condition |] ==> \
\  A co (INT i:I. B(i)) = (INT i:I. A co B(i))";
by (rtac equalityI 1);
by Safe_tac;
by (ALLGOALS(Blast_tac));
qed "constrains_INT_distrib";

(** Intersection **)

Goalw [constrains_def]
    "[| F : A co A'; F : B co B' |] ==> F : (A Int B) co (A' Int B')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "constrains_Int";

Goalw [constrains_def]
    "[| ALL i:I. F : A(i) co A'(i); F:program |] \
\     ==> F : (INT i:I. A(i)) co (INT i:I. A'(i))";
by (case_tac "I=0" 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_def]) 1);
by (etac not_emptyE 1);
by Safe_tac; 
by (dres_inst_tac [("x", "xd")]  bspec 1);
by (ALLGOALS(Blast_tac));
bind_thm ("constrains_INT", ballI RS result());


(* This rule simulates the HOL's one for (INT z. A i) co (INT z. B i)  *)

Goalw [constrains_def, condition_def]
 "[| ALL z. F: {s:state. P(s, z)} co {s:state. Q(s, z)}; F:program |] ==> \
\  F: {s:state. ALL z. P(s, z)} co {s:state. ALL z. Q(s, z)}";
by (auto_tac (claset() addSDs [bspec] addDs [ActsD], 
              simpset() addsimps [condition_def]));
by (Blast_tac 1);
bind_thm ("constrains_All", allI RS result());

Goalw [constrains_def] 
      "F : A co A' ==> A <= A'";
by (auto_tac (claset() addSDs [bspec], simpset()));
qed "constrains_imp_subset";

(*The reasoning is by subsets since "co" refers to single actions
  only.  So this rule isn't that useful.*)

Goalw [constrains_def]
    "[| F : A co B; F : B co C |] ==> F : A co C";
by Auto_tac;
by (dres_inst_tac [("x", "act")] bspec 1);
by (dres_inst_tac [("x", "Id")] bspec 2);
by (auto_tac (claset() addDs [ActsD], 
              simpset() addsimps [condition_def]));
qed "constrains_trans";

Goalw [constrains_def]
   "[| F : A co (A' Un B); F : B co B' |] ==> F : A co (A' Un B')";
by Auto_tac;
by (dres_inst_tac [("x", "Id")] bspec 1);
by (dres_inst_tac [("x", "act")] bspec 2);
by (auto_tac (claset(), simpset() addsimps [condition_def]));
qed "constrains_cancel";

(*** unless ***)

Goalw [unless_def] "F : (A-B) co (A Un B) ==> F : A unless B";
by (assume_tac 1);
qed "unlessI";

Goalw [unless_def] "F :A unless B ==> F : (A-B) co (A Un B)";
by (assume_tac 1);
qed "unlessD";

Goalw [unless_def, constrains_def] 
     "F: A unless B ==> F:program & A:condition & B:condition";
by Auto_tac;
qed "unlessD2";

(*** initially ***)

Goalw [initially_def]
"[| Init(F)<=A; F:program; A:condition |] ==> F:initially(A)";
by (Blast_tac 1);
qed "initiallyI";

Goalw [initially_def]
"F:initially(A) ==> Init(F)<=A";
by (Blast_tac 1);
qed "initiallyD";

Goalw [initially_def]
"F:initially(A) ==> F:program & A:condition";
by (Blast_tac 1);
qed "initiallyD2";

(*** stable ***)

Goalw [stable_def] 
    "F : A co A ==> F : stable(A)";
by (assume_tac 1);
qed "stableI";

Goalw [stable_def] "F : stable(A) ==> F : A co A";
by (assume_tac 1);
qed "stableD";

Goalw [stable_def, constrains_def]
   "F:stable(A)==> F:program & A:condition";
by (Blast_tac 1);
qed "stableD2";

Goalw [stable_def, constrains_def] 
      "stable(state) = program";
by (auto_tac (claset() addDs [ActsD], simpset()));
qed "stable_state";
Addsimps [stable_state];

(** Union **)

Goalw [stable_def]
    "[| F : stable(A); F : stable(A') |] ==> F : stable(A Un A')";
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "stable_Un";

val [major, minor] = Goalw [stable_def]
    "[| (!!i. i:I ==> F : stable(A(i))); F:program |] ==> F:stable (UN i:I. A(i))";
by (cut_facts_tac [minor] 1);
by (blast_tac (claset() addIs [constrains_UN, major]) 1);
qed "stable_UN";

Goalw [stable_def]
    "[| F : stable(A);  F : stable(A') |] ==> F : stable (A Int A')";
by (blast_tac (claset() addIs [constrains_Int]) 1);
qed "stable_Int";

val [major, minor] = Goalw [stable_def]
    "[| (!!i. i:I ==> F : stable(A(i))); F:program |] \
\  ==> F : stable (INT i:I. A(i))";
by (cut_facts_tac [minor] 1);
by (blast_tac (claset() addIs [constrains_INT, major]) 1);
qed "stable_INT";

Goalw [stable_def]
 "[| ALL z. F: stable({s:state. P(s, z)}); F:program |] ==> \
\ F: stable({s:state. ALL z. P(s, z)})";
by (rtac constrains_All 1);
by Auto_tac;
bind_thm("stable_All", allI RS result());


Goalw [stable_def, constrains_def]
    "[| F : stable(C); F : A co (C Un A') |] ==> F : (C Un A) co (C Un A')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "stable_constrains_Un";


Goalw [stable_def, constrains_def]
  "[| F : stable(C); F :  (C Int A) co A' |] ==> F : (C Int A) co (C Int A')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "stable_constrains_Int";

(*[| F : stable(C); F :  (C Int A) co A |] ==> F : stable (C Int A) *)
bind_thm ("stable_constrains_stable", stable_constrains_Int RS stableI);

(** invariant **)

Goalw [invariant_def, initially_def]
"invariant(A) = initially(A) Int stable(A)";
by (blast_tac (claset() addDs [stableD2]) 1);
qed "invariant_eq";

val invariant_def2 = invariant_eq RS eq_reflection;

Goalw [invariant_def]
 "[| Init(F)<=A;  F:stable(A) |] ==> F : invariant(A)";
by (blast_tac (claset() addDs [stableD2]) 1);
qed "invariantI";

Goalw [invariant_def]
"F:invariant(A) ==> Init(F)<=A & F:stable(A)";
by Auto_tac;
qed "invariantD";

Goalw [invariant_def] 
  "F:invariant(A) ==> F:program & A:condition";
by (blast_tac (claset() addDs [stableD2]) 1);
qed "invariantD2";

(*Could also say "invariant A Int invariant B <= invariant (A Int B)"*)
Goalw [invariant_def]
  "[| F : invariant(A);  F : invariant(B) |] ==> F : invariant(A Int B)";
by (asm_full_simp_tac (simpset() addsimps [stable_Int]) 1);
by (Blast_tac 1);
qed "invariant_Int";

(** The Elimination Theorem.  The "free" m has become universally quantified!
    Should the premise be !!m instead of ALL m ?  Would make it harder to use
    in forward proof. **)

Goalw [constrains_def]
    "[| ALL m:M. F : {s:S. x(s) = m} co B(m); F:program  |] \
\    ==> F:{s:S. x(s):M} co (UN m:M. B(m))";
by Safe_tac;
by (Blast_tac 1);
by (auto_tac (claset(), simpset() addsimps [condition_def]));
qed "elimination";

(* As above, but for the special case of S=state *)
Goal "[| ALL m:M. F : {s:state. x(s) = m} co B(m); F:program  |] \
\    ==> F:{s:state. x(s):M} co (UN m:M. B(m))";
by (rtac elimination  1);
by (ALLGOALS(Clarify_tac));
qed "eliminiation2";


Goalw [constrains_def, strongest_rhs_def]
    "[| F:program; A:condition |] ==>F : A co (strongest_rhs(F,A))";
by (auto_tac (claset() addDs [ActsD], simpset()));
qed "constrains_strongest_rhs";

Goalw [constrains_def, strongest_rhs_def]
    "F : A co B ==> strongest_rhs(F,A) <=B";
by Safe_tac;
by (dtac InterD 1);
by (auto_tac (claset(), 
              simpset() addsimps [condition_def]));
qed "strongest_rhs_is_strongest";

(*** increasing ***)
Goalw [increasing_on_def]
   "[| F:increasing[A](f, r); z:A |] ==> F:stable({s:state. <z, f`s>:r})";
by (Blast_tac 1);
qed "increasing_onD";

Goalw [increasing_on_def]
"F:increasing[A](f, r) ==> F:program & f:state->A & part_order(A,r)";
by (auto_tac (claset(), simpset() addsimps [INT_iff]));
qed "increasing_onD2";

Goalw [increasing_on_def, stable_def] 
"[| part_order(A,r); c:A; F:program |] ==> F : increasing[A](lam s:state. c, r)";
by (auto_tac (claset(), simpset() addsimps [INT_iff]));
by (force_tac (claset() addSDs [bspec, ActsD], 
              simpset() addsimps [constrains_def, condition_def]) 1);
qed "increasing_on_constant";
Addsimps [increasing_on_constant];

Goalw [increasing_on_def, stable_def, constrains_def, part_order_def]
     "!!f. g:mono_map(A,r,A,r) \
\  ==> increasing[A](f, r) <= increasing[A](g O f, r)";
by (asm_full_simp_tac (simpset() addsimps [INT_iff,condition_def, mono_map_def]) 1);
by (auto_tac (claset() addIs [comp_fun], simpset() addsimps [mono_map_def]));
by (force_tac (claset() addSDs [bspec, ActsD],  simpset()) 1);
by (subgoal_tac "xc:state" 1);
by (force_tac (claset() addSDs [ActsD], simpset()) 2);
by (subgoal_tac "f`xd:A & f`xc:A" 1);
by (blast_tac (claset() addDs [apply_type]) 2);
by (rotate_tac 3 1);
by (dres_inst_tac [("x", "f`xd")] bspec 1);
by (Asm_simp_tac 1);
by (REPEAT(etac conjE 1));
by (rotate_tac ~2 1);
by (dres_inst_tac [("x", "act")] bspec 1);
by (Asm_simp_tac 1);
by (dres_inst_tac [("c", "xc")] subsetD 1);
by (rtac imageI 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [refl_def]) 1);
by (dres_inst_tac [("x", "f`xd")] bspec 1);
by (dres_inst_tac [("x", "f`xc")] bspec 2);
by (ALLGOALS(Asm_simp_tac));
by (dres_inst_tac [("b", "g`(f`xd)")] trans_onD 1);
by Auto_tac;
qed "mono_increasing_on_comp";

(*Holds by the theorem (succ(m) le n) = (m < n) *)
Goalw [increasing_on_def, nat_order_def]
     "[| F:increasing[nat](f, nat_order); z:nat |] \
\  ==> F: stable({s:state. z < f`s})";
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 1);
by Safe_tac;
by (dres_inst_tac [("x", "succ(z)")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [apply_type, Collect_conj_eq]));
by (subgoal_tac "{x: state . f ` x : nat} = state" 1);
by Auto_tac;
qed "strict_increasing_onD";