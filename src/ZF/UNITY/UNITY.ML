(*  Title:      ZF/UNITY/UNITY.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)
From Misra, "A Logic for Concurrent Programming", 1994

Proofs ported from HOL
*)

(** SKIP **)
Goalw [SKIP_def]  "SKIP:program";
by (rewrite_goal_tac [program_def, mk_program_def] 1);
by Auto_tac;
qed "SKIP_in_program";
AddIffs [SKIP_in_program];
AddTCs  [SKIP_in_program];

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
AddIffs [programify_idem];

Goal
"Init(programify(F)) = Init(F)";
by (simp_tac (simpset() addsimps [Init_def]) 1);
qed "Init_programify";
AddIffs [Init_programify];

Goal
"Acts(programify(F)) = Acts(F)";
by (simp_tac (simpset() addsimps [Acts_def]) 1);
qed "Acts_programify";
AddIffs [Acts_programify];

Goal
"AllowedActs(programify(F)) = AllowedActs(F)";
by (simp_tac (simpset() addsimps [AllowedActs_def]) 1);
qed "AllowedActs_programify";
AddIffs [AllowedActs_programify];

(** program's inspectors **)

Goal  "F:program ==>id(state):RawActs(F)";
by (auto_tac (claset(), simpset() 
        addsimps [program_def, RawActs_def]));
qed "id_in_RawActs";

Goal "id(state):Acts(F)";
by (simp_tac (simpset() 
      addsimps [id_in_RawActs, Acts_def]) 1);
qed "id_in_Acts";

Goal  "F:program ==>id(state):RawAllowedActs(F)";
by (auto_tac (claset(), simpset() 
         addsimps [program_def, RawAllowedActs_def]));
qed "id_in_RawAllowedActs";

Goal   "id(state):AllowedActs(F)";
by (simp_tac (simpset() 
     addsimps [id_in_RawAllowedActs, AllowedActs_def]) 1);
qed "id_in_AllowedActs";

AddIffs [id_in_Acts, id_in_AllowedActs];
AddTCs [id_in_Acts, id_in_AllowedActs];

Goal "cons(id(state), Acts(F)) = Acts(F)";
by (simp_tac (simpset() addsimps [cons_absorb]) 1);
qed "cons_id_Acts";

Goal "cons(id(state), AllowedActs(F)) = AllowedActs(F)";
by (simp_tac (simpset() addsimps [cons_absorb]) 1);
qed "cons_id_AllowedActs";

AddIffs [cons_id_Acts, cons_id_AllowedActs];

(** inspectors's types **)
Goal
"F:program ==> RawInit(F)<=state";
by (auto_tac (claset(), simpset() 
        addsimps [program_def, RawInit_def]));
qed "RawInit_type";

Goal
"F:program ==> RawActs(F)<=Pow(state*state)";
by (auto_tac (claset(), simpset() 
       addsimps [program_def, RawActs_def]));
qed "RawActs_type";

Goal
"F:program ==> RawAllowedActs(F)<=Pow(state*state)";
by (auto_tac (claset(), simpset() 
         addsimps [program_def, RawAllowedActs_def]));
qed "RawAllowedActs_type";

Goal "Init(F)<=state";
by (simp_tac (simpset() 
    addsimps [RawInit_type, Init_def]) 1);
qed "Init_type";

Goalw [st_set_def] "st_set(Init(F))";
by (rtac Init_type 1);
qed "st_set_Init";
AddIffs [st_set_Init];

Goal
"Acts(F)<=Pow(state*state)";
by (simp_tac (simpset() 
    addsimps [RawActs_type, Acts_def]) 1);
qed "Acts_type";

Goal
"AllowedActs(F)<=Pow(state*state)";
by (simp_tac (simpset() 
     addsimps [RawAllowedActs_type, AllowedActs_def]) 1);
qed "AllowedActs_type";

(** More simplification rules involving state 
    and Init, Acts, and AllowedActs **)

Goal "state <= Init(F) <-> Init(F)=state";
by (cut_inst_tac [("F", "F")] Init_type 1);
by Auto_tac;
qed "state_subset_is_Init_iff";
AddIffs [state_subset_is_Init_iff];

Goal "Pow(state*state) <= Acts(F) <-> Acts(F)=Pow(state*state)";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by Auto_tac;
qed "Pow_state_times_state_is_subset_Acts_iff";
AddIffs [Pow_state_times_state_is_subset_Acts_iff];

Goal "Pow(state*state) <= AllowedActs(F) <-> AllowedActs(F)=Pow(state*state)";
by (cut_inst_tac [("F", "F")] AllowedActs_type 1);
by Auto_tac;
qed "Pow_state_times_state_is_subset_AllowedActs_iff";
AddIffs [Pow_state_times_state_is_subset_AllowedActs_iff];

(** Eliminating `Int state' from expressions  **)
Goal "Init(F) Int state = Init(F)";
by (cut_inst_tac [("F", "F")] Init_type 1);
by (Blast_tac 1);
qed "Init_Int_state";
AddIffs [Init_Int_state];

Goal "state Int Init(F) = Init(F)";
by (cut_inst_tac [("F", "F")] Init_type 1);
by (Blast_tac 1);
qed "state_Int_Init";
AddIffs [state_Int_Init];

Goal "Acts(F) Int Pow(state*state) = Acts(F)";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (Blast_tac 1);
qed "Acts_Int_Pow_state_times_state";
AddIffs [Acts_Int_Pow_state_times_state];

Goal "Pow(state*state) Int Acts(F) = Acts(F)";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (Blast_tac 1);
qed "state_times_state_Int_Acts";
AddIffs [state_times_state_Int_Acts];

Goal "AllowedActs(F) Int Pow(state*state) = AllowedActs(F)";
by (cut_inst_tac [("F", "F")] AllowedActs_type 1);
by (Blast_tac 1);
qed "AllowedActs_Int_Pow_state_times_state";
AddIffs [AllowedActs_Int_Pow_state_times_state];

Goal "Pow(state*state) Int AllowedActs(F) = AllowedActs(F)";
by (cut_inst_tac [("F", "F")] AllowedActs_type 1);
by (Blast_tac 1);
qed "state_times_state_Int_AllowedActs";
AddIffs [state_times_state_Int_AllowedActs];

(** mk_program **)

Goalw [mk_program_def, program_def] "mk_program(init, acts, allowed):program";
by Auto_tac;
qed "mk_program_in_program";
AddIffs [mk_program_in_program];
AddTCs [mk_program_in_program];

Goalw [RawInit_def, mk_program_def]
  "RawInit(mk_program(init, acts, allowed)) = init Int state";
by Auto_tac;
qed "RawInit_eq";
AddIffs [RawInit_eq];

Goalw [RawActs_def, mk_program_def] 
"RawActs(mk_program(init, acts, allowed)) = cons(id(state), acts Int Pow(state*state))";
by Auto_tac;
qed "RawActs_eq";
AddIffs [RawActs_eq];

Goalw [RawAllowedActs_def, mk_program_def]
"RawAllowedActs(mk_program(init, acts, allowed)) = \
\ cons(id(state), allowed Int Pow(state*state))";
by Auto_tac;
qed "RawAllowedActs_eq";
AddIffs [RawAllowedActs_eq];

Goalw [Init_def]  "Init(mk_program(init, acts, allowed)) = init Int state";
by (Simp_tac 1);
qed "Init_eq";
AddIffs [Init_eq];

Goalw [Acts_def] 
"Acts(mk_program(init, acts, allowed)) = cons(id(state), acts  Int Pow(state*state))";
by (Simp_tac 1);
qed "Acts_eq";
AddIffs [Acts_eq];

Goalw [AllowedActs_def]
"AllowedActs(mk_program(init, acts, allowed))= \
\ cons(id(state), allowed Int Pow(state*state))";
by (Simp_tac 1);
qed "AllowedActs_eq";
AddIffs [AllowedActs_eq];

(**Init, Acts, and AlowedActs  of SKIP **)

Goalw [SKIP_def] "RawInit(SKIP) = state";
by Auto_tac;
qed "RawInit_SKIP";
AddIffs [RawInit_SKIP];

Goalw [SKIP_def] "RawAllowedActs(SKIP) = Pow(state*state)";
by Auto_tac;
qed "RawAllowedActs_SKIP";
AddIffs [RawAllowedActs_SKIP];

Goalw [SKIP_def] "RawActs(SKIP) = {id(state)}";
by Auto_tac;
qed "RawActs_SKIP";
AddIffs [RawActs_SKIP];

Goalw [Init_def] "Init(SKIP) = state";
by Auto_tac;
qed "Init_SKIP";
AddIffs [Init_SKIP];

Goalw [Acts_def] "Acts(SKIP) = {id(state)}";
by Auto_tac;
qed "Acts_SKIP";
AddIffs [Acts_SKIP];

Goalw [AllowedActs_def] "AllowedActs(SKIP) = Pow(state*state)";
by Auto_tac;
qed "AllowedActs_SKIP";
AddIffs [AllowedActs_SKIP];

(** Equality of UNITY programs **)

Goal 
"F:program ==> mk_program(RawInit(F), RawActs(F), RawAllowedActs(F))=F";
by (rewrite_goal_tac [program_def, mk_program_def,RawInit_def,
                      RawActs_def, RawAllowedActs_def] 1);
by Auto_tac;
by (REPEAT(Blast_tac 1));
qed "raw_surjective_mk_program";
Addsimps [raw_surjective_mk_program];

Goalw [Init_def, Acts_def, AllowedActs_def]
  "mk_program(Init(F), Acts(F), AllowedActs(F)) = programify(F)";
by Auto_tac;
qed "surjective_mk_program";
AddIffs [surjective_mk_program];

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

(*** These rules allow "lazy" definition expansion 

...skipping 1 line

***)

Goal "F == mk_program (init,acts,allowed) ==> Init(F) = init Int state";
by Auto_tac;
qed "def_prg_Init";


Goal "F == mk_program (init,acts,allowed) ==> \
\ Acts(F) = cons(id(state), acts Int Pow(state*state))";
by Auto_tac;
qed "def_prg_Acts";


Goal "F == mk_program (init,acts,allowed) ==> \
\    AllowedActs(F) = cons(id(state), allowed Int Pow(state*state))";
by Auto_tac;
qed "def_prg_AllowedActs";


val [rew] = goal thy
    "[| F == mk_program (init,acts,allowed) |] \
\ ==> Init(F) = init Int state & Acts(F) = cons(id(state), acts Int Pow(state*state)) & \
\     AllowedActs(F) = cons(id(state), allowed Int Pow(state*state)) ";
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

Goalw [constrains_def]
"A co B <= program";
by Auto_tac;
qed "constrains_type";


val prems = Goalw [constrains_def]
    "[|(!!act s s'. [| act: Acts(F);  <s,s'>:act; s:A|] ==> s':A'); \
    \   F:program; st_set(A) |]  ==> F:A co A'";
by (auto_tac (claset() delrules [subsetI], simpset()));
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps prems)));
by (Clarify_tac 1);
by (blast_tac(claset() addIs prems) 1);
qed "constrainsI";

Goalw [constrains_def]
   "F:A co B ==> ALL act:Acts(F). act``A<=B";
by (Blast_tac 1);
qed "constrainsD";

Goalw [constrains_def]
   "F:A co B ==> F:program & st_set(A)";
by (Blast_tac 1);
qed "constrainsD2"; 

Goalw [constrains_def, st_set_def] "F : 0 co B <-> F:program";
by (Blast_tac 1);
qed "constrains_empty";

Goalw [constrains_def, st_set_def]
    "(F : A co 0) <-> (A=0 & F:program)";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by Auto_tac;
by (Blast_tac 1);
qed "constrains_empty2";

Goalw [constrains_def, st_set_def]
"(F: state co B) <-> (state<=B & F:program)";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (Blast_tac 1);
qed "constrains_state";

Goalw [constrains_def, st_set_def] "F:A co state <-> (F:program & st_set(A))";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (Blast_tac 1);
qed "constrains_state2";

AddIffs [constrains_empty, constrains_empty2, 
         constrains_state, constrains_state2];

(*monotonic in 2nd argument*)
Goalw [constrains_def]
    "[| F:A co A'; A'<=B' |] ==> F : A co B'";
by (Blast_tac 1);
qed "constrains_weaken_R";

(*anti-monotonic in 1st argument*)
Goalw [constrains_def, st_set_def]
    "[| F : A co A'; B<=A |] ==> F : B co A'";
by (Blast_tac 1);
qed "constrains_weaken_L";

Goal
   "[| F : A co A'; B<=A; A'<=B' |] ==> F : B co B'";
by (dtac constrains_weaken_R 1);
by (dtac constrains_weaken_L 2);
by (REPEAT(Blast_tac 1));
qed "constrains_weaken";

(** Union **)

Goalw [constrains_def, st_set_def]
    "[| F : A co A'; F:B co B' |] ==> F:(A Un B) co (A' Un B')";
by Auto_tac;
by (Force_tac 1);
qed "constrains_Un";

val major::minor::_ = Goalw [constrains_def, st_set_def]
"[|(!!i. i:I ==> F:A(i) co A'(i)); F:program |]==> F:(UN i:I. A(i)) co (UN i:I. A'(i))";
by (cut_facts_tac [minor] 1);
by Safe_tac;
by (ALLGOALS(ftac major ));
by (ALLGOALS(Asm_full_simp_tac));
by (REPEAT(Blast_tac 1));
qed "constrains_UN";

Goalw [constrains_def, st_set_def]
     "(A Un B) co C = (A co C) Int (B co C)";
by Auto_tac;
by (Force_tac 1);
qed "constrains_Un_distrib";

Goalw [constrains_def, st_set_def]
   "i:I ==> (UN i:I. A(i)) co B = (INT i:I. A(i) co B)";
by (rtac equalityI 1);
by (REPEAT(Force_tac 1));
qed "constrains_UN_distrib";

(** Intersection **)
Goalw [constrains_def, st_set_def]
 "C co (A Int B) = (C co A) Int (C co B)";
by (rtac equalityI 1);
by (ALLGOALS(Clarify_tac)); (* to speed up the proof *)
by (REPEAT(Blast_tac 1));
qed "constrains_Int_distrib";

Goalw [constrains_def, st_set_def] 
"x:I ==> A co (INT i:I. B(i)) = (INT i:I. A co B(i))";
by (rtac equalityI 1);
by Safe_tac;
by (REPEAT(Blast_tac 1));
qed "constrains_INT_distrib";

Goalw [constrains_def, st_set_def]
    "[| F : A co A'; F : B co B' |] ==> F : (A Int B) co (A' Int B')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "constrains_Int";

val major::minor::_ = Goalw [constrains_def, st_set_def]
"[| (!!i. i:I==>F:A(i) co A'(i)); F:program|]==> F:(INT i:I. A(i)) co (INT i:I. A'(i))";
by (cut_facts_tac [minor] 1);
by (cut_inst_tac [("F", "F")] Acts_type 1);
by (case_tac "I=0" 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_def]) 1);
by (etac not_emptyE 1);
by Safe_tac;
by (forw_inst_tac [("i", "xd")] major 1);
by (ftac major 2);
by (ftac major 3);
by (REPEAT(Force_tac 1));
qed "constrains_INT";

(* The rule below simulates the HOL's one for (INT z. A i) co (INT z. B i) *)
Goalw [constrains_def]
"[| ALL z. F:{s:state. P(s, z)} co {s:state. Q(s, z)}; F:program |]==>\
\   F:{s:state. ALL z. P(s, z)} co {s:state. ALL z. Q(s, z)}";
by (Blast_tac 1);
qed "constrains_All";

Goalw [constrains_def, st_set_def] 
  "[| F:A co A' |] ==> A <= A'";
by Auto_tac;
by (Blast_tac 1);
qed "constrains_imp_subset";
(*The reasoning is by subsets since "co" refers to single actions
  only.  So this rule isn't that useful.*)

Goalw [constrains_def, st_set_def]
    "[| F : A co B; F : B co C |] ==> F : A co C";
by Auto_tac;
by (Blast_tac 1);
qed "constrains_trans";

Goal
"[| F : A co (A' Un B); F : B co B' |] ==> F:A co (A' Un B')";
by (dres_inst_tac [("A", "B")] constrains_imp_subset 1);
by (blast_tac (claset() addIs [constrains_weaken_R]) 1);
qed "constrains_cancel";

(*** unless ***)

Goalw [unless_def, constrains_def] 
     "A unless B <= program";
by Auto_tac;
qed "unless_type";

Goalw [unless_def] "[| F:(A-B) co (A Un B) |] ==> F : A unless B";
by (blast_tac (claset() addDs [constrainsD2]) 1);
qed "unlessI";

Goalw [unless_def] "F :A unless B ==> F : (A-B) co (A Un B)";
by Auto_tac;
qed "unlessD";

(*** initially ***)

Goalw [initially_def]
"initially(A) <= program";
by (Blast_tac 1);
qed "initially_type";

Goalw [initially_def]
"[| F:program; Init(F)<=A |] ==> F:initially(A)";
by (Blast_tac 1);
qed "initiallyI";

Goalw [initially_def]
"F:initially(A) ==> Init(F)<=A";
by (Blast_tac 1);
qed "initiallyD";

(*** stable ***)

Goalw [stable_def, constrains_def]
   "stable(A)<=program";
by (Blast_tac 1);
qed "stable_type";

Goalw [stable_def] 
    "F : A co A ==> F : stable(A)";
by (assume_tac 1);
qed "stableI";

Goalw [stable_def] "F:stable(A) ==> F : A co A";
by (assume_tac 1);
qed "stableD";

Goalw [stable_def, constrains_def] "F:stable(A) ==> F:program & st_set(A)";
by Auto_tac;
qed "stableD2";

Goalw [stable_def, constrains_def] "stable(state) = program";
by (auto_tac (claset() addDs [Acts_type RS subsetD], simpset()));
qed "stable_state";
AddIffs [stable_state];

(** Union **)

Goalw [stable_def]
    "[| F : stable(A); F:stable(A') |] ==> F : stable(A Un A')";
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "stable_Un";

val [major, minor] = Goalw [stable_def]
"[|(!!i. i:I ==> F : stable(A(i))); F:program |] ==> F:stable (UN i:I. A(i))";
by (cut_facts_tac [minor] 1);
by (blast_tac (claset() addIs [constrains_UN, major]) 1);
qed "stable_UN";

Goalw [stable_def]
    "[| F : stable(A);  F : stable(A') |] ==> F : stable (A Int A')";
by (blast_tac (claset() addIs [constrains_Int]) 1);
qed "stable_Int";

val [major, minor] = Goalw [stable_def]
"[| (!!i. i:I ==> F:stable(A(i))); F:program |] ==> F : stable (INT i:I. A(i))";
by (cut_facts_tac [minor] 1);
by (blast_tac (claset() addIs [constrains_INT, major]) 1);
qed "stable_INT";

Goalw [stable_def]
"[|ALL z. F:stable({s:state. P(s, z)}); F:program|]==>F:stable({s:state. ALL z. P(s, z)})";
by (rtac constrains_All 1);
by Auto_tac;
qed "stable_All";

Goalw [stable_def, constrains_def, st_set_def]
"[| F : stable(C); F : A co (C Un A') |] ==> F : (C Un A) co (C Un A')";
by (cut_inst_tac [("F", "F")] Acts_type 1);
by Auto_tac;
by (Blast.depth_tac (claset()) 10 1);
qed "stable_constrains_Un";

Goalw [stable_def, constrains_def, st_set_def]
  "[| F : stable(C); F :  (C Int A) co A' |] ==> F : (C Int A) co (C Int A')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "stable_constrains_Int";

(* [| F:stable(C); F :(C Int A) co A |] ==> F:stable(C Int A) *)
bind_thm ("stable_constrains_stable", stable_constrains_Int RS stableI);

(** invariant **)

Goalw [invariant_def] 
  "invariant(A) <= program";
by (blast_tac (claset() addDs [stable_type RS subsetD]) 1);
qed "invariant_type";

Goalw [invariant_def, initially_def]
 "[| Init(F)<=A;  F:stable(A) |] ==> F : invariant(A)";
by (forward_tac [stable_type RS subsetD] 1);
by Auto_tac;
qed "invariantI";

Goalw [invariant_def, initially_def]
"F:invariant(A) ==> Init(F)<=A & F:stable(A)";
by Auto_tac;
qed "invariantD";

Goalw [invariant_def]
 "F:invariant(A) ==> F:program & st_set(A)";
by (blast_tac (claset() addDs [stableD2]) 1);
qed "invariantD2";

(*Could also say "invariant A Int invariant B <= invariant (A Int B)"*)
Goalw [invariant_def, initially_def]
  "[| F : invariant(A);  F : invariant(B) |] ==> F : invariant(A Int B)";
by (asm_full_simp_tac (simpset() addsimps [stable_Int]) 1);
by (Blast_tac 1);
qed "invariant_Int";

(** The Elimination Theorem.  The "free" m has become universally quantified!
 Should the premise be !!m instead of ALL m ? Would make it harder 
 to use in forward proof. **)

(* The general case easier to prove that le special case! *)
Goalw [constrains_def, st_set_def]
    "[| ALL m:M. F : {s:A. x(s) = m} co B(m); F:program  |] \
\    ==> F:{s:A. x(s):M} co (UN m:M. B(m))";
by Safe_tac;
by Auto_tac;
by (Blast_tac 1);
qed "elimination";

(* As above, but for the special case of A=state *)
Goal "[| ALL m:M. F : {s:state. x(s) = m} co B(m); F:program  |] \
\    ==> F:{s:state. x(s):M} co (UN m:M. B(m))";
by (rtac elimination  1);
by (ALLGOALS(Clarify_tac));
qed "eliminiation2";

(** strongest_rhs **)

Goalw [constrains_def, strongest_rhs_def, st_set_def]
    "[| F:program; st_set(A) |] ==> F:A co (strongest_rhs(F,A))";
by (auto_tac (claset() addDs [Acts_type RS subsetD], simpset()));
qed "constrains_strongest_rhs";

Goalw [constrains_def, strongest_rhs_def, st_set_def]
"[| F:A co B; st_set(B) |] ==> strongest_rhs(F,A) <= B";
by Safe_tac;
by (dtac InterD 1);
by Auto_tac;
qed "strongest_rhs_is_strongest";

(*** increasing ***)
Goalw [increasing_def] "increasing(A, r, f) <= program";
by (case_tac "A=0" 1);
by (etac not_emptyE 2);
by (Clarify_tac 2);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [Inter_iff, Inter_0])));
by (blast_tac (claset() addDs [stable_type RS subsetD]) 1); 
qed "increasing_type";

Goalw [increasing_def]
   "[| F:increasing(A, r, f); a:A |] ==> F:stable({s:state. <a, f`s>:r})";
by (Blast_tac 1);
qed "increasingD";

Goalw [increasing_def]
"F:increasing(A, r, f) ==> F:program & (EX a. a:A)";
by (auto_tac (claset() addDs [stable_type RS subsetD],
              simpset() addsimps [INT_iff]));
qed "increasingD2";

Goalw [increasing_def, stable_def]
 "F:increasing(A, r, lam s:state. c) <-> F:program & (EX a. a:A)";
by (auto_tac (claset() addDs [constrains_type RS subsetD],
               simpset() addsimps [INT_iff]));
qed "increasing_constant";
AddIffs [increasing_constant];

Goalw [increasing_def, stable_def, constrains_def, st_set_def, part_order_def]
"[| g:mono_map(A,r,A,r); part_order(A, r); f:state->A |] \
\  ==> increasing(A, r,f) <= increasing(A, r,g O f)";
by (case_tac "A=0" 1);
by (Asm_full_simp_tac 1);
by (etac not_emptyE 1);
by (Clarify_tac 1);
by (cut_inst_tac [("F", "xa")] Acts_type 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_iff, mono_map_def]) 1);
by Auto_tac;
by (rename_tac "xa xc xd act xe xf" 1);
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
qed "mono_increasing_comp";

(*Holds by the theorem (succ(m) le n) = (m < n) *)
Goalw [increasing_def]
     "[| F:increasing(nat, {<m,n>:nat*nat. m le n}, f); f:state->nat; k:nat |] \
\  ==> F: stable({s:state. k < f`s})";
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 1);
by Safe_tac;
by (dres_inst_tac [("x", "succ(k)")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [apply_type, Collect_conj_eq]));
by (subgoal_tac "{x: state . f`x : nat} = state" 1);
by Auto_tac;
qed "strict_increasingD";


(* Used in WFair.thy *)
Goal "A:Pow(Pow(B)) ==> Union(A):Pow(B)";
by Auto_tac;
qed "Union_PowI";
