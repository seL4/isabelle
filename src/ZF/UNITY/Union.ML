(*  Title:      ZF/UNITY/Union.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs

Proofs ported from HOL.

*)

(** SKIP **)

Goal "reachable(SKIP) = state";
by (force_tac (claset() addEs [reachable.induct]
                        addIs reachable.intrs, simpset()) 1);
qed "reachable_SKIP";

Addsimps [reachable_SKIP];

(* Elimination programify from ok and Join *)

Goal "programify(F) ok G <-> F ok G";
by (simp_tac (simpset() addsimps [ok_def]) 1);
qed "ok_programify_left";

Goal "F ok programify(G) <-> F ok G";
by (simp_tac (simpset() addsimps [ok_def]) 1);
qed "ok_programify_right";

Goal "programify(F) Join G = F Join G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Join_programify_left";

Goal "F Join programify(G) = F Join G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Join_programify_right";

Addsimps [ok_programify_left, ok_programify_right, 
          Join_programify_left, Join_programify_right];

(** SKIP and safety properties **)

Goalw [constrains_def] 
"[| A:condition; B:condition |] ==> (SKIP: A co B) <-> (A<=B)";
by Auto_tac;
qed "SKIP_in_constrains_iff";
Addsimps [SKIP_in_constrains_iff];


Goalw [Constrains_def] 
"[| A:condition; B:condition |] ==> (SKIP : A Co B)<-> (A<=B)";
by (Asm_simp_tac 1);
by (auto_tac (claset(), 
    simpset() addsimps [condition_def]));
qed "SKIP_in_Constrains_iff";
Addsimps [SKIP_in_Constrains_iff];

Goal "A:condition ==>SKIP : stable(A)";
by (auto_tac (claset(), 
    simpset() addsimps [stable_def]));
qed "SKIP_in_stable";
Addsimps [SKIP_in_stable, SKIP_in_stable RS stable_imp_Stable];


(** Join and JOIN types **)

Goalw [Join_def]  
  "F Join G : program";
by Auto_tac;
qed "Join_in_program";
AddIffs [Join_in_program];
AddTCs [Join_in_program];

Goalw [JOIN_def]  
"JOIN(I,F):program";
by Auto_tac;
qed "JOIN_in_program";
AddIffs [JOIN_in_program];
AddTCs [JOIN_in_program];

(* Init, Acts, and AllowedActs of Join and JOIN *)
Goal "Init(F Join G) = Init(F) Int Init(G)";
by (simp_tac (simpset() 
         addsimps [Int_assoc, Join_def]) 1);
qed "Init_Join";

Goal "Acts(F Join G) = Acts(F) Un Acts(G)";
by (simp_tac (simpset() 
     addsimps [Int_Un_distrib,cons_absorb,Join_def]) 1);
qed "Acts_Join";

Goal "AllowedActs(F Join G) = \
\ AllowedActs(F) Int AllowedActs(G)";
by (simp_tac (simpset() 
     addsimps [Int_assoc,cons_absorb,Join_def]) 1);
qed "AllowedActs_Join";
Addsimps [Init_Join, Acts_Join, AllowedActs_Join];


(** Join's algebraic laws **)

Goal "F Join G = G Join F";
by (simp_tac (simpset() addsimps 
     [Join_def, Un_commute, Int_commute]) 1);
qed "Join_commute";


Goal "A Join (B Join C) = B Join (A Join C)";
by (asm_simp_tac (simpset() addsimps 
     Un_ac@Int_ac@[Join_def,Int_Un_distrib, cons_absorb]) 1);
qed "Join_left_commute";


Goal "(F Join G) Join H = F Join (G Join H)";
by (asm_simp_tac (simpset() addsimps 
          Un_ac@[Join_def, cons_absorb, Int_assoc, Int_Un_distrib]) 1);
qed "Join_assoc";

Goalw [Join_def, SKIP_def] 
    "SKIP Join F = programify(F)";
by (simp_tac (simpset() addsimps [Int_absorb, cons_absorb,cons_eq]) 1);
qed "Join_SKIP_left";

Goal  "F Join SKIP =  programify(F)";
by (stac Join_commute 1);
by (asm_simp_tac (simpset() addsimps [Join_SKIP_left]) 1);
qed "Join_SKIP_right";


Addsimps [Join_SKIP_left, Join_SKIP_right];


Goal "F Join F = programify(F)";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Join_absorb";

Addsimps [Join_absorb];

Goal "F Join (F Join G) = F Join G";
by (asm_simp_tac (simpset() addsimps [Join_assoc RS sym]) 1);
qed "Join_left_absorb";


(*Join is an AC-operator*)
val Join_ac = [Join_assoc, Join_left_absorb, Join_commute, Join_left_commute];

(** Eliminating programify in JN and OK expressions **)

Goal "OK(I, %x. programify(F(x))) <-> OK(I, F)";
by (simp_tac (simpset() addsimps [OK_def]) 1);
qed "OK_programify";

Goal "JOIN(I, %x. programify(F(x))) = JOIN(I, F)";
by (simp_tac (simpset() addsimps [JOIN_def]) 1);
qed "JN_programify";

Addsimps [OK_programify, JN_programify];

(* JN *)

Goalw [JOIN_def]
"JOIN(0, F) = SKIP";
by Auto_tac;
qed "JN_empty";
Addsimps [JN_empty];
AddSEs [not_emptyE];
Addsimps [Inter_0];

Goal
   "Init(JN i:I. F(i)) = (if I=0 then state else (INT i:I. Init(F(i))))";
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (auto_tac (claset(), simpset() 
         addsimps [JOIN_def,INT_Int_distrib2]));
qed "Init_JN";

Goal
"Acts(JOIN(I,F)) = cons(Id, UN i:I.  Acts(F(i)))";
by (auto_tac (claset(), 
    simpset() addsimps [JOIN_def, UN_Int_distrib]));
qed "Acts_JN";

Goal
"AllowedActs(JN i:I. F(i)) = (if I=0 then action else (INT i:I. AllowedActs(F(i))))";
by (auto_tac (claset(), simpset() 
               addsimps [JOIN_def, INT_cons RS sym, INT_Int_distrib2]));
qed "AllowedActs_JN";

Addsimps [Init_JN, Acts_JN, AllowedActs_JN];


Goal "(JN i:cons(a,I). F(i)) = F(a) Join (JN i:I. F(i))";
by (rtac program_equalityI 1);
by Auto_tac;
qed "JN_cons";
Addsimps[JN_cons];


val prems = Goalw [JOIN_def]
    "[| I=J;  !!i. i:J ==> F(i) = G(i) |] ==> \
\    (JN i:I. F(i)) = (JN i:J. G(i))";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "JN_cong";

Addcongs [JN_cong];


(*** JN laws ***)
Goal "k:I ==>F(k) Join (JN i:I. F(i)) = (JN i:I. F(i))";
by (stac (JN_cons RS sym) 1);
by (auto_tac (claset(), 
           simpset() addsimps [cons_absorb]));
qed "JN_absorb";

Goalw [Inter_def] "[| i:I; j:J |] ==> \
\  (INT i:I Un J. A(i)) = ((INT i:I. A(i)) Int  (INT j:J. A(j)))";
by Auto_tac;
by (Blast_tac 1);
qed "INT_Un";
  
Goal "(JN i: I Un J. F(i)) = ((JN i: I. F(i)) Join (JN i:J. F(i)))";
by (rtac program_equalityI 1);
by (ALLGOALS(Asm_full_simp_tac));
by Safe_tac;
by (ALLGOALS(asm_full_simp_tac (simpset() 
        addsimps [Int_absorb, INT_Int_distrib2, 
                 Int_INT_distrib, UN_cons, INT_cons])));
by (ALLGOALS(Clarify_tac));
by (REPEAT(Blast_tac 1));
qed "JN_Un";

Goal "(JN i:I. c) = (if I=0 then SKIP else programify(c))";
by (rtac program_equalityI 1);
by Auto_tac;
qed "JN_constant";

Goal 
"(JN i:I. F(i) Join G(i)) = (JN i:I. F(i))  Join  (JN i:I. G(i))";
by (rtac program_equalityI 1);
by (ALLGOALS(simp_tac (simpset() addsimps [Int_absorb])));
by Safe_tac;
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps 
              [INT_Int_distrib, Int_absorb])));
by (Force_tac 1);
qed "JN_Join_distrib";

Goal 
"(JN i:I. F(i) Join G) = ((JN i:I. F(i) Join G))";
by (asm_simp_tac (simpset() 
    addsimps [JN_Join_distrib, JN_constant]) 1);
qed "JN_Join_miniscope";

(*Used to prove guarantees_JN_I*)

Goal "i:I==>F(i) Join JOIN(I - {i}, F) = JOIN(I, F)";
by (rtac program_equalityI 1);
by Auto_tac;
qed "JN_Join_diff";

(*** Safety: co, stable, FP ***)


(*Fails if I=0 because it collapses to SKIP : A co B, i.e. to A<=B.  So an
  alternative precondition is A<=B, but most proofs using this rule require
  I to be nonempty for other reasons anyway.*)

Goalw [constrains_def, JOIN_def]
 "i:I==>(JN i:I. F(i)):A co B <-> (ALL i:I. programify(F(i)):A co B)";
by Auto_tac;
by (blast_tac (claset() addDs [ActsD]) 1);
qed "JN_constrains";

Goal "(F Join G : A co B) <-> \
\  (programify(F):A co B & programify(G):A co B)";
by (auto_tac
    (claset(), simpset() addsimps [constrains_def]));
qed "Join_constrains";

Goal "(F Join G : A unless B) <-> \
\   (programify(F) : A unless B & programify(G):A unless B)";
by (asm_simp_tac (simpset() addsimps [Join_constrains, unless_def]) 1);
qed "Join_unless";

Addsimps [Join_constrains, Join_unless];

(*Analogous weak versions FAIL; see Misra [1994] 5.4.1, Substitution Axiom.
  reachable (F Join G) could be much bigger than reachable F, reachable G
*)

Goal "[| F : A co A';  G:B co B' |] \
\     ==> F Join G : (A Int B) co (A' Un B')";
by (subgoal_tac "A:condition&A':condition & B: condition&  \
                \ B': condition & F:program & G:program" 1);
by (blast_tac (claset()  addDs [constrainsD2]) 2);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Join_constrains_weaken";

(*If I=0, it degenerates to SKIP : UNIV co 0, which is false.*)
Goal "[| ALL i:I. F(i) : A(i) co A'(i);  i: I |] \
\     ==> (JN i:I. F(i)) : (INT i:I. A(i)) co (UN i:I. A'(i))";
by (asm_simp_tac (simpset() addsimps [JN_constrains]) 1);
by (Clarify_tac 1);
by (subgoal_tac "(ALL i:I. F(i):program & A(i):condition)&\
                \ (Union(RepFun(I, A')):condition)&\
                \ (Inter(RepFun(I, A)):condition)" 1);
by (blast_tac (claset() addDs [constrainsD2]) 2);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "JN_constrains_weaken";


Goal "A:condition ==> (JN i:I. F(i)) : stable(A) <-> \
\ (ALL i:I. programify(F(i)):stable(A))";
by (asm_simp_tac 
    (simpset() addsimps [stable_def, constrains_def, JOIN_def]) 1);
by Auto_tac;
by (blast_tac (claset() addDs [ActsD]) 1);
qed "JN_stable";


Goal "[| ALL i:I. F(i) : invariant(A);  i : I |]  \
\      ==> (JN i:I. F(i)) : invariant(A)";
by (subgoal_tac "A:condition" 1);
by (blast_tac (claset() addDs [invariantD2]) 2);
by (asm_full_simp_tac (simpset() addsimps [invariant_def, JN_stable]) 1);
by (Blast_tac 1);
bind_thm ("invariant_JN_I", ballI RS result());
Goal " (F Join G : stable(A)) <->  \
\     (programify(F) : stable(A) & programify(G): stable(A))";
by (asm_simp_tac (simpset() addsimps [stable_def]) 1);
qed "Join_stable";


(* TO BE DONE: stable_increasing *)

Addsimps [Join_stable];

Goal "[| F : invariant(A); G : invariant(A) |]  \
\     ==> F Join G : invariant(A)";
by (subgoal_tac "F:program&G:program" 1);
by (blast_tac (claset() addDs [invariantD2]) 2);
by (full_simp_tac (simpset() addsimps [invariant_def]) 1);
by (auto_tac (claset() addIs [Join_in_program], simpset()));
qed "invariant_JoinI";


(* Fails if I=0 because INT i:0. A(i) = 0 *)
Goal "i:I ==> FP(JN i:I. F(i)) = (INT i:I. FP (programify(F(i))))";
by (asm_simp_tac (simpset() addsimps [FP_def, Inter_def]) 1);
by (rtac equalityI 1);
by Safe_tac;
by (ALLGOALS(subgoal_tac "{x}:condition"));
by (rotate_tac ~1 3);
by (rotate_tac ~1 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [JN_stable])));
by (rewrite_goals_tac [condition_def]);
by (REPEAT(Blast_tac 1));
qed "FP_JN";

(*** Progress: transient, ensures ***)

Goal "i:I==>(JN i:I. F(i)) : transient(A) <-> \
\  (EX i:I. programify(F(i)) : transient(A))";
by (auto_tac (claset(),
              simpset() addsimps [transient_def, JOIN_def]));
by (auto_tac (claset(), simpset() addsimps 
            [condition_def,UN_Int_distrib, INT_Int_distrib]));
qed "JN_transient";

Goal "F Join G : transient(A) <-> \
\     (programify(F) : transient(A) | programify(G):transient(A))";
by (auto_tac (claset(),
              simpset() addsimps [transient_def,
                                  Join_def, Int_Un_distrib]));
qed "Join_transient";

Addsimps [Join_transient];


Goal "F : transient(A) ==> F Join G : transient(A)";
by (asm_full_simp_tac (simpset() 
           addsimps [Join_transient, transientD]) 1);
qed "Join_transient_I1";


Goal "G : transient(A) ==> F Join G : transient(A)";
by (asm_full_simp_tac (simpset() 
           addsimps [Join_transient, transientD]) 1);
qed "Join_transient_I2";

(*If I=0 it degenerates to (SKIP : A ensures B) = False, i.e. to ~(A<=B) *)
Goal "i : I ==> \
\     (JN i:I. F(i)) : A ensures B <-> \
\     ((ALL i:I. programify(F(i)) : (A-B) co (A Un B)) &  \
\     (EX i:I. programify(F(i)) : A ensures B))";
by (auto_tac (claset(),
              simpset() addsimps [ensures_def, JN_constrains, JN_transient]));
qed "JN_ensures";


Goalw [ensures_def]
     "F Join G : A ensures B  <->     \
\     (programify(F) : (A-B) co (A Un B) & programify(G) : (A-B) co (A Un B) & \
\      (programify(F): transient (A-B) | programify(G) : transient (A-B)))";
by (auto_tac (claset(), simpset() addsimps [Join_transient]));
qed "Join_ensures";



Goalw [stable_def, constrains_def, Join_def]
    "[| F : stable(A);  G : A co A' |] \
\    ==> F Join G : A co A'";
by Auto_tac;
by (rewrite_goals_tac [condition_def]);
by Auto_tac;
by (blast_tac (claset() addDs [ActsD]) 3);
by (dres_inst_tac [("x", "Id")] bspec 1);
by (dres_inst_tac [("x", "Id")] bspec 2);
by (dres_inst_tac [("x", "x")] bspec 4);
by (dres_inst_tac [("x", "Id")] bspec 5);
by Auto_tac;
qed "stable_Join_constrains";

(*Premise for G cannot use Always because  F: Stable A  is
   weaker than G : stable A *)
Goal "[| F : stable(A);  G : invariant(A) |] ==> F Join G : Always(A)";
by (subgoal_tac "A:condition & F:program" 1);
by (blast_tac (claset() addDs [stableD2]) 2);
by (asm_full_simp_tac (simpset() addsimps [Always_def, invariant_def, 
                                       Stable_eq_stable]) 1);
by (force_tac(claset() addIs [stable_Int], simpset()) 1);
qed "stable_Join_Always1";



(*As above, but exchanging the roles of F and G*)
Goal "[| F : invariant(A);  G : stable(A) |] ==> F Join G : Always(A)";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [stable_Join_Always1]) 1);
qed "stable_Join_Always2";



Goal "[| F : stable(A);  G : A ensures B |] ==> F Join G : A ensures B";
by (subgoal_tac "F:program&G:program&A:condition&B:condition" 1);
by (blast_tac (claset() addDs [stableD2, ensuresD2]) 2);
by (asm_simp_tac (simpset() addsimps [Join_ensures]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "stable_Join_ensures1";


(*As above, but exchanging the roles of F and G*)
Goal "[| F : A ensures B;  G : stable(A) |] ==> F Join G : A ensures B";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [stable_Join_ensures1]) 1);
qed "stable_Join_ensures2";


(*** the ok and OK relations ***)

Goal "SKIP ok F";
by (auto_tac (claset() addDs [ActsD],
   simpset() addsimps [ok_def]));
qed "ok_SKIP1";  

Goal "F ok SKIP";
by (auto_tac (claset() addDs [ActsD],
      simpset() addsimps [ok_def]));
qed "ok_SKIP2";

AddIffs [ok_SKIP1, ok_SKIP2];  

Goal "(F ok G & (F Join G) ok H) <-> (G ok H & F ok (G Join H))";
by (auto_tac (claset(), simpset() addsimps [ok_def]));
qed "ok_Join_commute";

Goal "(F ok G) <->(G ok F)";
by (auto_tac (claset(), simpset() addsimps [ok_def]));
qed "ok_commute";

bind_thm ("ok_sym", ok_commute RS iffD1);

Goal "OK({<0,F>,<1,G>,<2,H>}, snd) <-> (F ok G & (F Join G) ok H)";
by (asm_full_simp_tac
    (simpset() addsimps [ok_def, Join_def,  OK_def,
                        Int_assoc, cons_absorb, Int_Un_distrib, Ball_def]) 1);
by (rtac iffI 1);
by Safe_tac; 
by (REPEAT(Force_tac 1));
qed "ok_iff_OK";

Goal "F ok (G Join H) <-> (F ok G & F ok H)";
by (auto_tac (claset(), simpset() addsimps [ok_def]));
qed "ok_Join_iff1";


Goal "(G Join H) ok F <-> (G ok F & H ok F)";
by (auto_tac (claset(), simpset() addsimps [ok_def]));
qed "ok_Join_iff2";
AddIffs [ok_Join_iff1, ok_Join_iff2];

(*useful?  Not with the previous two around*)
Goal "[| F ok G; (F Join G) ok H |] ==> F ok (G Join H)";
by (auto_tac (claset(), simpset() addsimps [ok_def]));
qed "ok_Join_commute_I";

Goal "F ok JOIN(I,G) <-> (ALL i:I. F ok G(i))";
by (auto_tac (claset(), simpset() addsimps [ok_def]));
by (blast_tac (claset() addDs [ActsD]) 1);
by (REPEAT(Force_tac 1));
qed "ok_JN_iff1";


Goal "JOIN(I,G) ok F   <->  (ALL i:I. G(i) ok F)";
by (auto_tac (claset(), simpset() addsimps [ok_def]));
by (blast_tac (claset() addDs [ActsD]) 1);
qed "ok_JN_iff2";
AddIffs [ok_JN_iff1, ok_JN_iff2];

Goal "OK(I,F) <-> (ALL i: I. ALL j: I-{i}. F(i) ok (F(j)))"; 
by (auto_tac (claset(), simpset() addsimps [ok_def, OK_def]));  
qed "OK_iff_ok";


Goal "[| OK(I,F); i: I; j: I; i~=j|] ==> F(i) ok F(j)"; 
by (auto_tac (claset(), simpset() addsimps [OK_iff_ok]));  
qed "OK_imp_ok";


(*** Allowed ***)

Goal "Allowed(SKIP) = program";
by (auto_tac (claset() addDs [ActsD], 
               simpset() addsimps [Allowed_def]));  
qed "Allowed_SKIP";

Goal "Allowed(F Join G) = \
\  Allowed(programify(F)) Int Allowed(programify(G))";
by (auto_tac (claset(), simpset() addsimps [Allowed_def]));
qed "Allowed_Join";

Goal "i:I ==> \
\  Allowed(JOIN(I,F)) = (INT i:I. Allowed(programify(F(i))))";
by (auto_tac (claset(), simpset() addsimps [Allowed_def]));
br equalityI 1;
by Auto_tac;
qed "Allowed_JN";

Addsimps [Allowed_SKIP, Allowed_Join, Allowed_JN];

Goal 
"F ok G <-> (programify(F):Allowed(programify(G)) & \
\  programify(G):Allowed(programify(F)))";
by (asm_simp_tac (simpset() addsimps [ok_def, Allowed_def]) 1);
qed "ok_iff_Allowed";


Goal "OK(I,F) <-> \
\ (ALL i: I. ALL j: I-{i}. programify(F(i)) : Allowed(programify(F(j))))"; 
by (auto_tac (claset(), simpset() addsimps [OK_iff_ok, ok_iff_Allowed]));  
qed "OK_iff_Allowed";

(*** safety_prop, for reasoning about given instances of "ok" ***)

Goal "safety_prop(X) ==> (Acts(G) <= cons(Id, (UN F:X. Acts(F)))) <-> (programify(G):X)";
by (full_simp_tac( simpset() addsimps [safety_prop_def]) 1);
by (Clarify_tac 1);
by (case_tac "G:program" 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Blast_tac 1);
by Safe_tac;
by (Force_tac 2);
by (force_tac (claset(), simpset() 
          addsimps [programify_def]) 1);
qed "safety_prop_Acts_iff";

Goal "X:property ==> \
\ (safety_prop(X) --> \
\ ((UN G:X. Acts(G)) <= AllowedActs(F)) <-> (X <= Allowed(programify(F))))";
by (auto_tac (claset(), 
      simpset() addsimps [Allowed_def, 
              safety_prop_Acts_iff RS iff_sym, property_def]));  
qed "safety_prop_AllowedActs_iff_Allowed";


Goal "X:property ==> \
\  safety_prop(X) --> Allowed(mk_program(init, acts, UN F:X. Acts(F))) = X";
by (asm_full_simp_tac (simpset() addsimps [Allowed_def, 
        UN_Int_distrib,safety_prop_Acts_iff, property_def]) 1);
by Auto_tac;
qed "Allowed_eq";

Goal "[| F == mk_program (init, acts, UN F:X. Acts(F)); X:property; safety_prop(X) |] \
\     ==> Allowed(F) = X";
by (asm_simp_tac (simpset() addsimps [Allowed_eq]) 1); 
qed "def_prg_Allowed";

(*For safety_prop to hold, the property must be satisfiable!*)
Goal "B:condition ==> safety_prop(A co B) <-> (A <= B)";
by (simp_tac (simpset() addsimps [safety_prop_def, constrains_def]) 1);
by Auto_tac;
by (Blast_tac 2); 
by (force_tac (claset(), simpset() addsimps [condition_def]) 1);
qed "safety_prop_constrains";
Addsimps [safety_prop_constrains];



Goal "A:condition ==>safety_prop(stable(A))";
by (asm_simp_tac (simpset() addsimps [stable_def]) 1);
qed "safety_prop_stable";
Addsimps [safety_prop_stable];

Goal "[| X:property; Y:property |] ==> \
\  safety_prop(X) --> safety_prop(Y) --> safety_prop(X Int Y)";
by (asm_full_simp_tac (simpset() 
         addsimps [safety_prop_def, property_def]) 1); 
by Safe_tac;
by (dres_inst_tac [("B", "Union(RepFun(X Int Y, Acts))"),
                   ("C", "Union(RepFun(Y, Acts))")] subset_trans 2);
by (dres_inst_tac [("B", "Union(RepFun(X Int Y, Acts))"),
                   ("C", "Union(RepFun(X, Acts))")] subset_trans 1);
by (REPEAT(Blast_tac 1));
qed "safety_prop_Int";
Addsimps [safety_prop_Int];

(* If I=0 the conclusion becomes safety_prop(0) which is false *)
Goal "[| ALL i:I. X(i):property; i:I |] ==> \
\  (ALL i:I. safety_prop(X(i))) --> safety_prop(INT i:I. X(i))";
by (asm_full_simp_tac (simpset() addsimps [safety_prop_def, property_def]) 1); 
by Safe_tac;
by (dres_inst_tac [("B", "Union(RepFun(Inter(RepFun(I, X)), Acts))"),
                   ("C", "Union(RepFun(X(xb), Acts))")] subset_trans 3);
by (REPEAT(Blast_tac 1));
bind_thm ("safety_prop_Inter", ballI RS result());

Goal "[| F == mk_program(init,acts, UN G:X. Acts(G)); safety_prop(X); X:property |] \
\     ==> F ok G <-> (programify(G):X & acts Int action <= AllowedActs(G))";
by (auto_tac (claset(),
       simpset() addsimps [ok_def, safety_prop_Acts_iff, UN_Int_distrib, property_def]));
qed "def_UNION_ok_iff";

