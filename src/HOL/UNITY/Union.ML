(*  Title:      HOL/UNITY/Union.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs
*)

Addcongs [UN_cong, INT_cong];


(** SKIP **)

Goal "Init SKIP = UNIV";
by (simp_tac (simpset() addsimps [SKIP_def]) 1);
qed "Init_SKIP";

Goal "Acts SKIP = {Id}";
by (simp_tac (simpset() addsimps [SKIP_def]) 1);
qed "Acts_SKIP";

Addsimps [Init_SKIP, Acts_SKIP];

Goal "reachable SKIP = UNIV";
by (force_tac (claset() addEs [reachable.induct]
			addIs reachable.intrs, simpset()) 1);
qed "reachable_SKIP";

Addsimps [reachable_SKIP];

(** SKIP and safety properties **)

Goalw [constrains_def] "(SKIP : A co B) = (A<=B)";
by Auto_tac;
qed "SKIP_in_constrains_iff";
AddIffs [SKIP_in_constrains_iff];

Goalw [Constrains_def] "(SKIP : A Co B) = (A<=B)";
by Auto_tac;
qed "SKIP_in_Constrains_iff";
AddIffs [SKIP_in_Constrains_iff];

Goalw [stable_def] "SKIP : stable A";
by Auto_tac;
qed "SKIP_in_stable";
AddIffs [SKIP_in_stable, SKIP_in_stable RS stable_imp_Stable];


(** Join **)

Goal "Init (F Join G) = Init F Int Init G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Init_Join";

Goal "Acts (F Join G) = Acts F Un Acts G";
by (auto_tac (claset(), simpset() addsimps [Join_def]));
qed "Acts_Join";

Addsimps [Init_Join, Acts_Join];


(** JN **)

Goalw [JOIN_def, SKIP_def] "(JN i:{}. F i) = SKIP";
by Auto_tac;
qed "JN_empty";
Addsimps [JN_empty];

Goal "(JN i:insert a I. F i) = (F a) Join (JN i:I. F i)";
by (rtac program_equalityI 1);
by (ALLGOALS (simp_tac (simpset() addsimps [JOIN_def, Join_def])));
qed "JN_insert";
Addsimps[JN_empty, JN_insert];

Goal "Init (JN i:I. F i) = (INT i:I. Init (F i))";
by (simp_tac (simpset() addsimps [JOIN_def]) 1);
qed "Init_JN";

Goal "Acts (JN i:I. F i) = insert Id (UN i:I. Acts (F i))";
by (auto_tac (claset(), simpset() addsimps [JOIN_def]));
qed "Acts_JN";

Addsimps [Init_JN, Acts_JN];

val prems = Goalw [JOIN_def]
    "[| I=J;  !!i. i:J ==> F i = G i |] ==> \
\    (JN i:I. F i) = (JN i:J. G i)";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "JN_cong";

Addcongs [JN_cong];


(** Algebraic laws **)

Goal "F Join G = G Join F";
by (simp_tac (simpset() addsimps [Join_def, Un_commute, Int_commute]) 1);
qed "Join_commute";

Goal "A Join (B Join C) = B Join (A Join C)";
by (simp_tac (simpset() addsimps Un_ac@Int_ac@[Join_def]) 1);
qed "Join_left_commute";

Goal "(F Join G) Join H = F Join (G Join H)";
by (simp_tac (simpset() addsimps Un_ac@[Join_def, Int_assoc]) 1);
qed "Join_assoc";
 
Goalw [Join_def, SKIP_def] "SKIP Join F = F";
by (rtac program_equalityI 1);
by (ALLGOALS (simp_tac (simpset() addsimps [insert_absorb])));
qed "Join_SKIP_left";

Goalw [Join_def, SKIP_def] "F Join SKIP = F";
by (rtac program_equalityI 1);
by (ALLGOALS (simp_tac (simpset() addsimps [insert_absorb])));
qed "Join_SKIP_right";

Addsimps [Join_SKIP_left, Join_SKIP_right];

Goalw [Join_def] "F Join F = F";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Join_absorb";

Addsimps [Join_absorb];

Goalw [Join_def] "F Join (F Join G) = F Join G";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Join_left_absorb";

(*Join is an AC-operator*)
val Join_ac = [Join_assoc, Join_left_absorb, Join_commute, Join_left_commute];


(*** JN laws ***)

(*Also follows by JN_insert and insert_absorb, but the proof is longer*)
Goal "k:I ==> F k Join (JN i:I. F i) = (JN i:I. F i)";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_absorb";

Goal "(JN i: I Un J. F i) = ((JN i: I. F i) Join (JN i:J. F i))";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_Un";

Goal "(JN i:I. c) = (if I={} then SKIP else c)";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_constant";

Goal "(JN i:I. F i Join G i) = (JN i:I. F i)  Join  (JN i:I. G i)";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_Join_distrib";

Goal "i : I ==> (JN i:I. F i Join G) = ((JN i:I. F i) Join G)";
by (asm_simp_tac (simpset() addsimps [JN_Join_distrib, JN_constant]) 1);
by Auto_tac;
qed "JN_Join_miniscope";

(*Used to prove guarantees_JN_I*)
Goalw  [JOIN_def, Join_def] "i: I ==> F i Join JOIN (I - {i}) F = JOIN I F";
by (rtac program_equalityI 1);
by Auto_tac;
qed "JN_Join_diff";


(*** Safety: co, stable, FP ***)

(*Fails if I={} because it collapses to SKIP : A co B*)
Goalw [constrains_def, JOIN_def]
    "i : I ==> (JN i:I. F i) : A co B = (ALL i:I. F i : A co B)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "JN_constrains";

Goal "(F Join G : A co B) = (F : A co B & G : A co B)";
by (auto_tac
    (claset(),
     simpset() addsimps [constrains_def, Join_def]));
qed "Join_constrains";

Goal "(F Join G : A unless B) = (F : A unless B & G : A unless B)";
by (simp_tac (simpset() addsimps [Join_constrains, unless_def]) 1);
qed "Join_unless";

(*Analogous weak versions FAIL; see Misra [1994] 5.4.1, Substitution Axiom.
  reachable (F Join G) could be much bigger than reachable F, reachable G
*)


Goal "[| F : A co A';  G : B co B' |] \
\     ==> F Join G : (A Int B) co (A' Un B')";
by (simp_tac (simpset() addsimps [Join_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Join_constrains_weaken";

Goal "[| ALL i:I. F i : A i co A' i;  i: I |] \
\     ==> (JN i:I. F i) : (INT i:I. A i) co (UN i:I. A' i)";
by (asm_simp_tac (simpset() addsimps [JN_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "JN_constrains_weaken";

Goal "(JN i:I. F i) : stable A = (ALL i:I. F i : stable A)";
by (asm_simp_tac 
    (simpset() addsimps [stable_def, constrains_def, JOIN_def]) 1);
qed "JN_stable";

Goal "[| ALL i:I. F i : invariant A;  i : I |]  \
\      ==> (JN i:I. F i) : invariant A";
by (asm_full_simp_tac (simpset() addsimps [invariant_def, JN_stable]) 1);
by (Blast_tac 1);
bind_thm ("invariant_JN_I", ballI RS result());

Goal "(F Join G : stable A) = \
\     (F : stable A & G : stable A)";
by (simp_tac (simpset() addsimps [stable_def, Join_constrains]) 1);
qed "Join_stable";

Goal "(F Join G : increasing f) = \
\     (F : increasing f & G : increasing f)";
by (simp_tac (simpset() addsimps [increasing_def, Join_stable]) 1);
by (Blast_tac 1);
qed "Join_increasing";

Goal "[| F : invariant A; G : invariant A |]  \
\     ==> F Join G : invariant A";
by (full_simp_tac (simpset() addsimps [invariant_def, Join_stable]) 1);
by (Blast_tac 1);
qed "invariant_JoinI";

Goal "FP (JN i:I. F i) = (INT i:I. FP (F i))";
by (asm_simp_tac (simpset() addsimps [FP_def, JN_stable, INTER_def]) 1);
qed "FP_JN";


(*** Progress: transient, ensures ***)

Goal "i : I ==> \
\   (JN i:I. F i) : transient A = (EX i:I. F i : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, JOIN_def]));
qed "JN_transient";

Goal "F Join G : transient A = \
\     (F : transient A | G : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [bex_Un, transient_def,
				  Join_def]));
qed "Join_transient";

Goal "F : transient A ==> F Join G : transient A";
by (asm_simp_tac (simpset() addsimps [Join_transient]) 1);
qed "Join_transient_I1";

Goal "G : transient A ==> F Join G : transient A";
by (asm_simp_tac (simpset() addsimps [Join_transient]) 1);
qed "Join_transient_I2";

Goal "i : I ==> \
\     (JN i:I. F i) : A ensures B = \
\     ((ALL i:I. F i : (A-B) co (A Un B)) & \
\      (EX i:I. F i : A ensures B))";
by (auto_tac (claset(),
	      simpset() addsimps [ensures_def, JN_constrains, JN_transient]));
qed "JN_ensures";

Goalw [ensures_def]
     "F Join G : A ensures B =     \
\     (F : (A-B) co (A Un B) & G : (A-B) co (A Un B) & \
\      (F : transient (A-B) | G : transient (A-B)))";
by (auto_tac (claset(),
	      simpset() addsimps [Join_constrains, Join_transient]));
qed "Join_ensures";

Goalw [stable_def, constrains_def, Join_def]
    "[| F : stable A;  G : A co A' |] \
\    ==> F Join G : A co A'";
by (asm_full_simp_tac (simpset() addsimps [ball_Un]) 1);
by (Blast_tac 1);
qed "stable_Join_constrains";

(*Premise for G cannot use Always because  F: Stable A  is weaker than
  G : stable A *)
Goal "[| F : stable A;  G : invariant A |] ==> F Join G : Always A";
by (full_simp_tac (simpset() addsimps [Always_def, invariant_def, 
				       Stable_eq_stable, Join_stable]) 1);
by (force_tac(claset() addIs [stable_Int], simpset()) 1);
qed "stable_Join_Always1";

(*As above, but exchanging the roles of F and G*)
Goal "[| F : invariant A;  G : stable A |] ==> F Join G : Always A";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [stable_Join_Always1]) 1);
qed "stable_Join_Always2";

Goal "[| F : stable A;  G : A ensures B |] ==> F Join G : A ensures B";
by (asm_simp_tac (simpset() addsimps [Join_ensures]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "stable_Join_ensures1";

(*As above, but exchanging the roles of F and G*)
Goal "[| F : A ensures B;  G : stable A |] ==> F Join G : A ensures B";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [stable_Join_ensures1]) 1);
qed "stable_Join_ensures2";


