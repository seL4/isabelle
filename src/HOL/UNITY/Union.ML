(*  Title:      HOL/UNITY/Union.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs
*)


Goal "Init (F Join G) = Init F Int Init G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Init_SKIP";

Goal "Init (F Join G) = Init F Int Init G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Init_Join";

Goal "Acts (F Join G) = Acts F Un Acts G";
by (auto_tac (claset(), simpset() addsimps [Join_def]));
qed "Acts_Join";

Goal "Init (JN i:I. F i) = (INT i:I. Init (F i))";
by (simp_tac (simpset() addsimps [JOIN_def]) 1);
qed "Init_JN";

Goal "Acts (JN i:I. F i) = insert Id (UN i:I. Acts (F i))";
by (auto_tac (claset(), simpset() addsimps [JOIN_def]));
qed "Acts_JN";

Addsimps [Init_Join, Init_JN];

Goal "(JN x:insert a A. B x) = (B a) Join (JN x:A. B x)";
by (rtac program_equalityI 1);
by (ALLGOALS (simp_tac (simpset() addsimps [JOIN_def, Join_def])));
qed "JN_insert";
Addsimps[JN_insert];


(** Algebraic laws **)

Goal "F Join G = G Join F";
by (simp_tac (simpset() addsimps [Join_def, Un_commute, Int_commute]) 1);
qed "Join_commute";

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

Goal "(JN G:{}. G) = SKIP";
by (simp_tac (simpset() addsimps [JOIN_def, SKIP_def]) 1);
qed "JN_empty";
Addsimps [JN_empty];




(*** Safety: constrains, stable, FP ***)

Goalw [constrains_def, JOIN_def]
    "I ~= {} ==> \
\    constrains (Acts (JN i:I. F i)) A B = \
\    (ALL i:I. constrains (Acts (F i)) A B)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "constrains_JN";

Goal "constrains (Acts (F Join G)) A B =  \
\     (constrains (Acts F) A B & constrains (Acts G) A B)";
by (auto_tac
    (claset(),
     simpset() addsimps [constrains_def, Join_def]));
qed "constrains_Join";

(**FAILS, I think; see 5.4.1, Substitution Axiom.
   The problem is to relate reachable (F Join G) with 
   reachable F and reachable G

Goalw [Constrains_def]
    "Constrains (JN i:I. F i) A B = (ALL i:I. Constrains (F i) A B)";
by (simp_tac (simpset() addsimps [constrains_JN]) 1);
by (Blast_tac 1);
qed "Constrains_JN";

Goal "Constrains (F Join G) A B = (Constrains F A B & Constrains G A B)";
by (auto_tac
    (claset(),
     simpset() addsimps [Constrains_def, constrains_Join]));
qed "Constrains_Join";
**)

Goal "[| constrains (Acts F) A A';  constrains (Acts G) B B' |] \
\     ==> constrains (Acts (F Join G)) (A Int B) (A' Un B')";
by (simp_tac (simpset() addsimps [constrains_Join]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "constrains_Join_weaken";

Goal "I ~= {} ==> \
\     stable (Acts (JN i:I. F i)) A = (ALL i:I. stable (Acts (F i)) A)";
by (asm_simp_tac (simpset() addsimps [stable_def, constrains_JN]) 1);
qed "stable_JN";

Goal "stable (Acts (F Join G)) A = \
\     (stable (Acts F) A & stable (Acts G) A)";
by (simp_tac (simpset() addsimps [stable_def, constrains_Join]) 1);
qed "stable_Join";

Goal "I ~= {} ==> FP (Acts (JN i:I. F i)) = (INT i:I. FP (Acts (F i)))";
by (asm_simp_tac (simpset() addsimps [FP_def, stable_JN, INTER_def]) 1);
qed "FP_JN";


(*** Progress: transient, ensures ***)

Goal "I ~= {} ==> \
\   transient (Acts (JN i:I. F i)) A = (EX i:I. transient (Acts (F i)) A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, JOIN_def]));
qed "transient_JN";

Goal "transient (Acts (F Join G)) A = \
\     (transient (Acts F) A | transient (Acts G) A)";
by (auto_tac (claset(),
	      simpset() addsimps [bex_Un, transient_def,
				  Join_def]));
qed "transient_Join";

Goal "I ~= {} ==> \
\     ensures (Acts (JN i:I. F i)) A B = \
\     ((ALL i:I. constrains (Acts (F i)) (A-B) (A Un B)) & \
\      (EX i:I. ensures (Acts (F i)) A B))";
by (auto_tac (claset(),
	      simpset() addsimps [ensures_def, constrains_JN, transient_JN]));
qed "ensures_JN";

Goalw [ensures_def]
     "ensures (Acts (F Join G)) A B =     \
\     (constrains (Acts F) (A-B) (A Un B) & \
\      constrains (Acts G) (A-B) (A Un B) & \
\      (ensures (Acts F) A B | ensures (Acts G) A B))";
by (auto_tac (claset(),
	      simpset() addsimps [constrains_Join, transient_Join]));
qed "ensures_Join";

Goalw [stable_def, constrains_def, Join_def]
    "[| stable (Acts F) A;  constrains (Acts G) A A';  Id: Acts G |] \
\    ==> constrains (Acts (F Join G)) A A'";
by (asm_simp_tac (simpset() addsimps [ball_Un]) 1);
by (Blast_tac 1);
qed "stable_constrains_Join";

(*Premises cannot use Invariant because  Stable F A  is weaker than
  stable (Acts G) A *)
Goal "[| stable (Acts F) A;  Init G <= A;  stable (Acts G) A |] \
\      ==> Invariant (F Join G) A";
by (simp_tac (simpset() addsimps [Invariant_def, Stable_eq_stable,
				  stable_Join]) 1);
by (force_tac(claset() addIs [stable_reachable, stable_Int],
	      simpset() addsimps [Acts_Join]) 1);
qed "stable_Join_Invariant";

Goal "[| stable (Acts F) A;  ensures (Acts G) A B |]     \
\     ==> ensures (Acts (F Join G)) A B";
by (asm_simp_tac (simpset() addsimps [ensures_Join]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "ensures_stable_Join1";

(*As above, but exchanging the roles of F and G*)
Goal "[| ensures (Acts F) A B;  stable (Acts G) A |]     \
\     ==> ensures (Acts (F Join G)) A B";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [ensures_stable_Join1]) 1);
qed "ensures_stable_Join2";

