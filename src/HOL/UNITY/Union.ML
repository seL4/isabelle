(*  Title:      HOL/UNITY/Union.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs

NOT CLEAR WHETHER ALL THESE FORMS ARE NEEDED: 
    Maybe Join instead of Un, and JOIN for UNION
*)


Goal "Init (Join prgF prgG) = Init prgF Int Init prgG";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Init_Join";

Goal "Acts (Join prgF prgG) = Acts prgF Un Acts prgG";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Acts_Join";

Goal "Init (JN i:I. prg i) = (INT i:I. Init (prg i))";
by (simp_tac (simpset() addsimps [JOIN_def]) 1);
qed "Init_JN";

Goal "Acts (JN i:I. prg i) = (UN i:I. Acts (prg i))";
by (simp_tac (simpset() addsimps [JOIN_def]) 1);
qed "Acts_JN";

Addsimps [Init_Join, Init_JN];

(** Theoretical issues **)

Goal "Join prgF prgG = Join prgG prgF";
by (simp_tac (simpset() addsimps [Join_def, Un_commute, Int_commute]) 1);
qed "Join_commute";

Goal "Join (Join prgF prgG) prgH = Join prgF (Join prgG prgH)";
by (simp_tac (simpset() addsimps [Join_def, Un_assoc, Int_assoc]) 1);
qed "Join_assoc";


(*
val field_defs = thms"program.field_defs";
val dest_defs = thms"program.dest_defs";
val dest_convs = thms"program.dest_convs";

val update_defs = thms"program.update_defs";
val make_defs = thms"program.make_defs";
val update_convs = thms"program.update_convs";
val simps = thms"program.simps";
*)


(**NOT PROVABLE because no "surjective pairing" for records
Goalw [Join_def, Null_def] "id: Acts prgF ==> Join prgF Null = prgF";
by (asm_simp_tac (simpset() addsimps [insert_absorb]) 1);
qed "Join_Null";
*)

(**NOT PROVABLE because no "surjective pairing" for records
Goalw [Join_def] "Join prgF prgF = prgF";
by Auto_tac;
qed "Join_absorb";
*)



(*** Safety: constrains, stable, FP ***)

Goalw [constrains_def, JOIN_def]
    "constrains (Acts (JN i:I. prg i)) A B = \
\    (ALL i:I. constrains (Acts (prg i)) A B)";
by Auto_tac;
qed "constrains_JN";

(**FAILS, I think; see 5.4.1, Substitution Axiom.
Goalw [Constrains_def]
    "Constrains (JN i:I. prg i) A B = (ALL i:I. Constrains (prg i) A B)";
by (simp_tac (simpset() addsimps [constrains_JN]) 1);
by (Blast_tac 1);
qed "Constrains_JN";
**)

Goalw [constrains_def, Join_def]
    "constrains (Acts (Join prgF prgG)) A B =  \
\    (constrains (Acts prgF) A B & constrains (Acts prgG) A B)";
by (simp_tac (simpset() addsimps [ball_Un]) 1);
qed "constrains_Join";

Goal "[| constrains (Acts prgF) A A';  constrains (Acts prgG) B B' |] \
\     ==> constrains (Acts (Join prgF prgG)) (A Int B) (A' Un B')";
by (simp_tac (simpset() addsimps [constrains_Join]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "constrains_Join_weaken";

Goalw [stable_def] 
    "stable (Acts (JN i:I. prg i)) A = (ALL i:I. stable (Acts (prg i)) A)";
by (simp_tac (simpset() addsimps [constrains_JN]) 1);
qed "stable_JN";

Goal "stable (Acts (Join prgF prgG)) A = \
\     (stable (Acts prgF) A & stable (Acts prgG) A)";
by (simp_tac (simpset() addsimps [stable_def, constrains_Join]) 1);
qed "stable_Join";

Goalw [FP_def] "FP (Acts (JN i:I. prg i)) = (INT i:I. FP (Acts (prg i)))";
by (simp_tac (simpset() addsimps [stable_JN, INTER_def]) 1);
qed "FP_JN";


(*** Progress: transient, ensures ***)

Goalw [transient_def, JOIN_def]
   "transient (Acts (JN i:I. prg i)) A = (EX i:I. transient (Acts (prg i)) A)";
by (Simp_tac 1);
qed "transient_JN";

Goalw [transient_def, Join_def]
   "transient (Acts (Join prgF prgG)) A = \
\   (transient (Acts prgF) A | transient (Acts prgG) A)";
by (simp_tac (simpset() addsimps [bex_Un]) 1);
qed "transient_Join";

Goalw [ensures_def]
    "ensures (Acts (JN i:I. prg i)) A B = \
\    ((ALL i:I. constrains (Acts (prg i)) (A-B) (A Un B)) & \
\     (EX i:I. ensures (Acts (prg i)) A B))";
by (auto_tac (claset(),
	      simpset() addsimps [constrains_JN, transient_JN]));
qed "ensures_JN";

Goalw [ensures_def]
     "ensures (Acts (Join prgF prgG)) A B =     \
\     (constrains (Acts prgF) (A-B) (A Un B) & \
\      constrains (Acts prgG) (A-B) (A Un B) & \
\      (ensures (Acts prgF) A B | ensures (Acts prgG) A B))";
by (auto_tac (claset(),
	      simpset() addsimps [constrains_Join, transient_Join]));
qed "ensures_Join";

Goalw [stable_def, constrains_def, Join_def]
    "[| stable (Acts prgF) A;  constrains (Acts prgG) A A';  id: Acts prgG |] \
\    ==> constrains (Acts (Join prgF prgG)) A A'";
by (asm_simp_tac (simpset() addsimps [ball_Un]) 1);
by (Blast_tac 1);
qed "stable_constrains_Join";

(*Premises cannot use Invariant because  Stable prgF A  is weaker than
  stable (Acts prgG) A *)
Goal  "[| stable (Acts prgF) A;  Init prgG <= A;  stable (Acts prgG) A |] \
\      ==> Invariant (Join prgF prgG) A";
by (simp_tac (simpset() addsimps [Invariant_def, Stable_eq_stable,
				  stable_Join]) 1);
by (force_tac(claset() addIs [stable_reachable, stable_Int],
	      simpset() addsimps [Acts_Join]) 1);
qed "stable_Join_Invariant";

Goal "[| stable (Acts prgF) A;  ensures (Acts prgG) A B |]     \
\     ==> ensures (Acts (Join prgF prgG)) A B";
by (asm_simp_tac (simpset() addsimps [ensures_Join]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "ensures_stable_Join1";

(*As above, but exchanging the roles of F and G*)
Goal "[| ensures (Acts prgF) A B;  stable (Acts prgG) A |]     \
\     ==> ensures (Acts (Join prgF prgG)) A B";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [ensures_stable_Join1]) 1);
qed "ensures_stable_Join2";

