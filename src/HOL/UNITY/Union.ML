(*  Title:      HOL/UNITY/Union.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs

NOT CLEAR WHETHER ALL THESE FORMS ARE NEEDED: 
    Maybe Join instead of Un, and JOIN for UNION
*)

(*** Safety: constrains, stable, FP ***)

Goalw [constrains_def]
    "constrains (UN i:I. acts i) A B = (ALL i:I. constrains (acts i) A B)";
by (Blast_tac 1);
qed "constrains_UN";

Goalw [constrains_def]
    "constrains (actsF Un actsG) A B =  \
\    (constrains actsF A B & constrains actsG A B)";
by (simp_tac (simpset() addsimps [ball_Un]) 1);
qed "constrains_Un";

(*Provable by constrains_Un and constrains_weaken, but why bother?*)
Goalw [constrains_def]
     "[| constrains actsF A A';  constrains actsG B B' |] \
\     ==> constrains (actsF Un actsG) (A Int B) (A' Un B')";
by (Blast_tac 1);
qed "constrains_Un_weaken";

Goalw [stable_def] "stable (UN i:I. acts i) A = (ALL i:I. stable (acts i) A)";
by (simp_tac (simpset() addsimps [constrains_UN]) 1);
qed "stable_UN";

Goalw [stable_def]
    "stable (actsF Un actsG) A = (stable actsF A & stable actsG A)";
by (simp_tac (simpset() addsimps [constrains_Un]) 1);
qed "stable_Un";

Goal "stable (Acts (Join prgF prgG)) A = \
\     (stable (Acts prgF) A & stable (Acts prgG) A)";
by (simp_tac (simpset() addsimps [Join_def, stable_Un]) 1);
qed "stable_Join";

Goalw [FP_def] "FP (UN i:I. acts i) = (INT i:I. FP (acts i))";
by (simp_tac (simpset() addsimps [stable_UN, INTER_def]) 1);
qed "FP_UN";


(*** Progress: transient, ensures ***)

Goalw [transient_def]
    "transient (UN i:I. acts i) A = (EX i:I. transient (acts i) A)";
by (Simp_tac 1);
qed "transient_UN";

Goalw [ensures_def,transient_def]
    "ensures (UN i:I. acts i) A B = \
\    ((ALL i:I. constrains (acts i) (A-B) (A Un B)) & \
\     (EX i:I. ensures (acts i) A B))";
by (simp_tac (simpset() addsimps [constrains_UN]) 1);
by Auto_tac;
qed "ensures_UN";

(*Alternative proof: simplify using ensures_def,transient_def,constrains_Un*)
Goal "ensures (actsF Un actsG) A B =     \
\     (constrains actsF (A-B) (A Un B) & \
\      constrains actsG (A-B) (A Un B) & \
\      (ensures actsF A B | ensures actsG A B))";
by (simp_tac (simpset() addcongs [conj_cong]
			addsimps [ensures_UN, Un_eq_UN,
				  all_bool_eq, ex_bool_eq]) 1);
qed "ensures_Un";

(*Or a longer proof via constrains_imp_subset*)
Goalw [stable_def, constrains_def]
     "[| stable actsF A;  constrains actsG A A';  id: actsG |] \
\     ==> constrains (actsF Un actsG) A A'";
by (asm_simp_tac (simpset() addsimps [ball_Un]) 1);
by (Blast_tac 1);
qed "stable_constrains_Un";

Goalw [Join_def]
      "[| stable (Acts prgF) A;  invariant prgG A |]     \
\      ==> invariant (Join prgF prgG) A";
by (asm_full_simp_tac (simpset() addsimps [invariant_def, stable_Un]) 1);
by (Blast_tac 1);
qed "stable_Join_invariant";

Goal "[| stable actsF A;  ensures actsG A B |]     \
\     ==> ensures (actsF Un actsG) A B";
by (asm_simp_tac (simpset() addsimps [ensures_Un]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "ensures_stable_Un1";

Goal "[| stable (Acts prgF) A;  ensures (Acts prgG) A B |]     \
\     ==> ensures (Acts (Join prgF prgG)) A B";
by (asm_simp_tac (simpset() addsimps [Join_def, ensures_stable_Un1]) 1);
qed "ensures_stable_Join1";

(*As above, but exchanging the roles of F and G*)
Goal "[| ensures actsF A B;  stable actsG A |]     \
\     ==> ensures (actsF Un actsG) A B";
by (stac Un_commute 1);
by (blast_tac (claset() addIs [ensures_stable_Un1]) 1);
qed "ensures_stable_Un2";

Goal "[| ensures (Acts prgF) A B;  stable (Acts prgG) A |]     \
\     ==> ensures (Acts (Join prgF prgG)) A B";
by (asm_simp_tac (simpset() addsimps [Join_def, ensures_stable_Un2]) 1);
qed "ensures_stable_Join2";


(** Theoretical issues **)

Goalw [Join_def] "Join prgF prgG = Join prgG prgF";
by (simp_tac (simpset() addsimps [Un_commute, Int_commute]) 1);
qed "Join_commute";

Goalw [Join_def] "Join (Join prgF prgG) prgH = Join prgF (Join prgG prgH)";
by (simp_tac (simpset() addsimps [Un_assoc, Int_assoc]) 1);
qed "Join_assoc";

(**NOT PROVABLE because no "surjective pairing" for records
Goalw [Join_def, Null_def] "id: Acts prgF ==> Join prgF Null = prgF";
by (asm_simp_tac (simpset() addsimps [insert_absorb]) 1);
qed "Join_Null";
*)

(**NOT PROVABLE because no "surjective pairing" for records
Goalw [Join_def] "Join prgF prgF = prgF";
auto();
qed "Join_absorb";
*)


(*
val field_defs = thms"program.field_defs";
val dest_defs = thms"program.dest_defs";
val dest_convs = thms"program.dest_convs";

val update_defs = thms"program.update_defs";
val make_defs = thms"program.make_defs";
val update_convs = thms"program.update_convs";
val simps = thms"program.simps";
*)
