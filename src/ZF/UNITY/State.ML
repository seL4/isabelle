(*  Title:      HOL/UNITY/State.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Formalizes UNITY-program states.
*)
AddIffs [some_assume];

AddIs var.intrs;
Addsimps var.intrs;

Goalw [st_set_def] "st_set({x:state. P(x)})";
by Auto_tac;
qed "st_set_Collect";
AddIffs [st_set_Collect];

Goalw [st_set_def] "st_set(0)";
by (Simp_tac 1);
qed "st_set_0";
AddIffs [st_set_0];

Goalw [st_set_def] "st_set(state)";
by (Simp_tac 1);
qed "st_set_state";
AddIffs [st_set_state];

(* Union *)

Goalw [st_set_def] 
"st_set(A Un B) <-> st_set(A) & st_set(B)";
by Auto_tac;
qed "st_set_Un_iff";
AddIffs [st_set_Un_iff];

Goalw [st_set_def] 
"st_set(Union(S)) <-> (ALL A:S. st_set(A))";
by Auto_tac;
qed "st_set_Union_iff";
AddIffs [st_set_Union_iff];

(* Intersection *)

Goalw [st_set_def] 
"st_set(A) | st_set(B) ==> st_set(A Int B)";
by Auto_tac;
qed "st_set_Int";
AddSIs [st_set_Int];

Goalw [st_set_def, Inter_def]
   "(S=0) | (EX A:S. st_set(A)) ==> st_set(Inter(S))";
by Auto_tac;
qed "st_set_Inter";
AddSIs [st_set_Inter];

(* Diff *)
Goalw [st_set_def]
"st_set(A) ==> st_set(A - B)";
by Auto_tac;
qed "st_set_DiffI";
AddSIs [st_set_DiffI];

Goal "{s:state. P(s)} Int state = {s:state. P(s)}";
by Auto_tac;
qed "Collect_Int_state";

Goal "state Int {s:state. P(s)} = {s:state. P(s)}";
by Auto_tac;
qed "state_Int_Collect";
AddIffs [Collect_Int_state, state_Int_Collect];

(* Introduction and destruction rules for st_set *)

Goalw [st_set_def]
 "A <= state ==> st_set(A)";
by (assume_tac 1);
qed "st_setI";

Goalw [st_set_def]
 "st_set(A) ==> A<=state";
by (assume_tac 1);
qed "st_setD";

Goalw [st_set_def]
"[| st_set(A); B<=A |] ==> st_set(B)";
by Auto_tac;
qed "st_set_subset";



