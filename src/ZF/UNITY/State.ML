(*  Title:      HOL/UNITY/State.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Formalizes UNITY-program states.
*)

AddIffs [some_in_state];


Goal "!!A. state<=A ==> EX x. x:A";
by (res_inst_tac [("x", "some")] exI 1);
by Auto_tac;
qed "state_subset_not_empty";

(** condition **)
Goalw [condition_def]
   "A:condition ==>A<=state";
by (Blast_tac 1);
qed "conditionD";

Goalw [condition_def]
   "A<=state ==> A:condition";
by (Blast_tac 1);
qed "conditionI";

(** actionSet **)
Goalw [actionSet_def]
"acts:actionSet ==> acts<=action";
by (Blast_tac 1);
qed "actionSetD";

Goalw [actionSet_def]
"acts<=action ==>acts:actionSet";
by (Blast_tac 1);
qed "actionSetI";

(** Identity **)
Goalw [condition_def, Identity_def]
"A:condition ==> Id``A = A";
by (Blast_tac 1);
qed "Id_image";

Goalw [Identity_def] 
"A<=state ==> Id``A = A";
by (Blast_tac 1);
qed "Id_image2";

Addsimps [Id_image, Id_image2];

Goalw [Identity_def]
  "Id:action";
by (Blast_tac 1);
qed "Id_in_action";
AddIffs [Id_in_action];
AddTCs [Id_in_action];

Goalw [Identity_def]
 "(x:Id) <-> (EX c:state. x=<c,c>)";
by (Blast_tac 1);
qed "Id_member_simp";
Addsimps [Id_member_simp];

Goalw [Identity_def]
"Id``0 = 0";
by (Blast_tac 1);
qed "Id_0";
Addsimps [Id_0];


Goalw [Identity_def]
"Id``state = state";
by (Blast_tac 1);
qed "Id_image_state";
Addsimps [Id_image_state];

Goalw [condition_def]
"0:condition";
by (Blast_tac 1);
qed "condition_0";

Goalw [condition_def]
"state:condition";
by (Blast_tac 1);
qed "condition_state";

Goalw [actionSet_def] 
"0:actionSet";
by Auto_tac;
qed "actionSet_0";

Goalw [actionSet_def]
"action:actionSet";
by Auto_tac;
qed "actionSet_Prod";

AddIffs [condition_0, condition_state, actionSet_0, actionSet_Prod];
AddTCs [condition_0, condition_state, actionSet_0, actionSet_Prod];

(** Simplification rules for condition **)


(** Union and Un **)

Goalw [condition_def]
 "A Un B:condition <-> A:condition & B:condition";
by (Blast_tac 1);
qed "condition_Un";

Goalw [condition_def]
 "Union(S):condition <-> (ALL A:S. A:condition)";
by (Blast_tac 1);
qed "condition_Union";

AddIffs [condition_Un, condition_Union];
AddIs    [condition_Un RS iffD2, condition_Union RS iffD2];

(** Intersection **)

Goalw [condition_def]
   "[| A:condition; B:condition |] ==> A Int B: condition";
by (Blast_tac 1);
qed "condition_IntI";

Goalw [condition_def, Inter_def]
   "(ALL A:S. A:condition) ==> Inter(S): condition";
by (Blast_tac 1);
bind_thm("condition_InterI", ballI RS result());

AddIs [condition_IntI, condition_InterI];
Addsimps  [condition_IntI, condition_InterI];

Goalw [condition_def]
"A:condition ==> A - B :condition";
by (Blast_tac 1);
qed "condition_DiffI";
AddIs [condition_DiffI];
Addsimps [condition_DiffI];


(** Needed in WFair.thy **)
Goalw [condition_def]
"S:Pow(condition) ==> Union(S):condition";
by (Blast_tac 1);
qed "Union_in_conditionI";

(** Simplification rules **)

Goalw [condition_def]
    "{s:state. P(s)}:condition";
by Auto_tac;
qed "Collect_in_condition";

Goal "{s:state. P(s)}:Pow(state)";
by Auto_tac;
qed "Collect_condition2";

Goal "{s:state. P(s)}<=state";
by Auto_tac;
qed "Collect_condition3";

Goal "{s:state. P(s)} Int state = {s:state. P(s)}";
by Auto_tac;
qed "Collect_Int_state";

Goal "state Int {s:state. P(s)} = {s:state. P(s)}";
by Auto_tac;
qed "Collect_Int_state2";

val state_simps = [Collect_in_condition, Collect_condition2, 
Collect_condition3, Collect_Int_state, Collect_Int_state2];


(* actionSet *)

Goalw [actionSet_def]
 "(A Un B):actionSet <-> (A:actionSet&B:actionSet)";
by Auto_tac;
qed "actionSet_Un";

Goalw [actionSet_def]
 "(UN i:I. A(i)):actionSet <-> (ALL i:I. A(i):actionSet)";
by Auto_tac;
qed "actionSet_UN";

AddIffs [actionSet_Un, actionSet_UN];
AddIs [actionSet_Un RS iffD2, actionSet_UN RS iffD2];

Goalw [actionSet_def]
"[| A:actionSet; B:actionSet |] ==> (A Int B):actionSet";
by Auto_tac;
qed "actionSet_Int";

Goalw [actionSet_def]
"(ALL i:I. A(i):actionSet) ==> (INT i:I. A(i)):actionSet";
by (auto_tac (claset(), simpset() addsimps [Inter_def]));
qed "actionSet_INT";

Addsimps [actionSet_INT];
AddIs [actionSet_INT];
Addsimps [Inter_0];

Goalw [condition_def]
 "(PROD x:variable. type_of(x)):condition";
by Auto_tac;
qed "PROD_condition";

Addsimps [PROD_condition];
AddIs [PROD_condition];
