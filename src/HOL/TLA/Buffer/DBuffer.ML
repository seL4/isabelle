(* 
    File:        DBuffer.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Double FIFO buffer implements simple FIFO buffer.
*)


val db_css = (claset(), simpset() addsimps [qc_def]);
Addsimps [qc_def];

val db_defs = [BInit_def, Enq_def, Deq_def, Next_def, IBuffer_def, Buffer_def,
               DBInit_def,DBEnq_def,DBDeq_def,DBPass_def,DBNext_def,DBuffer_def];


(*** Proper initialization ***)
Goal "|- Init DBInit --> Init (BInit inp qc out)";
by (auto_tac (db_css addsimps2 [Init_def,DBInit_def,BInit_def]));
qed "DBInit";


(*** Step simulation ***)
Goal "|- [DBNext]_(inp,mid,out,q1,q2) --> [Next inp qc out]_(inp,qc,out)";
by (rtac square_simulation 1);
by (Clarsimp_tac 1);
by (action_simp_tac (simpset() addsimps hd_append::db_defs) [] [] 1);
qed "DB_step_simulation";


(*** Simulation of fairness ***)

(* Compute enabledness predicates for DBDeq and DBPass actions *)
Goalw [angle_def,DBDeq_def,Deq_def] "|- <DBDeq>_(inp,mid,out,q1,q2) = DBDeq";
by (REPEAT (Safe_tac THEN Asm_lr_simp_tac 1));
qed "DBDeq_visible";

Goalw [action_rewrite DBDeq_visible]
  "|- Enabled (<DBDeq>_(inp,mid,out,q1,q2)) = (q2 ~= #[])";
by (force_tac (db_css addSIs2 [DB_base RS base_enabled] addSEs2 [enabledE] 
                     addsimps2 [angle_def,DBDeq_def,Deq_def]) 1);
qed "DBDeq_enabled";

Goal "|- <DBPass>_(inp,mid,out,q1,q2) = DBPass";
by (auto_tac (db_css addsimps2 [angle_def,DBPass_def,Deq_def]));
qed "DBPass_visible";

Goalw [action_rewrite DBPass_visible]
   "|- Enabled (<DBPass>_(inp,mid,out,q1,q2)) = (q1 ~= #[])";
by (force_tac (db_css addSIs2 [DB_base RS base_enabled] addSEs2 [enabledE] 
                     addsimps2 [angle_def,DBPass_def,Deq_def]) 1);
qed "DBPass_enabled";


(* The plan for proving weak fairness at the higher level is to prove
   (0)  DBuffer => (Enabled (Deq inp qc out) ~> (Deq inp qc out))
   which is in turn reduced to the two leadsto conditions
   (1)  DBuffer => (Enabled (Deq inp qc out) ~> q2 ~= [])
   (2)  DBuffer => (q2 ~= [] ~> DBDeq)
   and the fact that DBDeq implies <Deq inp qc out>_(inp,qc,out)
   (and therefore DBDeq ~> <Deq inp qc out>_(inp,qc,out) trivially holds).

   Condition (1) is reduced to
   (1a) DBuffer => (qc ~= [] /\ q2 = [] ~> q2 ~= [])
   by standard leadsto rules (leadsto_classical) and rule Deq_enabledE.

   Both (1a) and (2) are proved from DBuffer's WF conditions by standard
   WF reasoning (Lamport's WF1 and WF_leadsto).
   The condition WF(Deq inp qc out) follows from (0) by rule leadsto_WF.

   One could use Lamport's WF2 instead.
*)

(* Condition (1a) *)
Goal "|- [][DBNext]_(inp,mid,out,q1,q2) & WF(DBPass)_(inp,mid,out,q1,q2) \
\        --> (qc ~= #[] & q2 = #[] ~> q2 ~= #[])";
by (rtac WF1 1);
by (force_tac (db_css addsimps2 db_defs) 1);
by (force_tac (db_css addsimps2 [angle_def,DBPass_def]) 1);
by (force_tac (db_css addsimps2 [DBPass_enabled]) 1);
qed "DBFair_1a";

(* Condition (1) *)
Goal "|- [][DBNext]_(inp,mid,out,q1,q2) & WF(DBPass)_(inp,mid,out,q1,q2) \
\        --> (Enabled (<Deq inp qc out>_(inp,qc,out)) ~> q2 ~= #[])";
by (Clarsimp_tac 1);
by (rtac (temp_use leadsto_classical) 1);
by (rtac ((temp_use DBFair_1a) RS (temp_use LatticeTransitivity)) 1);
by (TRYALL atac);
by (rtac (temp_use ImplLeadsto_gen) 1);
by (force_tac (db_css addSIs2 [necT] addSDs2 [STL2_gen, Deq_enabledE]
                      addsimps2 Init_defs) 1);
qed "DBFair_1";

(* Condition (2) *)
Goal "|- [][DBNext]_(inp,mid,out,q1,q2) & WF(DBDeq)_(inp,mid,out,q1,q2) \
\        --> (q2 ~= #[] ~> DBDeq)";
by (rtac WF_leadsto 1);
by (force_tac (db_css addsimps2 [DBDeq_enabled]) 1);
by (force_tac (db_css addsimps2 [angle_def]) 1);
by (force_tac (db_css addsimps2 db_defs addSEs2 [Stable]) 1);
qed "DBFair_2";

(* High-level fairness *)
Goal "|- [][DBNext]_(inp,mid,out,q1,q2) & WF(DBPass)_(inp,mid,out,q1,q2) \
\                                       & WF(DBDeq)_(inp,mid,out,q1,q2)  \ 
\        --> WF(Deq inp qc out)_(inp,qc,out)";
by (auto_tac (temp_css addSIs2 [leadsto_WF,
                                (temp_use DBFair_1) RSN(2,(temp_use LatticeTransitivity)),
                                (temp_use DBFair_2) RSN(2,(temp_use LatticeTransitivity))]));
by (auto_tac (db_css addSIs2 [ImplLeadsto_simple]
                     addsimps2 [angle_def,DBDeq_def,Deq_def,hd_append]));
qed "DBFair";

(*** Main theorem ***)
Goalw [DBuffer_def,Buffer_def,IBuffer_def] "|- DBuffer --> Buffer inp out";
by (force_tac (temp_css addSIs2 [eexI,DBInit,DB_step_simulation RS STL4,DBFair]) 1);
qed "DBuffer_impl_Buffer";
