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
goal DBuffer.thy "Init DBInit .-> Init (BInit inp qc out)";
by (auto_tac (db_css addsimps2 [Init_def,DBInit_def,BInit_def]));
qed "DBInit";


(*** Step simulation ***)
goal DBuffer.thy "[DBNext]_<inp,mid,out,q1,q2> .-> [Next inp qc out]_<inp,qc,out>";
by (rtac square_simulation 1);
by (Action_simp_tac 1);
by (action_simp_tac (simpset() addsimps hd_append::db_defs) [] [] 1);
qed "DB_step_simulation";


(*** Simulation of fairness ***)

(* Compute enabledness predicates for DBDeq and DBPass actions *)
goal DBuffer.thy "<DBDeq>_<inp,mid,out,q1,q2> .= DBDeq";
by (auto_tac (db_css addsimps2 [angle_def,DBDeq_def,Deq_def]));
qed "DBDeq_visible";

goal DBuffer.thy "$Enabled (<DBDeq>_<inp,mid,out,q1,q2>) .= ($q2 .~= .[])";
by (rewtac (action_rewrite DBDeq_visible));
by (cut_facts_tac [DB_base] 1);
by (auto_tac (db_css addSEs2 [base_enabled,enabledE] 
                     addsimps2 [angle_def,DBDeq_def,Deq_def]));
qed "DBDeq_enabled";

goal DBuffer.thy "<DBPass>_<inp,mid,out,q1,q2> .= DBPass";
by (auto_tac (db_css addsimps2 [angle_def,DBPass_def,Deq_def]));
qed "DBPass_visible";

goal DBuffer.thy "$Enabled (<DBPass>_<inp,mid,out,q1,q2>) .= ($q1 .~= .[])";
by (rewtac (action_rewrite DBPass_visible));
by (cut_facts_tac [DB_base] 1);
by (auto_tac (db_css addSEs2 [base_enabled,enabledE] 
                     addsimps2 [angle_def,DBPass_def,Deq_def]));
qed "DBPass_enabled";


(* The plan for proving weak fairness at the higher level is to prove
   (0)  DBuffer => (Enabled (Deq inp qc out) ~> (Deq inp qc out))
   which is in turn reduced to the two leadsto conditions
   (1)  DBuffer => (Enabled (Deq inp qc out) ~> q2 ~= [])
   (2)  DBuffer => (q2 ~= [] ~> DBDeq)
   and the fact that DBDeq implies <Deq inp qc out>_<inp,qc,out>
   (and therefore DBDeq ~> <Deq inp qc out>_<inp,qc,out> trivially holds).

   Condition (1) is reduced to
   (1a) DBuffer => (qc ~= [] /\ q2 = [] ~> q2 ~= [])
   by standard leadsto rules (leadsto_classical) and rule Deq_enabledE.

   Both (1a) and (2) are proved from DBuffer's WF conditions by standard
   WF reasoning (Lamport's WF1 and WF_leadsto).
   The condition WF(Deq inp qc out) follows from (0) by rule leadsto_WF.

   One could use Lamport's WF2 instead.
*)

(* Condition (1a) *)
goal DBuffer.thy 
  "[][DBNext]_<inp,mid,out,q1,q2> .& WF(DBPass)_<inp,mid,out,q1,q2> \
\  .-> ($qc .~= .[] .& $q2 .= .[] ~> $q2 .~= .[])";
by (rtac WF1 1);
by (action_simp_tac (simpset() addsimps square_def::db_defs) [] [] 1);
by (action_simp_tac (simpset() addsimps [angle_def,DBPass_def]) [] [] 1);
by (action_simp_tac (simpset() addsimps [DBPass_enabled]) [] [] 1);
qed "DBFair_1a";

(* Condition (1) *)
goal DBuffer.thy
  "[][DBNext]_<inp,mid,out,q1,q2> .& WF(DBPass)_<inp,mid,out,q1,q2> \
\  .-> ($Enabled (<Deq inp qc out>_<inp,qc,out>) ~> $q2 .~= .[])";
by (auto_tac (temp_css addSIs2 [leadsto_classical] addSEs2 [temp_conjimpE DBFair_1a]));
by (auto_tac (temp_css addsimps2 [leadsto,Init_def] addDs2 [STL2bD]
                       addSDs2 [action_mp Deq_enabledE] addSEs2 [STL4E]));
qed "DBFair_1";

(* Condition (2) *)
goal DBuffer.thy
  "[][DBNext]_<inp,mid,out,q1,q2> .& WF(DBDeq)_<inp,mid,out,q1,q2> \
\  .-> ($q2 .~= .[] ~> DBDeq)";
by (rtac WF_leadsto 1);
by (action_simp_tac (simpset() addsimps [DBDeq_visible,DBDeq_enabled]) [] [] 1);
by (action_simp_tac (simpset() addsimps [angle_def]) [] [] 1);
by (action_simp_tac (simpset() addsimps square_def::db_defs) [tempI] [Stable] 1);
qed "DBFair_2";

(* High-level fairness *)
goal DBuffer.thy
  "[][DBNext]_<inp,mid,out,q1,q2> .& WF(DBPass)_<inp,mid,out,q1,q2> \
\                                 .& WF(DBDeq)_<inp,mid,out,q1,q2>  \ 
\  .-> WF(Deq inp qc out)_<inp,qc,out>";
by (auto_tac (db_css addSIs2 [leadsto_WF]));
by (auto_tac (db_css addSIs2 [(temp_mp DBFair_1) RSN(2,LatticeTransitivity)]));
by (auto_tac (db_css addSIs2 [(temp_mp DBFair_2) RSN(2,LatticeTransitivity)]));
by (auto_tac (db_css addSIs2 [ImplLeadsto] addSEs2 [STL4E]
                     addsimps2 [angle_def,DBDeq_def,Deq_def,hd_append]));
qed "DBFair";

(*** Main theorem ***)
goalw DBuffer.thy [DBuffer_def,Buffer_def,IBuffer_def] "DBuffer .-> Buffer inp out";
by (auto_tac (db_css addSIs2 (map temp_mp [eexI,DBInit,DB_step_simulation RS STL4,DBFair])));
qed "DBuffer_impl_Buffer";
