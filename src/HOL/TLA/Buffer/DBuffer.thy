(*  Title:      HOL/TLA/Buffer/DBuffer.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>Two FIFO buffers in a row, with interleaving assumption\<close>

theory DBuffer
imports Buffer
begin

axiomatization
  (* implementation variables *)
  inp  :: "nat stfun" and
  mid  :: "nat stfun" and
  out  :: "nat stfun" and
  q1   :: "nat list stfun" and
  q2   :: "nat list stfun" and
  qc   :: "nat list stfun" and

  DBInit :: stpred and
  DBEnq :: action and
  DBDeq :: action and
  DBPass :: action and
  DBNext :: action and
  DBuffer :: temporal
where
  DB_base:        "basevars (inp,mid,out,q1,q2)" and

  (* the concatenation of the two buffers *)
  qc_def:         "PRED qc == PRED (q2 @ q1)" and

  DBInit_def:     "DBInit   == PRED (BInit inp q1 mid  \<and>  BInit mid q2 out)" and
  DBEnq_def:      "DBEnq    == ACT  Enq inp q1 mid  \<and>  unchanged (q2,out)" and
  DBDeq_def:      "DBDeq    == ACT  Deq mid q2 out  \<and>  unchanged (inp,q1)" and
  DBPass_def:     "DBPass   == ACT  Deq inp q1 mid
                                 \<and> (q2$ = $q2 @ [ mid$ ])
                                 \<and> (out$ = $out)" and
  DBNext_def:     "DBNext   == ACT  (DBEnq \<or> DBDeq \<or> DBPass)" and
  DBuffer_def:    "DBuffer  == TEMP Init DBInit
                                 \<and> \<box>[DBNext]_(inp,mid,out,q1,q2)
                                 \<and> WF(DBDeq)_(inp,mid,out,q1,q2)
                                 \<and> WF(DBPass)_(inp,mid,out,q1,q2)"


declare qc_def [simp]

lemmas db_defs =
  BInit_def Enq_def Deq_def Next_def IBuffer_def Buffer_def
  DBInit_def DBEnq_def DBDeq_def DBPass_def DBNext_def DBuffer_def


(*** Proper initialization ***)
lemma DBInit: "\<turnstile> Init DBInit \<longrightarrow> Init (BInit inp qc out)"
  by (auto simp: Init_def DBInit_def BInit_def)


(*** Step simulation ***)
lemma DB_step_simulation: "\<turnstile> [DBNext]_(inp,mid,out,q1,q2) \<longrightarrow> [Next inp qc out]_(inp,qc,out)"
  apply (rule square_simulation)
   apply clarsimp
  apply (tactic
    \<open>action_simp_tac (\<^context> addsimps (@{thm hd_append} :: @{thms db_defs})) [] [] 1\<close>)
  done


(*** Simulation of fairness ***)

(* Compute enabledness predicates for DBDeq and DBPass actions *)
lemma DBDeq_visible: "\<turnstile> <DBDeq>_(inp,mid,out,q1,q2) = DBDeq"
  apply (unfold angle_def DBDeq_def Deq_def)
  apply (safe, simp (asm_lr))+
  done

lemma DBDeq_enabled: 
    "\<turnstile> Enabled (<DBDeq>_(inp,mid,out,q1,q2)) = (q2 \<noteq> #[])"
  apply (unfold DBDeq_visible [action_rewrite])
  apply (force intro!: DB_base [THEN base_enabled, temp_use]
    elim!: enabledE simp: angle_def DBDeq_def Deq_def)
  done

lemma DBPass_visible: "\<turnstile> <DBPass>_(inp,mid,out,q1,q2) = DBPass"
  by (auto simp: angle_def DBPass_def Deq_def)

lemma DBPass_enabled: 
    "\<turnstile> Enabled (<DBPass>_(inp,mid,out,q1,q2)) = (q1 \<noteq> #[])"
  apply (unfold DBPass_visible [action_rewrite])
  apply (force intro!: DB_base [THEN base_enabled, temp_use]
    elim!: enabledE simp: angle_def DBPass_def Deq_def)
  done


(* The plan for proving weak fairness at the higher level is to prove
   (0)  DBuffer => (Enabled (Deq inp qc out) \<leadsto> (Deq inp qc out))
   which is in turn reduced to the two leadsto conditions
   (1)  DBuffer => (Enabled (Deq inp qc out) \<leadsto> q2 \<noteq> [])
   (2)  DBuffer => (q2 \<noteq> [] \<leadsto> DBDeq)
   and the fact that DBDeq implies <Deq inp qc out>_(inp,qc,out)
   (and therefore DBDeq \<leadsto> <Deq inp qc out>_(inp,qc,out) trivially holds).

   Condition (1) is reduced to
   (1a) DBuffer => (qc \<noteq> [] /\ q2 = [] \<leadsto> q2 \<noteq> [])
   by standard leadsto rules (leadsto_classical) and rule Deq_enabledE.

   Both (1a) and (2) are proved from DBuffer's WF conditions by standard
   WF reasoning (Lamport's WF1 and WF_leadsto).
   The condition WF(Deq inp qc out) follows from (0) by rule leadsto_WF.

   One could use Lamport's WF2 instead.
*)

(* Condition (1a) *)
lemma DBFair_1a: "\<turnstile> \<box>[DBNext]_(inp,mid,out,q1,q2) \<and> WF(DBPass)_(inp,mid,out,q1,q2)  
         \<longrightarrow> (qc \<noteq> #[] \<and> q2 = #[] \<leadsto> q2 \<noteq> #[])"
  apply (rule WF1)
    apply (force simp: db_defs)
   apply (force simp: angle_def DBPass_def)
  apply (force simp: DBPass_enabled [temp_use])
  done

(* Condition (1) *)
lemma DBFair_1: "\<turnstile> \<box>[DBNext]_(inp,mid,out,q1,q2) \<and> WF(DBPass)_(inp,mid,out,q1,q2)  
         \<longrightarrow> (Enabled (<Deq inp qc out>_(inp,qc,out)) \<leadsto> q2 \<noteq> #[])"
  apply clarsimp
  apply (rule leadsto_classical [temp_use])
  apply (rule DBFair_1a [temp_use, THEN LatticeTransitivity [temp_use]])
  apply assumption+
  apply (rule ImplLeadsto_gen [temp_use])
  apply (force intro!: necT [temp_use] dest!: STL2_gen [temp_use] Deq_enabledE [temp_use]
    simp add: Init_defs)
  done

(* Condition (2) *)
lemma DBFair_2: "\<turnstile> \<box>[DBNext]_(inp,mid,out,q1,q2) \<and> WF(DBDeq)_(inp,mid,out,q1,q2)  
         \<longrightarrow> (q2 \<noteq> #[] \<leadsto> DBDeq)"
  apply (rule WF_leadsto)
    apply (force simp: DBDeq_enabled [temp_use])
   apply (force simp: angle_def)
  apply (force simp: db_defs elim!: Stable [temp_use])
  done

(* High-level fairness *)
lemma DBFair: "\<turnstile> \<box>[DBNext]_(inp,mid,out,q1,q2) \<and> WF(DBPass)_(inp,mid,out,q1,q2)  
                                        \<and> WF(DBDeq)_(inp,mid,out,q1,q2)   
         \<longrightarrow> WF(Deq inp qc out)_(inp,qc,out)"
  apply (auto simp del: qc_def intro!: leadsto_WF [temp_use]
    DBFair_1 [temp_use, THEN [2] LatticeTransitivity [temp_use]]
    DBFair_2 [temp_use, THEN [2] LatticeTransitivity [temp_use]])
  apply (auto intro!: ImplLeadsto_simple [temp_use]
    simp: angle_def DBDeq_def Deq_def hd_append [try_rewrite])
  done

(*** Main theorem ***)
lemma DBuffer_impl_Buffer: "\<turnstile> DBuffer \<longrightarrow> Buffer inp out"
  apply (unfold DBuffer_def Buffer_def IBuffer_def)
  apply (force intro!: eexI [temp_use] DBInit [temp_use]
    DB_step_simulation [THEN STL4, temp_use] DBFair [temp_use])
  done

end
