(*  Title:      HOL/UNITY/Mutex.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

theory Mutex = UNITY_Main:

record state =
  p :: bool
  m :: int
  n :: int
  u :: bool
  v :: bool

types command = "(state*state) set"

constdefs
  
  (** The program for process U **)
  
  U0 :: command
    "U0 == {(s,s'). s' = s (|u:=True, m:=1|) & m s = 0}"

  U1 :: command
    "U1 == {(s,s'). s' = s (|p:= v s, m:=2|) & m s = 1}"

  U2 :: command
    "U2 == {(s,s'). s' = s (|m:=3|) & ~ p s & m s = 2}"

  U3 :: command
    "U3 == {(s,s'). s' = s (|u:=False, m:=4|) & m s = 3}"

  U4 :: command
    "U4 == {(s,s'). s' = s (|p:=True, m:=0|) & m s = 4}"

  (** The program for process V **)
  
  V0 :: command
    "V0 == {(s,s'). s' = s (|v:=True, n:=1|) & n s = 0}"

  V1 :: command
    "V1 == {(s,s'). s' = s (|p:= ~ u s, n:=2|) & n s = 1}"

  V2 :: command
    "V2 == {(s,s'). s' = s (|n:=3|) & p s & n s = 2}"

  V3 :: command
    "V3 == {(s,s'). s' = s (|v:=False, n:=4|) & n s = 3}"

  V4 :: command
    "V4 == {(s,s'). s' = s (|p:=False, n:=0|) & n s = 4}"

  Mutex :: "state program"
    "Mutex == mk_program ({s. ~ u s & ~ v s & m s = 0 & n s = 0},
		 	  {U0, U1, U2, U3, U4, V0, V1, V2, V3, V4},
			  UNIV)"


  (** The correct invariants **)

  IU :: "state set"
    "IU == {s. (u s = (1 \<le> m s & m s \<le> 3)) & (m s = 3 --> ~ p s)}"

  IV :: "state set"
    "IV == {s. (v s = (1 \<le> n s & n s \<le> 3)) & (n s = 3 --> p s)}"

  (** The faulty invariant (for U alone) **)

  bad_IU :: "state set"
    "bad_IU == {s. (u s = (1 \<le> m s & m s \<le> 3)) &
	           (3 \<le> m s & m s \<le> 4 --> ~ p s)}"


declare Mutex_def [THEN def_prg_Init, simp]

declare U0_def [THEN def_act_simp, simp]
declare U1_def [THEN def_act_simp, simp]
declare U2_def [THEN def_act_simp, simp]
declare U3_def [THEN def_act_simp, simp]
declare U4_def [THEN def_act_simp, simp]
declare V0_def [THEN def_act_simp, simp]
declare V1_def [THEN def_act_simp, simp]
declare V2_def [THEN def_act_simp, simp]
declare V3_def [THEN def_act_simp, simp]
declare V4_def [THEN def_act_simp, simp]

declare IU_def [THEN def_set_simp, simp]
declare IV_def [THEN def_set_simp, simp]
declare bad_IU_def [THEN def_set_simp, simp]

lemma IU: "Mutex \<in> Always IU"
apply (rule AlwaysI, force) 
apply (unfold Mutex_def, constrains) 
done


lemma IV: "Mutex \<in> Always IV"
apply (rule AlwaysI, force) 
apply (unfold Mutex_def, constrains)
done

(*The safety property: mutual exclusion*)
lemma mutual_exclusion: "Mutex \<in> Always {s. ~ (m s = 3 & n s = 3)}"
apply (rule Always_weaken) 
apply (rule Always_Int_I [OF IU IV], auto)
done


(*The bad invariant FAILS in V1*)
lemma "Mutex \<in> Always bad_IU"
apply (rule AlwaysI, force) 
apply (unfold Mutex_def, constrains, auto)
(*Resulting state: n=1, p=false, m=4, u=false.  
  Execution of V1 (the command of process v guarded by n=1) sets p:=true,
  violating the invariant!*)
oops


lemma eq_123: "((1::int) \<le> i & i \<le> 3) = (i = 1 | i = 2 | i = 3)"
by arith


(*** Progress for U ***)

lemma U_F0: "Mutex \<in> {s. m s=2} Unless {s. m s=3}"
by (unfold Unless_def Mutex_def, constrains)

lemma U_F1: "Mutex \<in> {s. m s=1} LeadsTo {s. p s = v s & m s = 2}"
by (unfold Mutex_def, ensures_tac U1)

lemma U_F2: "Mutex \<in> {s. ~ p s & m s = 2} LeadsTo {s. m s = 3}"
apply (cut_tac IU)
apply (unfold Mutex_def, ensures_tac U2)
done

lemma U_F3: "Mutex \<in> {s. m s = 3} LeadsTo {s. p s}"
apply (rule_tac B = "{s. m s = 4}" in LeadsTo_Trans)
 apply (unfold Mutex_def)
 apply (ensures_tac U3)
apply (ensures_tac U4)
done

lemma U_lemma2: "Mutex \<in> {s. m s = 2} LeadsTo {s. p s}"
apply (rule LeadsTo_Diff [OF LeadsTo_weaken_L
                             Int_lower2 [THEN subset_imp_LeadsTo]])
apply (rule LeadsTo_Trans [OF U_F2 U_F3], auto)
done

lemma U_lemma1: "Mutex \<in> {s. m s = 1} LeadsTo {s. p s}"
by (rule LeadsTo_Trans [OF U_F1 [THEN LeadsTo_weaken_R] U_lemma2], blast)

lemma U_lemma123: "Mutex \<in> {s. 1 \<le> m s & m s \<le> 3} LeadsTo {s. p s}"
by (simp add: eq_123 Collect_disj_eq LeadsTo_Un_distrib U_lemma1 U_lemma2 U_F3)

(*Misra's F4*)
lemma u_Leadsto_p: "Mutex \<in> {s. u s} LeadsTo {s. p s}"
by (rule Always_LeadsTo_weaken [OF IU U_lemma123], auto)


(*** Progress for V ***)


lemma V_F0: "Mutex \<in> {s. n s=2} Unless {s. n s=3}"
by (unfold Unless_def Mutex_def, constrains)

lemma V_F1: "Mutex \<in> {s. n s=1} LeadsTo {s. p s = (~ u s) & n s = 2}"
by (unfold Mutex_def, ensures_tac "V1")

lemma V_F2: "Mutex \<in> {s. p s & n s = 2} LeadsTo {s. n s = 3}"
apply (cut_tac IV)
apply (unfold Mutex_def, ensures_tac "V2")
done

lemma V_F3: "Mutex \<in> {s. n s = 3} LeadsTo {s. ~ p s}"
apply (rule_tac B = "{s. n s = 4}" in LeadsTo_Trans)
 apply (unfold Mutex_def)
 apply (ensures_tac V3)
apply (ensures_tac V4)
done

lemma V_lemma2: "Mutex \<in> {s. n s = 2} LeadsTo {s. ~ p s}"
apply (rule LeadsTo_Diff [OF LeadsTo_weaken_L
                             Int_lower2 [THEN subset_imp_LeadsTo]])
apply (rule LeadsTo_Trans [OF V_F2 V_F3], auto) 
done

lemma V_lemma1: "Mutex \<in> {s. n s = 1} LeadsTo {s. ~ p s}"
by (rule LeadsTo_Trans [OF V_F1 [THEN LeadsTo_weaken_R] V_lemma2], blast)

lemma V_lemma123: "Mutex \<in> {s. 1 \<le> n s & n s \<le> 3} LeadsTo {s. ~ p s}"
by (simp add: eq_123 Collect_disj_eq LeadsTo_Un_distrib V_lemma1 V_lemma2 V_F3)


(*Misra's F4*)
lemma v_Leadsto_not_p: "Mutex \<in> {s. v s} LeadsTo {s. ~ p s}"
by (rule Always_LeadsTo_weaken [OF IV V_lemma123], auto)


(** Absence of starvation **)

(*Misra's F6*)
lemma m1_Leadsto_3: "Mutex \<in> {s. m s = 1} LeadsTo {s. m s = 3}"
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
apply (rule_tac [2] U_F2)
apply (simp add: Collect_conj_eq)
apply (subst Un_commute)
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
 apply (rule_tac [2] PSP_Unless [OF v_Leadsto_not_p U_F0])
apply (rule U_F1 [THEN LeadsTo_weaken_R], auto)
done

(*The same for V*)
lemma n1_Leadsto_3: "Mutex \<in> {s. n s = 1} LeadsTo {s. n s = 3}"
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
apply (rule_tac [2] V_F2)
apply (simp add: Collect_conj_eq)
apply (subst Un_commute)
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
 apply (rule_tac [2] PSP_Unless [OF u_Leadsto_p V_F0])
apply (rule V_F1 [THEN LeadsTo_weaken_R], auto)
done

end
