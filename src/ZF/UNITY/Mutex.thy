(*  Title:      ZF/UNITY/Mutex.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra.

Variables' types are introduced globally so that type verification
reduces to the usual ZF typechecking \<in> an ill-tyed expression will
reduce to the empty set.
*)

header{*Mutual Exclusion*}

theory Mutex
imports SubstAx
begin

text{*Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra

Variables' types are introduced globally so that type verification reduces to
the usual ZF typechecking: an ill-tyed expressions reduce to the empty set.
*}

abbreviation "p == Var([0])"
abbreviation "m == Var([1])"
abbreviation "n == Var([0,0])"
abbreviation "u == Var([0,1])"
abbreviation "v == Var([1,0])"

axiomatization where --{** Type declarations  **}
  p_type:  "type_of(p)=bool & default_val(p)=0" and
  m_type:  "type_of(m)=int  & default_val(m)=#0" and
  n_type:  "type_of(n)=int  & default_val(n)=#0" and
  u_type:  "type_of(u)=bool & default_val(u)=0" and
  v_type:  "type_of(v)=bool & default_val(v)=0"

definition
  (** The program for process U **)
  "U0 == {<s,t>:state*state. t = s(u:=1, m:=#1) & s`m = #0}"

definition
  "U1 == {<s,t>:state*state. t = s(p:= s`v, m:=#2) &  s`m = #1}"

definition
  "U2 == {<s,t>:state*state. t = s(m:=#3) & s`p=0 & s`m = #2}"

definition
  "U3 == {<s,t>:state*state. t=s(u:=0, m:=#4) & s`m = #3}"

definition
  "U4 == {<s,t>:state*state. t = s(p:=1, m:=#0) & s`m = #4}"


   (** The program for process V **)

definition
  "V0 == {<s,t>:state*state. t = s (v:=1, n:=#1) & s`n = #0}"

definition
  "V1 == {<s,t>:state*state. t = s(p:=not(s`u), n:=#2) & s`n = #1}"

definition
  "V2 == {<s,t>:state*state. t  = s(n:=#3) & s`p=1 & s`n = #2}"

definition
  "V3 == {<s,t>:state*state. t = s (v:=0, n:=#4) & s`n = #3}"

definition
  "V4 == {<s,t>:state*state. t  = s (p:=0, n:=#0) & s`n = #4}"

definition
  "Mutex == mk_program({s:state. s`u=0 & s`v=0 & s`m = #0 & s`n = #0},
              {U0, U1, U2, U3, U4, V0, V1, V2, V3, V4}, Pow(state*state))"

  (** The correct invariants **)

definition
  "IU == {s:state. (s`u = 1\<longleftrightarrow>(#1 $<= s`m & s`m $<= #3))
                     & (s`m = #3 \<longrightarrow> s`p=0)}"

definition
  "IV == {s:state. (s`v = 1 \<longleftrightarrow> (#1 $<= s`n & s`n $<= #3))
                      & (s`n = #3 \<longrightarrow> s`p=1)}"

  (** The faulty invariant (for U alone) **)

definition
  "bad_IU == {s:state. (s`u = 1 \<longleftrightarrow> (#1 $<= s`m & s`m  $<= #3))&
                   (#3 $<= s`m & s`m $<= #4 \<longrightarrow> s`p=0)}"


(** Variables' types **)

declare p_type [simp] u_type [simp] v_type [simp] m_type [simp] n_type [simp]

lemma u_value_type: "s \<in> state ==>s`u \<in> bool"
apply (unfold state_def)
apply (drule_tac a = u in apply_type, auto)
done

lemma v_value_type: "s \<in> state ==> s`v \<in> bool"
apply (unfold state_def)
apply (drule_tac a = v in apply_type, auto)
done

lemma p_value_type: "s \<in> state ==> s`p \<in> bool"
apply (unfold state_def)
apply (drule_tac a = p in apply_type, auto)
done

lemma m_value_type: "s \<in> state ==> s`m \<in> int"
apply (unfold state_def)
apply (drule_tac a = m in apply_type, auto)
done

lemma n_value_type: "s \<in> state ==>s`n \<in> int"
apply (unfold state_def)
apply (drule_tac a = n in apply_type, auto)
done

declare p_value_type [simp] u_value_type [simp] v_value_type [simp]
        m_value_type [simp] n_value_type [simp]

declare p_value_type [TC] u_value_type [TC] v_value_type [TC]
        m_value_type [TC] n_value_type [TC]



text{*Mutex is a program*}

lemma Mutex_in_program [simp,TC]: "Mutex \<in> program"
by (simp add: Mutex_def)


declare Mutex_def [THEN def_prg_Init, simp]
declare Mutex_def [program]

declare  U0_def [THEN def_act_simp, simp]
declare  U1_def [THEN def_act_simp, simp]
declare  U2_def [THEN def_act_simp, simp]
declare  U3_def [THEN def_act_simp, simp]
declare  U4_def [THEN def_act_simp, simp]

declare  V0_def [THEN def_act_simp, simp]
declare  V1_def [THEN def_act_simp, simp]
declare  V2_def [THEN def_act_simp, simp]
declare  V3_def [THEN def_act_simp, simp]
declare  V4_def [THEN def_act_simp, simp]

declare  U0_def [THEN def_set_simp, simp]
declare  U1_def [THEN def_set_simp, simp]
declare  U2_def [THEN def_set_simp, simp]
declare  U3_def [THEN def_set_simp, simp]
declare  U4_def [THEN def_set_simp, simp]

declare  V0_def [THEN def_set_simp, simp]
declare  V1_def [THEN def_set_simp, simp]
declare  V2_def [THEN def_set_simp, simp]
declare  V3_def [THEN def_set_simp, simp]
declare  V4_def [THEN def_set_simp, simp]

declare  IU_def [THEN def_set_simp, simp]
declare  IV_def [THEN def_set_simp, simp]
declare  bad_IU_def [THEN def_set_simp, simp]

lemma IU: "Mutex \<in> Always(IU)"
apply (rule AlwaysI, force)
apply (unfold Mutex_def, safety, auto)
done

lemma IV: "Mutex \<in> Always(IV)"
apply (rule AlwaysI, force)
apply (unfold Mutex_def, safety)
done

(*The safety property: mutual exclusion*)
lemma mutual_exclusion: "Mutex \<in> Always({s \<in> state. ~(s`m = #3 & s`n = #3)})"
apply (rule Always_weaken)
apply (rule Always_Int_I [OF IU IV], auto)
done

(*The bad invariant FAILS in V1*)

lemma less_lemma: "[| x$<#1; #3 $<= x |] ==> P"
apply (drule_tac j = "#1" and k = "#3" in zless_zle_trans)
apply (drule_tac [2] j = x in zle_zless_trans, auto)
done

lemma "Mutex \<in> Always(bad_IU)"
apply (rule AlwaysI, force)
apply (unfold Mutex_def, safety, auto)
apply (subgoal_tac "#1 $<= #3")
apply (drule_tac x = "#1" and y = "#3" in zle_trans, auto)
apply (simp (no_asm) add: not_zless_iff_zle [THEN iff_sym])
apply auto
(*Resulting state: n=1, p=false, m=4, u=false.
  Execution of V1 (the command of process v guarded by n=1) sets p:=true,
  violating the invariant!*)
oops



(*** Progress for U ***)

lemma U_F0: "Mutex \<in> {s \<in> state. s`m=#2} Unless {s \<in> state. s`m=#3}"
by (unfold op_Unless_def Mutex_def, safety)

lemma U_F1:
     "Mutex \<in> {s \<in> state. s`m=#1} LeadsTo {s \<in> state. s`p = s`v & s`m = #2}"
by (unfold Mutex_def, ensures U1)

lemma U_F2: "Mutex \<in> {s \<in> state. s`p =0 & s`m = #2} LeadsTo {s \<in> state. s`m = #3}"
apply (cut_tac IU)
apply (unfold Mutex_def, ensures U2)
done

lemma U_F3: "Mutex \<in> {s \<in> state. s`m = #3} LeadsTo {s \<in> state. s`p=1}"
apply (rule_tac B = "{s \<in> state. s`m = #4}" in LeadsTo_Trans)
 apply (unfold Mutex_def)
 apply (ensures U3)
apply (ensures U4)
done


lemma U_lemma2: "Mutex \<in> {s \<in> state. s`m = #2} LeadsTo {s \<in> state. s`p=1}"
apply (rule LeadsTo_Diff [OF LeadsTo_weaken_L
                             Int_lower2 [THEN subset_imp_LeadsTo]])
apply (rule LeadsTo_Trans [OF U_F2 U_F3], auto)
apply (auto dest!: p_value_type simp add: bool_def)
done

lemma U_lemma1: "Mutex \<in> {s \<in> state. s`m = #1} LeadsTo {s \<in> state. s`p =1}"
by (rule LeadsTo_Trans [OF U_F1 [THEN LeadsTo_weaken_R] U_lemma2], blast)

lemma eq_123: "i \<in> int ==> (#1 $<= i & i $<= #3) \<longleftrightarrow> (i=#1 | i=#2 | i=#3)"
apply auto
apply (auto simp add: neq_iff_zless)
apply (drule_tac [4] j = "#3" and i = i in zle_zless_trans)
apply (drule_tac [2] j = i and i = "#1" in zle_zless_trans)
apply (drule_tac j = i and i = "#1" in zle_zless_trans, auto)
apply (rule zle_anti_sym)
apply (simp_all (no_asm_simp) add: zless_add1_iff_zle [THEN iff_sym])
done


lemma U_lemma123: "Mutex \<in> {s \<in> state. #1 $<= s`m & s`m $<= #3} LeadsTo {s \<in> state. s`p=1}"
by (simp add: eq_123 Collect_disj_eq LeadsTo_Un_distrib U_lemma1 U_lemma2 U_F3)


(*Misra's F4*)
lemma u_Leadsto_p: "Mutex \<in> {s \<in> state. s`u = 1} LeadsTo {s \<in> state. s`p=1}"
by (rule Always_LeadsTo_weaken [OF IU U_lemma123], auto)


(*** Progress for V ***)

lemma V_F0: "Mutex \<in> {s \<in> state. s`n=#2} Unless {s \<in> state. s`n=#3}"
by (unfold op_Unless_def Mutex_def, safety)

lemma V_F1: "Mutex \<in> {s \<in> state. s`n=#1} LeadsTo {s \<in> state. s`p = not(s`u) & s`n = #2}"
by (unfold Mutex_def, ensures "V1")

lemma V_F2: "Mutex \<in> {s \<in> state. s`p=1 & s`n = #2} LeadsTo {s \<in> state. s`n = #3}"
apply (cut_tac IV)
apply (unfold Mutex_def, ensures "V2")
done

lemma V_F3: "Mutex \<in> {s \<in> state. s`n = #3} LeadsTo {s \<in> state. s`p=0}"
apply (rule_tac B = "{s \<in> state. s`n = #4}" in LeadsTo_Trans)
 apply (unfold Mutex_def)
 apply (ensures V3)
apply (ensures V4)
done

lemma V_lemma2: "Mutex \<in> {s \<in> state. s`n = #2} LeadsTo {s \<in> state. s`p=0}"
apply (rule LeadsTo_Diff [OF LeadsTo_weaken_L
                             Int_lower2 [THEN subset_imp_LeadsTo]])
apply (rule LeadsTo_Trans [OF V_F2 V_F3], auto)
apply (auto dest!: p_value_type simp add: bool_def)
done

lemma V_lemma1: "Mutex \<in> {s \<in> state. s`n = #1} LeadsTo {s \<in> state. s`p = 0}"
by (rule LeadsTo_Trans [OF V_F1 [THEN LeadsTo_weaken_R] V_lemma2], blast)

lemma V_lemma123: "Mutex \<in> {s \<in> state. #1 $<= s`n & s`n $<= #3} LeadsTo {s \<in> state. s`p = 0}"
by (simp add: eq_123 Collect_disj_eq LeadsTo_Un_distrib V_lemma1 V_lemma2 V_F3)

(*Misra's F4*)
lemma v_Leadsto_not_p: "Mutex \<in> {s \<in> state. s`v = 1} LeadsTo {s \<in> state. s`p = 0}"
by (rule Always_LeadsTo_weaken [OF IV V_lemma123], auto)


(** Absence of starvation **)

(*Misra's F6*)
lemma m1_Leadsto_3: "Mutex \<in> {s \<in> state. s`m = #1} LeadsTo {s \<in> state. s`m = #3}"
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
apply (rule_tac [2] U_F2)
apply (simp add: Collect_conj_eq)
apply (subst Un_commute)
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
 apply (rule_tac [2] PSP_Unless [OF v_Leadsto_not_p U_F0])
apply (rule U_F1 [THEN LeadsTo_weaken_R], auto)
apply (auto dest!: v_value_type simp add: bool_def)
done


(*The same for V*)
lemma n1_Leadsto_3: "Mutex \<in> {s \<in> state. s`n = #1} LeadsTo {s \<in> state. s`n = #3}"
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
apply (rule_tac [2] V_F2)
apply (simp add: Collect_conj_eq)
apply (subst Un_commute)
apply (rule LeadsTo_cancel2 [THEN LeadsTo_Un_duplicate])
 apply (rule_tac [2] PSP_Unless [OF u_Leadsto_p V_F0])
apply (rule V_F1 [THEN LeadsTo_weaken_R], auto)
apply (auto dest!: u_value_type simp add: bool_def)
done

end