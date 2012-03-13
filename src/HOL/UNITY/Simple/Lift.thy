(*  Title:      HOL/UNITY/Simple/Lift.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Lift-Control Example.
*)

theory Lift
imports "../UNITY_Main"
begin

record state =
  floor :: "int"            --{*current position of the lift*}
  "open" :: "bool"          --{*whether the door is opened at floor*}
  stop  :: "bool"           --{*whether the lift is stopped at floor*}
  req   :: "int set"        --{*for each floor, whether the lift is requested*}
  up    :: "bool"           --{*current direction of movement*}
  move  :: "bool"           --{*whether moving takes precedence over opening*}

axiomatization
  Min :: "int" and   --{*least and greatest floors*}
  Max :: "int"       --{*least and greatest floors*}
where
  Min_le_Max [iff]: "Min \<le> Max"
  
  
  --{*Abbreviations: the "always" part*}
  
definition
  above :: "state set"
  where "above = {s. \<exists>i. floor s < i & i \<le> Max & i \<in> req s}"

definition
  below :: "state set"
  where "below = {s. \<exists>i. Min \<le> i & i < floor s & i \<in> req s}"

definition
  queueing :: "state set"
  where "queueing = above \<union> below"

definition
  goingup :: "state set"
  where "goingup = above \<inter> ({s. up s}  \<union> -below)"

definition
  goingdown :: "state set"
  where "goingdown = below \<inter> ({s. ~ up s} \<union> -above)"

definition
  ready :: "state set"
  where "ready = {s. stop s & ~ open s & move s}"
 
  --{*Further abbreviations*}

definition
  moving :: "state set"
  where "moving = {s. ~ stop s & ~ open s}"

definition
  stopped :: "state set"
  where "stopped = {s. stop s  & ~ open s & ~ move s}"

definition
  opened :: "state set"
  where "opened = {s. stop s  &  open s  &  move s}"

definition
  closed :: "state set"  --{*but this is the same as ready!!*}
  where "closed = {s. stop s  & ~ open s &  move s}"

definition
  atFloor :: "int => state set"
  where "atFloor n = {s. floor s = n}"

definition
  Req :: "int => state set"
  where "Req n = {s. n \<in> req s}"


  
  --{*The program*}
  
definition
  request_act :: "(state*state) set"
  where "request_act = {(s,s'). s' = s (|stop:=True, move:=False|)
                                  & ~ stop s & floor s \<in> req s}"

definition
  open_act :: "(state*state) set"
  where "open_act =
         {(s,s'). s' = s (|open :=True,
                           req  := req s - {floor s},
                           move := True|)
                       & stop s & ~ open s & floor s \<in> req s
                       & ~(move s & s \<in> queueing)}"

definition
  close_act :: "(state*state) set"
  where "close_act = {(s,s'). s' = s (|open := False|) & open s}"

definition
  req_up :: "(state*state) set"
  where "req_up =
         {(s,s'). s' = s (|stop  :=False,
                           floor := floor s + 1,
                           up    := True|)
                       & s \<in> (ready \<inter> goingup)}"

definition
  req_down :: "(state*state) set"
  where "req_down =
         {(s,s'). s' = s (|stop  :=False,
                           floor := floor s - 1,
                           up    := False|)
                       & s \<in> (ready \<inter> goingdown)}"

definition
  move_up :: "(state*state) set"
  where "move_up =
         {(s,s'). s' = s (|floor := floor s + 1|)
                       & ~ stop s & up s & floor s \<notin> req s}"

definition
  move_down :: "(state*state) set"
  where "move_down =
         {(s,s'). s' = s (|floor := floor s - 1|)
                       & ~ stop s & ~ up s & floor s \<notin> req s}"

definition
  button_press  :: "(state*state) set"
      --{*This action is omitted from prior treatments, which therefore are
        unrealistic: nobody asks the lift to do anything!  But adding this
        action invalidates many of the existing progress arguments: various
        "ensures" properties fail. Maybe it should be constrained to only
        allow button presses in the current direction of travel, like in a
        real lift.*}
  where "button_press =
         {(s,s'). \<exists>n. s' = s (|req := insert n (req s)|)
                        & Min \<le> n & n \<le> Max}"


definition
  Lift :: "state program"
    --{*for the moment, we OMIT @{text button_press}*}
  where "Lift = mk_total_program
                ({s. floor s = Min & ~ up s & move s & stop s &
                          ~ open s & req s = {}},
                 {request_act, open_act, close_act,
                  req_up, req_down, move_up, move_down},
                 UNIV)"


  --{*Invariants*}

definition
  bounded :: "state set"
  where "bounded = {s. Min \<le> floor s & floor s \<le> Max}"

definition
  open_stop :: "state set"
  where "open_stop = {s. open s --> stop s}"
  
definition
  open_move :: "state set"
  where "open_move = {s. open s --> move s}"
  
definition
  stop_floor :: "state set"
  where "stop_floor = {s. stop s & ~ move s --> floor s \<in> req s}"
  
definition
  moving_up :: "state set"
  where "moving_up = {s. ~ stop s & up s -->
                   (\<exists>f. floor s \<le> f & f \<le> Max & f \<in> req s)}"
  
definition
  moving_down :: "state set"
  where "moving_down = {s. ~ stop s & ~ up s -->
                     (\<exists>f. Min \<le> f & f \<le> floor s & f \<in> req s)}"
  
definition
  metric :: "[int,state] => int"
  where "metric =
       (%n s. if floor s < n then (if up s then n - floor s
                                  else (floor s - Min) + (n-Min))
             else
             if n < floor s then (if up s then (Max - floor s) + (Max-n)
                                  else floor s - n)
             else 0)"

locale Floor =
  fixes n
  assumes Min_le_n [iff]: "Min \<le> n"
      and n_le_Max [iff]: "n \<le> Max"

lemma not_mem_distinct: "[| x \<notin> A;  y \<in> A |] ==> x \<noteq> y"
by blast


declare Lift_def [THEN def_prg_Init, simp]

declare request_act_def [THEN def_act_simp, simp]
declare open_act_def [THEN def_act_simp, simp]
declare close_act_def [THEN def_act_simp, simp]
declare req_up_def [THEN def_act_simp, simp]
declare req_down_def [THEN def_act_simp, simp]
declare move_up_def [THEN def_act_simp, simp]
declare move_down_def [THEN def_act_simp, simp]
declare button_press_def [THEN def_act_simp, simp]

(*The ALWAYS properties*)
declare above_def [THEN def_set_simp, simp]
declare below_def [THEN def_set_simp, simp]
declare queueing_def [THEN def_set_simp, simp]
declare goingup_def [THEN def_set_simp, simp]
declare goingdown_def [THEN def_set_simp, simp]
declare ready_def [THEN def_set_simp, simp]

(*Basic definitions*)
declare bounded_def [simp] 
        open_stop_def [simp] 
        open_move_def [simp] 
        stop_floor_def [simp]
        moving_up_def [simp]
        moving_down_def [simp]

lemma open_stop: "Lift \<in> Always open_stop"
apply (rule AlwaysI, force) 
apply (unfold Lift_def, safety)
done

lemma stop_floor: "Lift \<in> Always stop_floor"
apply (rule AlwaysI, force) 
apply (unfold Lift_def, safety)
done

(*This one needs open_stop, which was proved above*)
lemma open_move: "Lift \<in> Always open_move"
apply (cut_tac open_stop)
apply (rule AlwaysI, force) 
apply (unfold Lift_def, safety)
done

lemma moving_up: "Lift \<in> Always moving_up"
apply (rule AlwaysI, force) 
apply (unfold Lift_def, safety)
apply (auto dest: order_le_imp_less_or_eq simp add: add1_zle_eq)
done

lemma moving_down: "Lift \<in> Always moving_down"
apply (rule AlwaysI, force) 
apply (unfold Lift_def, safety)
apply (blast dest: order_le_imp_less_or_eq)
done

lemma bounded: "Lift \<in> Always bounded"
apply (cut_tac moving_up moving_down)
apply (rule AlwaysI, force) 
apply (unfold Lift_def, safety, auto)
apply (drule not_mem_distinct, assumption, arith)+
done


subsection{*Progress*}

declare moving_def [THEN def_set_simp, simp]
declare stopped_def [THEN def_set_simp, simp]
declare opened_def [THEN def_set_simp, simp]
declare closed_def [THEN def_set_simp, simp]
declare atFloor_def [THEN def_set_simp, simp]
declare Req_def [THEN def_set_simp, simp]


text{*The HUG'93 paper mistakenly omits the Req n from these!*}

(** Lift_1 **)
lemma E_thm01: "Lift \<in> (stopped \<inter> atFloor n) LeadsTo (opened \<inter> atFloor n)"
apply (cut_tac stop_floor)
apply (unfold Lift_def, ensures_tac "open_act")
done  (*lem_lift_1_5*)




lemma E_thm02: "Lift \<in> (Req n \<inter> stopped - atFloor n) LeadsTo  
                       (Req n \<inter> opened - atFloor n)"
apply (cut_tac stop_floor)
apply (unfold Lift_def, ensures_tac "open_act")
done  (*lem_lift_1_1*)

lemma E_thm03: "Lift \<in> (Req n \<inter> opened - atFloor n) LeadsTo  
                       (Req n \<inter> closed - (atFloor n - queueing))"
apply (unfold Lift_def, ensures_tac "close_act")
done  (*lem_lift_1_2*)

lemma E_thm04: "Lift \<in> (Req n \<inter> closed \<inter> (atFloor n - queueing))   
                       LeadsTo (opened \<inter> atFloor n)"
apply (unfold Lift_def, ensures_tac "open_act")
done  (*lem_lift_1_7*)


(** Lift 2.  Statements of thm05a and thm05b were wrong! **)

lemmas linorder_leI = linorder_not_less [THEN iffD1]

context Floor
begin

lemmas le_MinD = Min_le_n [THEN order_antisym]
  and Max_leD = n_le_Max [THEN [2] order_antisym]

declare le_MinD [dest!]
  and linorder_leI [THEN le_MinD, dest!]
  and Max_leD [dest!]
  and linorder_leI [THEN Max_leD, dest!]


(*lem_lift_2_0 
  NOT an ensures_tac property, but a mere inclusion
  don't know why script lift_2.uni says ENSURES*)
lemma E_thm05c: 
    "Lift \<in> (Req n \<inter> closed - (atFloor n - queueing))    
             LeadsTo ((closed \<inter> goingup \<inter> Req n)  \<union> 
                      (closed \<inter> goingdown \<inter> Req n))"
by (auto intro!: subset_imp_LeadsTo simp add: linorder_neq_iff)

(*lift_2*)
lemma lift_2: "Lift \<in> (Req n \<inter> closed - (atFloor n - queueing))    
             LeadsTo (moving \<inter> Req n)"
apply (rule LeadsTo_Trans [OF E_thm05c LeadsTo_Un])
apply (unfold Lift_def) 
apply (ensures_tac [2] "req_down")
apply (ensures_tac "req_up", auto)
done


(** Towards lift_4 ***)
 
declare split_if_asm [split]


(*lem_lift_4_1 *)
lemma E_thm12a:
     "0 < N ==>  
      Lift \<in> (moving \<inter> Req n \<inter> {s. metric n s = N} \<inter> 
              {s. floor s \<notin> req s} \<inter> {s. up s})    
             LeadsTo  
               (moving \<inter> Req n \<inter> {s. metric n s < N})"
apply (cut_tac moving_up)
apply (unfold Lift_def, ensures_tac "move_up", safe)
(*this step consolidates two formulae to the goal  metric n s' \<le> metric n s*)
apply (erule linorder_leI [THEN order_antisym, symmetric])
apply (auto simp add: metric_def)
done


(*lem_lift_4_3 *)
lemma E_thm12b: "0 < N ==>  
      Lift \<in> (moving \<inter> Req n \<inter> {s. metric n s = N} \<inter> 
              {s. floor s \<notin> req s} - {s. up s})    
             LeadsTo (moving \<inter> Req n \<inter> {s. metric n s < N})"
apply (cut_tac moving_down)
apply (unfold Lift_def, ensures_tac "move_down", safe)
(*this step consolidates two formulae to the goal  metric n s' \<le> metric n s*)
apply (erule linorder_leI [THEN order_antisym, symmetric])
apply (auto simp add: metric_def)
done

(*lift_4*)
lemma lift_4:
     "0<N ==> Lift \<in> (moving \<inter> Req n \<inter> {s. metric n s = N} \<inter> 
                            {s. floor s \<notin> req s}) LeadsTo      
                           (moving \<inter> Req n \<inter> {s. metric n s < N})"
apply (rule LeadsTo_Trans [OF subset_imp_LeadsTo
                              LeadsTo_Un [OF E_thm12a E_thm12b]], auto)
done


(** towards lift_5 **)

(*lem_lift_5_3*)
lemma E_thm16a: "0<N    
  ==> Lift \<in> (closed \<inter> Req n \<inter> {s. metric n s = N} \<inter> goingup) LeadsTo  
             (moving \<inter> Req n \<inter> {s. metric n s < N})"
apply (cut_tac bounded)
apply (unfold Lift_def, ensures_tac "req_up")
apply (auto simp add: metric_def)
done


(*lem_lift_5_1 has ~goingup instead of goingdown*)
lemma E_thm16b: "0<N ==>    
      Lift \<in> (closed \<inter> Req n \<inter> {s. metric n s = N} \<inter> goingdown) LeadsTo  
                   (moving \<inter> Req n \<inter> {s. metric n s < N})"
apply (cut_tac bounded)
apply (unfold Lift_def, ensures_tac "req_down")
apply (auto simp add: metric_def)
done


(*lem_lift_5_0 proves an intersection involving ~goingup and goingup,
  i.e. the trivial disjunction, leading to an asymmetrical proof.*)
lemma E_thm16c:
     "0<N ==> Req n \<inter> {s. metric n s = N} \<subseteq> goingup \<union> goingdown"
by (force simp add: metric_def)


(*lift_5*)
lemma lift_5:
     "0<N ==> Lift \<in> (closed \<inter> Req n \<inter> {s. metric n s = N}) LeadsTo    
                     (moving \<inter> Req n \<inter> {s. metric n s < N})"
apply (rule LeadsTo_Trans [OF subset_imp_LeadsTo
                              LeadsTo_Un [OF E_thm16a E_thm16b]])
apply (drule E_thm16c, auto)
done


(** towards lift_3 **)

(*lemma used to prove lem_lift_3_1*)
lemma metric_eq_0D [dest]:
     "[| metric n s = 0;  Min \<le> floor s;  floor s \<le> Max |] ==> floor s = n"
by (force simp add: metric_def)


(*lem_lift_3_1*)
lemma E_thm11: "Lift \<in> (moving \<inter> Req n \<inter> {s. metric n s = 0}) LeadsTo    
                       (stopped \<inter> atFloor n)"
apply (cut_tac bounded)
apply (unfold Lift_def, ensures_tac "request_act", auto)
done

(*lem_lift_3_5*)
lemma E_thm13: 
  "Lift \<in> (moving \<inter> Req n \<inter> {s. metric n s = N} \<inter> {s. floor s \<in> req s})  
  LeadsTo (stopped \<inter> Req n \<inter> {s. metric n s = N} \<inter> {s. floor s \<in> req s})"
apply (unfold Lift_def, ensures_tac "request_act")
apply (auto simp add: metric_def)
done

(*lem_lift_3_6*)
lemma E_thm14: "0 < N ==>  
      Lift \<in>  
        (stopped \<inter> Req n \<inter> {s. metric n s = N} \<inter> {s. floor s \<in> req s})  
        LeadsTo (opened \<inter> Req n \<inter> {s. metric n s = N})"
apply (unfold Lift_def, ensures_tac "open_act")
apply (auto simp add: metric_def)
done

(*lem_lift_3_7*)
lemma E_thm15: "Lift \<in> (opened \<inter> Req n \<inter> {s. metric n s = N})   
             LeadsTo (closed \<inter> Req n \<inter> {s. metric n s = N})"
apply (unfold Lift_def, ensures_tac "close_act")
apply (auto simp add: metric_def)
done


(** the final steps **)

lemma lift_3_Req: "0 < N ==>  
      Lift \<in>  
        (moving \<inter> Req n \<inter> {s. metric n s = N} \<inter> {s. floor s \<in> req s})    
        LeadsTo (moving \<inter> Req n \<inter> {s. metric n s < N})"
apply (blast intro!: E_thm13 E_thm14 E_thm15 lift_5 intro: LeadsTo_Trans)
done


(*Now we observe that our integer metric is really a natural number*)
lemma Always_nonneg: "Lift \<in> Always {s. 0 \<le> metric n s}"
apply (rule bounded [THEN Always_weaken])
apply (auto simp add: metric_def)
done

lemmas R_thm11 = Always_LeadsTo_weaken [OF Always_nonneg E_thm11]

lemma lift_3: "Lift \<in> (moving \<inter> Req n) LeadsTo (stopped \<inter> atFloor n)"
apply (rule Always_nonneg [THEN integ_0_le_induct])
apply (case_tac "0 < z")
(*If z \<le> 0 then actually z = 0*)
prefer 2 apply (force intro: R_thm11 order_antisym simp add: linorder_not_less)
apply (rule LeadsTo_weaken_R [OF asm_rl Un_upper1])
apply (rule LeadsTo_Trans [OF subset_imp_LeadsTo
                              LeadsTo_Un [OF lift_4 lift_3_Req]], auto)
done


lemma lift_1: "Lift \<in> (Req n) LeadsTo (opened \<inter> atFloor n)"
apply (rule LeadsTo_Trans)
 prefer 2
 apply (rule LeadsTo_Un [OF E_thm04 LeadsTo_Un_post])
 apply (rule E_thm01 [THEN [2] LeadsTo_Trans_Un])
 apply (rule lift_3 [THEN [2] LeadsTo_Trans_Un])
 apply (rule lift_2 [THEN [2] LeadsTo_Trans_Un])
 apply (rule LeadsTo_Trans_Un [OF E_thm02 E_thm03])
apply (rule open_move [THEN Always_LeadsToI])
apply (rule Always_LeadsToI [OF open_stop subset_imp_LeadsTo], clarify)
(*The case split is not essential but makes the proof much faster.*)
apply (case_tac "open x", auto)
done

end

end
