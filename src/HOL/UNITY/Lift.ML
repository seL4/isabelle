(*  Title:      HOL/UNITY/Lift
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Lift-Control Example
*)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper record_split_name;

Goal "[| x ~: A;  y : A |] ==> x ~= y";
by (Blast_tac 1);
qed "not_mem_distinct";

fun distinct_tac i =
    dtac zle_neq_implies_zless i THEN
    eresolve_tac [not_mem_distinct, not_mem_distinct RS not_sym] i THEN
    assume_tac i;


(** Rules to move "metric n s" out of the assumptions, for case splitting **)
val mov_metric1 = read_instantiate_sg (sign_of thy) 
                   [("P", "?x < metric ?n ?s")] rev_mp;

val mov_metric2 = read_instantiate_sg (sign_of thy) 
                   [("P", "?x = metric ?n ?s")] rev_mp;

val mov_metric3 = read_instantiate_sg (sign_of thy) 
                   [("P", "~ (?x < metric ?n ?s)")] rev_mp;

val mov_metric4 = read_instantiate_sg (sign_of thy) 
                   [("P", "(?x <= metric ?n ?s)")] rev_mp;

(*The order in which they are applied seems to be critical...*)
val mov_metrics = [mov_metric2, mov_metric3, mov_metric1, mov_metric4];

val metric_simps = [metric_def, vimage_def];


Addsimps [Lift_def RS def_prg_Init];
program_defs_ref := [Lift_def];

Addsimps (map simp_of_act
	  [request_act_def, open_act_def, close_act_def,
	   req_up_def, req_down_def, move_up_def, move_down_def,
	   button_press_def]);

val always_defs = [above_def, below_def, queueing_def, 
		   goingup_def, goingdown_def, ready_def];

Addsimps (map simp_of_set always_defs);


val LeadsTo_Trans_Un' = rotate_prems 1 LeadsTo_Trans_Un;
(* [| Lift: B LeadsTo C; Lift: A LeadsTo B |] ==> Lift: (A Un B) LeadsTo C *)


(*Simplification for records*)
Addsimps (thms"state.update_defs");

Addsimps [bounded_def, open_stop_def, open_move_def, stop_floor_def,
	  moving_up_def, moving_down_def];

AddIffs [Min_le_Max];


Goal "Lift : Always open_stop";
by (rtac AlwaysI 1);
by (Force_tac 1);
by (constrains_tac 1);
qed "open_stop";

Goal "Lift : Always stop_floor";
by (rtac AlwaysI 1);
by (Force_tac 1);
by (constrains_tac 1);
qed "stop_floor";

(*This one needs open_stop, which was proved above*)
Goal "Lift : Always open_move";
by (rtac AlwaysI 1);
by (rtac (open_stop RS Always_ConstrainsI RS StableI) 2);
by (Force_tac 1);
by (constrains_tac 1);
qed "open_move";

Goal "Lift : Always moving_up";
by (rtac AlwaysI 1);
by (Force_tac 1);
by (constrains_tac 1);
by (blast_tac (claset() addDs [zle_imp_zless_or_eq]) 1);
qed "moving_up";

Goal "Lift : Always moving_down";
by (rtac AlwaysI 1);
by (Force_tac 1);
by (constrains_tac 1);
by (blast_tac (claset() addDs [zle_imp_zless_or_eq]) 1);
qed "moving_down";

Goal "Lift : Always bounded";
by (rtac AlwaysI 1);
by (rtac (Always_Int_rule [moving_up, moving_down] RS Always_StableI) 2);
by (Force_tac 1);
by (constrains_tac 1);
by (ALLGOALS Clarify_tac);
by (REPEAT_FIRST distinct_tac);
by Auto_tac;
qed "bounded";



(*** Progress ***)


val abbrev_defs = [moving_def, stopped_def, 
		   opened_def, closed_def, atFloor_def, Req_def];

Addsimps (map simp_of_set abbrev_defs);


(** The HUG'93 paper mistakenly omits the Req n from these! **)

(** Lift_1 **)

Goal "Lift : (stopped Int atFloor n) LeadsTo (opened Int atFloor n)";
by (cut_facts_tac [stop_floor] 1);
by (ensures_tac "open_act" 1);
qed "E_thm01";  (*lem_lift_1_5*)

Goal "Lift : (Req n Int stopped - atFloor n) LeadsTo \
\                    (Req n Int opened - atFloor n)";
by (cut_facts_tac [stop_floor] 1);
by (ensures_tac "open_act" 1);
qed "E_thm02";  (*lem_lift_1_1*)

Goal "Lift : (Req n Int opened - atFloor n) LeadsTo \
\                    (Req n Int closed - (atFloor n - queueing))";
by (ensures_tac "close_act" 1);
qed "E_thm03";  (*lem_lift_1_2*)

Goal "Lift : (Req n Int closed Int (atFloor n - queueing))  \
\            LeadsTo (opened Int atFloor n)";
by (ensures_tac "open_act" 1);
qed "E_thm04";  (*lem_lift_1_7*)


(** Lift 2.  Statements of thm05a and thm05b were wrong! **)

Open_locale "floor"; 

val Min_le_n = thm "Min_le_n";
val n_le_Max = thm "n_le_Max";

AddIffs [Min_le_n, n_le_Max];

val le_MinD = Min_le_n RS order_antisym;
val Max_leD = n_le_Max RSN (2,order_antisym);

val linorder_leI = linorder_not_less RS iffD1;

AddSDs [le_MinD, linorder_leI RS le_MinD,
	Max_leD, linorder_leI RS Max_leD];

(*lem_lift_2_0 
  NOT an ensures property, but a mere inclusion;
  don't know why script lift_2.uni says ENSURES*)
Goal "Lift : (Req n Int closed - (atFloor n - queueing))   \
\            LeadsTo ((closed Int goingup Int Req n)  Un \
\                     (closed Int goingdown Int Req n))";
by (rtac subset_imp_LeadsTo 1);
by (auto_tac (claset() addSEs [int_neqE], simpset()));
qed "E_thm05c";

(*lift_2*)
Goal "Lift : (Req n Int closed - (atFloor n - queueing))   \
\            LeadsTo (moving Int Req n)";
by (rtac ([E_thm05c, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (ensures_tac "req_down" 2);
by (ensures_tac "req_up" 1);
by Auto_tac;
qed "lift_2";


(** Towards lift_4 ***)
 

(*lem_lift_4_1 *)
Goal "#0 < N ==> \
\     Lift : (moving Int Req n Int {s. metric n s = N} Int \
\             {s. floor s ~: req s} Int {s. up s})   \
\            LeadsTo \
\              (moving Int Req n Int {s. metric n s < N})";
by (cut_facts_tac [moving_up] 1);
by (ensures_tac "move_up" 1);
by Safe_tac;
(*this step consolidates two formulae to the goal  metric n s' <= metric n s*)
by (etac (linorder_leI RS order_antisym RS sym) 1);
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (REPEAT_FIRST distinct_tac);
(** LEVEL 6 **)
by (ALLGOALS (asm_simp_tac (simpset() addsimps 
			    [zle_def] @ metric_simps @ zcompare_rls)));
qed "E_thm12a";



(*lem_lift_4_3 *)
Goal "#0 < N ==> \
\     Lift : (moving Int Req n Int {s. metric n s = N} Int \
\             {s. floor s ~: req s} - {s. up s})   \
\            LeadsTo (moving Int Req n Int {s. metric n s < N})";
by (cut_facts_tac [moving_down] 1);
by (ensures_tac "move_down" 1);
by Safe_tac;
(*this step consolidates two formulae to the goal  metric n s' <= metric n s*)
by (etac (linorder_leI RS order_antisym RS sym) 1);
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (REPEAT_FIRST distinct_tac);
(** LEVEL 6 **)
by (ALLGOALS (asm_simp_tac (simpset() addsimps metric_simps @ zcompare_rls)));
qed "E_thm12b";

(*lift_4*)
Goal "#0<N ==> Lift : (moving Int Req n Int {s. metric n s = N} Int \
\                           {s. floor s ~: req s}) LeadsTo     \
\                          (moving Int Req n Int {s. metric n s < N})";
by (rtac ([subset_imp_LeadsTo, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (etac E_thm12b 3);
by (etac E_thm12a 2);
by (Blast_tac 1);
qed "lift_4";


(** towards lift_5 **)

(*lem_lift_5_3*)
Goal "#0<N   \
\     ==> Lift : (closed Int Req n Int {s. metric n s = N} Int goingup) LeadsTo \
\                      (moving Int Req n Int {s. metric n s < N})";
by (cut_facts_tac [bounded] 1);
by (ensures_tac "req_up" 1);
by Auto_tac;
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (ALLGOALS (asm_simp_tac (simpset() addsimps metric_simps @ zcompare_rls)));
by (Blast_tac 1);
qed "E_thm16a";

(*lem_lift_5_1 has ~goingup instead of goingdown*)
Goal "#0<N ==>   \
\     Lift : (closed Int Req n Int {s. metric n s = N} Int goingdown) LeadsTo \
\                  (moving Int Req n Int {s. metric n s < N})";
by (cut_facts_tac [bounded] 1);
by (ensures_tac "req_down" 1);
by Auto_tac;
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (ALLGOALS (asm_simp_tac (simpset() addsimps metric_simps @ zcompare_rls)));
by (Blast_tac 1);
qed "E_thm16b";



(*lem_lift_5_0 proves an intersection involving ~goingup and goingup,
  i.e. the trivial disjunction, leading to an asymmetrical proof.*)
Goal "#0<N ==> Req n Int {s. metric n s = N} <= goingup Un goingdown";
by (asm_simp_tac (simpset() addsimps metric_simps) 1);
by (force_tac (claset() delrules [impCE] addEs [impCE], 
	       simpset() addsimps conj_comms) 1);
qed "E_thm16c";


(*lift_5*)
Goal "#0<N ==> Lift : (closed Int Req n Int {s. metric n s = N}) LeadsTo   \
\                          (moving Int Req n Int {s. metric n s < N})";
by (rtac ([subset_imp_LeadsTo, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (etac E_thm16b 3);
by (etac E_thm16a 2);
by (dtac E_thm16c 1);
by (Blast_tac 1);
qed "lift_5";


(** towards lift_3 **)

(*lemma used to prove lem_lift_3_1*)
Goal "[| metric n s = #0;  Min <= floor s;  floor s <= Max |] ==> floor s = n";
by (etac rev_mp 1);
(*force simplification of "metric..." while in conclusion part*)
by (asm_simp_tac (simpset() addsimps metric_simps) 1);
qed "metric_eq_0D";

AddDs [metric_eq_0D];


(*lem_lift_3_1*)
Goal "Lift : (moving Int Req n Int {s. metric n s = #0}) LeadsTo   \
\                  (stopped Int atFloor n)";
by (cut_facts_tac [bounded] 1);
by (ensures_tac "request_act" 1);
by Auto_tac;
qed "E_thm11";

(*lem_lift_3_5*)
Goal
  "Lift : (moving Int Req n Int {s. metric n s = N} Int {s. floor s : req s}) \
\ LeadsTo (stopped Int Req n Int {s. metric n s = N} Int {s. floor s : req s})";
by (ensures_tac "request_act" 1);
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "E_thm13";

(*lem_lift_3_6*)
Goal "#0 < N ==> \
\     Lift : \
\       (stopped Int Req n Int {s. metric n s = N} Int {s. floor s : req s}) \
\       LeadsTo (opened Int Req n Int {s. metric n s = N})";
by (ensures_tac "open_act" 1);
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "E_thm14";

(*lem_lift_3_7*)
Goal "Lift : (opened Int Req n Int {s. metric n s = N})  \
\            LeadsTo (closed Int Req n Int {s. metric n s = N})";
by (ensures_tac "close_act" 1);
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "E_thm15";


(** the final steps **)

Goal "#0 < N ==> \
\     Lift : \
\       (moving Int Req n Int {s. metric n s = N} Int {s. floor s : req s})   \
\       LeadsTo (moving Int Req n Int {s. metric n s < N})";
by (blast_tac (claset() addSIs [E_thm13, E_thm14, E_thm15, lift_5]
	                addIs [LeadsTo_Trans]) 1);
qed "lift_3_Req";



(*Now we observe that our integer metric is really a natural number*)
Goal "Lift : Always {s. #0 <= metric n s}";
by (rtac (bounded RS Always_weaken) 1);
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "Always_nonneg";

val R_thm11 = [Always_nonneg, E_thm11] MRS Always_LeadsTo_weaken;

Goal "Lift : (moving Int Req n) LeadsTo (stopped Int atFloor n)";
by (rtac (Always_nonneg RS integ_0_le_induct) 1);
by (case_tac "#0 < z" 1);
(*If z <= #0 then actually z = #0*)
by (fold_tac [zle_def]);
by (force_tac (claset() addIs [R_thm11, order_antisym], simpset()) 2);
by (rtac ([asm_rl, Un_upper1] MRS LeadsTo_weaken_R) 1);
by (rtac ([subset_imp_LeadsTo, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (rtac lift_3_Req 3);
by (rtac lift_4 2);
by Auto_tac;
qed "lift_3";


Goal "Lift : (Req n) LeadsTo (opened Int atFloor n)";
by (rtac LeadsTo_Trans 1);
by (rtac (E_thm04 RS LeadsTo_Un) 2);
by (rtac LeadsTo_Un_post 2);
by (rtac (E_thm01 RS LeadsTo_Trans_Un') 2);
by (rtac (lift_3 RS LeadsTo_Trans_Un') 2);
by (rtac (lift_2 RS LeadsTo_Trans_Un') 2);
by (rtac (E_thm03 RS LeadsTo_Trans_Un') 2);
by (rtac E_thm02 2);
by (rtac (open_move RS Always_LeadsToI) 1);
by (rtac (open_stop RS Always_LeadsToI) 1);
by (rtac subset_imp_LeadsTo 1);
by (Clarify_tac 1);
(*The case split is not essential but makes Blast_tac much faster.
  Must also be careful to prevent simplification from looping*)
by (case_tac "open x" 1);
by (ALLGOALS (rotate_tac ~1));
by (ALLGOALS Asm_full_simp_tac);
by (Blast_tac 1);
qed "lift_1";

Close_locale "floor";
