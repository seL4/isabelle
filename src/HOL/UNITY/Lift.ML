(*  Title:      HOL/UNITY/Lift
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Lift-Control Example
*)


(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";


(** Rules to move "metric n s" out of the assumptions, for case splitting **)
val mov_metric1 = read_instantiate_sg (sign_of thy) 
                 [("P", "?x < metric ?n ?s")] rev_mp;

val mov_metric2 = read_instantiate_sg (sign_of thy) 
                 [("P", "?x = metric ?n ?s")] rev_mp;

val mov_metric3 = read_instantiate_sg (sign_of thy) 
                 [("P", "~ (?x < metric ?n ?s)")] rev_mp;

(*The order in which they are applied seems to be critical...*)
val mov_metrics = [mov_metric2, mov_metric3, mov_metric1];


val Suc_lessD_contra = Suc_lessD COMP rev_contrapos;
val Suc_lessD_contra' = less_not_sym RS Suc_lessD_contra;

Addsimps [Lprg_def RS def_prg_simps];

Addsimps (map simp_of_act
	  [request_act_def, open_act_def, close_act_def,
	   req_up_def, req_down_def, move_up_def, move_down_def,
	   button_press_def]);

val always_defs = [above_def, below_def, queueing_def, 
		   goingup_def, goingdown_def, ready_def];

Addsimps (map simp_of_set always_defs);

Goalw [Lprg_def] "id : Acts Lprg";
by (Simp_tac 1);
qed "id_in_Acts";
AddIffs [id_in_Acts];


val LeadsTo_Un_post' = id_in_Acts RS LeadsTo_Un_post
and LeadsTo_Trans_Un' = rotate_prems 1 (id_in_Acts RS LeadsTo_Trans_Un);
(* [| LeadsTo Lprg B C; LeadsTo Lprg A B |] ==> LeadsTo Lprg (A Un B) C *)


val metric_simps =
    [metric_def, vimage_def, 
     not_less_less_Suc_eq, less_not_sym RS not_less_less_Suc_eq,
     Suc_lessD_contra, Suc_lessD_contra',
     less_not_refl2, less_not_refl3];


(*Hoping to be faster than
    asm_simp_tac (simpset() addsimps metric_simps
  but sometimes it's slower*)
val metric_simp_tac = 
    asm_simp_tac (simpset() addsimps [metric_def, vimage_def]) THEN'
    asm_simp_tac (simpset() addsimps metric_simps);


(*Simplification for records*)
Addsimps (thms"state.update_defs");

Addsimps [Suc_le_eq];

Addsimps [bounded_def, open_stop_def, open_move_def, stop_floor_def,
	  moving_up_def, moving_down_def];

AddIffs [Min_le_Max];


val nat_exhaust_le_pred = 
    read_instantiate_sg (sign_of thy) [("P", "?m <= ?y-1")] nat.exhaust;

val nat_exhaust_pred_le = 
    read_instantiate_sg (sign_of thy) [("P", "?y-1 <= ?m")] nat.exhaust;

Goal "m < n ==> m <= n-1";
by (asm_simp_tac (simpset() addsimps [gr_implies_gr0 RS le_pred_eq]) 1);
qed "less_imp_le_pred";

Goal "Invariant Lprg open_stop";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac 1);
qed "open_stop";

Goal "Invariant Lprg stop_floor";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac 1);
qed "stop_floor";

(*This one needs open_stop, which was proved above*)
Goal "Invariant Lprg open_move";
by (rtac InvariantI 1);
by (rtac (open_stop RS Invariant_ConstrainsI RS StableI) 2);
by (Force_tac 1);
by (constrains_tac 1);
qed "open_move";

Goal "Invariant Lprg moving_up";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac 1);
by (blast_tac (claset() addDs [le_imp_less_or_eq]) 1);
qed "moving_up";

Goal "Invariant Lprg moving_down";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac 1);
by Safe_tac;
by (dres_inst_tac [("m","f")] le_imp_less_or_eq 3);
by (auto_tac (claset(),
	      simpset() addsimps [gr_implies_gr0 RS le_pred_eq]));
qed "moving_down";

Goal "Invariant Lprg bounded";
by (rtac InvariantI 1);
by (rtac (Invariant_Int_rule [moving_up, moving_down] RS Invariant_StableI) 2);
by (Force_tac 1);
by (constrains_tac 1);
by Safe_tac;
by (TRYALL (resolve_tac [nat_exhaust_le_pred, nat_exhaust_pred_le]));
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq]));
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq, le_eq_less_or_eq]));
qed "bounded";



(*** Progress ***)


val abbrev_defs = [moving_def, stopped_def, 
		   opened_def, closed_def, atFloor_def, Req_def];

Addsimps (map simp_of_set abbrev_defs);


(** The HUG'93 paper mistakenly omits the Req n from these! **)

(** Lift_1 **)

Goal "LeadsTo Lprg (stopped Int atFloor n) (opened Int atFloor n)";
by (cut_facts_tac [stop_floor] 1);
by (ensures_tac "open_act" 1);
qed "E_thm01";  (*lem_lift_1_5*)

Goal "LeadsTo Lprg (Req n Int stopped - atFloor n) \
\                  (Req n Int opened - atFloor n)";
by (cut_facts_tac [stop_floor] 1);
by (ensures_tac "open_act" 1);
qed "E_thm02";  (*lem_lift_1_1*)

Goal "LeadsTo Lprg (Req n Int opened - atFloor n) \
\                  (Req n Int closed - (atFloor n - queueing))";
by (ensures_tac "close_act" 1);
qed "E_thm03";  (*lem_lift_1_2*)

Goal "LeadsTo Lprg (Req n Int closed Int (atFloor n - queueing)) \
\                  (opened Int atFloor n)";
by (ensures_tac "open_act" 1);
qed "E_thm04";  (*lem_lift_1_7*)


(** Lift 2.  Statements of thm05a and thm05b were wrong! **)

Open_locale "floor"; 

val Min_le_n = thm "Min_le_n";
val n_le_Max = thm "n_le_Max";

AddIffs [Min_le_n, n_le_Max];

val le_MinD = Min_le_n RS le_anti_sym;
val Max_leD = n_le_Max RSN (2,le_anti_sym);

AddSDs [le_MinD, leI RS le_MinD,
	Max_leD, leI RS Max_leD];

(*lem_lift_2_0 
  NOT an ensures property, but a mere inclusion;
  don't know why script lift_2.uni says ENSURES*)
Goal "LeadsTo Lprg (Req n Int closed - (atFloor n - queueing))   \
\                  ((closed Int goingup Int Req n)  Un \
\                   (closed Int goingdown Int Req n))";
by (rtac subset_imp_LeadsTo 1);
by (auto_tac (claset() addSEs [nat_neqE], simpset()));
qed "E_thm05c";

(*lift_2*)
Goal "LeadsTo Lprg (Req n Int closed - (atFloor n - queueing))   \
\                  (moving Int Req n)";
by (rtac ([E_thm05c, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (ensures_tac "req_down" 2);
by (ensures_tac "req_up" 1);
by Auto_tac;
qed "lift_2";


(** Towards lift_4 ***)

Goal "[| x ~: A;  y : A |] ==> x ~= y";
by (Blast_tac 1);
qed "not_mem_distinct";

fun distinct_tac i =
    dtac le_neq_implies_less i THEN
    eresolve_tac [not_mem_distinct, not_mem_distinct RS not_sym] i THEN
    assume_tac i;


(*lem_lift_4_1 *)
Goal "0 < N ==> \
\     LeadsTo Lprg \
\       (moving Int Req n Int (metric n -`` {N}) Int \
\         {s. floor s ~: req s} Int {s. up s})   \
\       (moving Int Req n Int (metric n -`` lessThan N))";
by (cut_facts_tac [moving_up] 1);
by (ensures_tac "move_up" 1);
by Safe_tac;
(*this step consolidates two formulae to the goal  metric n s' <= metric n s*)
by (etac (leI RS le_anti_sym RS sym) 1);
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (REPEAT_FIRST distinct_tac);
by (ALLGOALS metric_simp_tac);
by (auto_tac
    (claset() addEs [diff_Suc_less_diff RS less_not_refl3 RSN (2, rev_notE)]
	      addIs [diff_Suc_less_diff], 
     simpset()));
qed "E_thm12a";


(*This rule helps eliminate occurrences of  (floor s - 1) *)
val less_floor_imp = read_instantiate_sg (sign_of thy) 
                 [("n", "floor ?s")] less_eq_Suc_add RS exE;

(*lem_lift_4_3 *)
Goal "0 < N ==> \
\     LeadsTo Lprg \
\       (moving Int Req n Int (metric n -`` {N}) Int \
\        {s. floor s ~: req s} - {s. up s})   \
\       (moving Int Req n Int (metric n -`` lessThan N))";
by (cut_facts_tac [moving_down] 1);
by (ensures_tac "move_down" 1);
by Safe_tac;
by (ALLGOALS distinct_tac);
by (ALLGOALS (etac less_floor_imp THEN' Clarify_tac THEN' Asm_full_simp_tac));
(*this step consolidates two formulae to the goal  metric n s' <= metric n s*)
by (etac (leI RS le_anti_sym RS sym) 1);
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (ALLGOALS metric_simp_tac);
by (auto_tac
    (claset() addEs [diff_less_Suc_diff RS less_not_refl3 RSN (2, rev_notE)]
              addIs [diff_le_Suc_diff, diff_less_Suc_diff],
	      simpset() addsimps [trans_le_add1]));
qed "E_thm12b";


(*lift_4*)
Goal "0<N ==> LeadsTo Lprg (moving Int Req n Int (metric n -`` {N}) Int \
\                           {s. floor s ~: req s})     \
\                          (moving Int Req n Int (metric n -`` lessThan N))";
by (rtac ([subset_imp_LeadsTo, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (etac E_thm12b 4);
by (etac E_thm12a 3);
by (rtac id_in_Acts 2);
by (Blast_tac 1);
qed "lift_4";


(** towards lift_5 **)

(*lem_lift_5_3*)
Goal "0<N   \
\     ==> LeadsTo Lprg (closed Int Req n Int (metric n -`` {N}) Int goingup) \
\                      (moving Int Req n Int (metric n -`` lessThan N))";
by (cut_facts_tac [bounded] 1);
by (ensures_tac "req_up" 1);
by Auto_tac;
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (ALLGOALS (asm_simp_tac (simpset() addsimps metric_simps)));
     (*faster than metric_simp_tac or than using just metric_def*)
by (auto_tac (claset() addIs [diff_Suc_less_diff], 
	      simpset() addsimps [arith1, arith2]));
qed "E_thm16a";

    (*arith1 comes from
     1. !!s i.
	   [| n : req s; stop s; ~ open s; move s; floor s < i; i <= Max;
	      i : req s; ALL i. i < floor s --> Min <= i --> i ~: req s;
	      ~ n < Suc (floor s); ~ n < floor s; ~ up s; floor s < n;
	      Suc (floor s) < n; 0 < floor s - Min |]
	   ==> n - Suc (floor s) < floor s - Min + (n - Min)
    *)

    (*arith2 comes from
     2. !!s i.
	   [| Min <= floor s; ...
	      n : req s; stop s; ~ open s; move s; floor s < i; i <= Max;
	      i : req s; ALL i. i < floor s --> Min <= i --> i ~: req s;
	      ~ n < floor s; ~ up s; floor s < n; ~ n < Suc (floor s);
	      Suc (floor s) < n; Min < n |]
	   ==> n - Suc (floor s) < floor s - Min + (n - Min)
    *)

(*lem_lift_5_1 has ~goingup instead of goingdown*)
Goal "0<N ==>   \
\     LeadsTo Lprg (closed Int Req n Int (metric n -`` {N}) Int goingdown) \
\                  (moving Int Req n Int (metric n -`` lessThan N))";
by (cut_facts_tac [bounded] 1);
by (ensures_tac "req_down" 1);
by Auto_tac;
by (ALLGOALS (etac less_floor_imp THEN' Clarify_tac THEN' Asm_full_simp_tac));
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (ALLGOALS (asm_simp_tac (simpset() addsimps metric_simps)));
     (*faster and better than metric_simp_tac *)
by (auto_tac (claset() addIs [diff_Suc_less_diff, diff_less_Suc_diff], 
	      simpset() addsimps [trans_le_add1, arith3, arith4]));
qed "E_thm16b";

    (*arith3 comes from
     1. !!s i x.
	   [| floor s = Suc (i + x); Min <= Suc (i + x); stop s; i + x < Max;
	      ~ open s; n : req s; move s; Min <= i; i : req s;
	      ALL ia. ia <= Max --> Suc (i + x) < ia --> ia ~: req s;
	      ~ Suc (i + x) < n; ~ i + x < n; n ~= i + x; up s; n < i + x;
	      Suc (i + x) < Max |]
	   ==> i + x - n < Max - Suc (i + x) + (Max - n)
    *)

    (*arith4 comes from
     2. !!s i x.
	   [| floor s = Suc (i + x); Min <= Suc (i + x); stop s; i + x < Max;
	      ~ open s; n : req s; move s; Min <= i; i : req s;
	      ALL ia. ia <= Max --> Suc (i + x) < ia --> ia ~: req s;
	      ~ Suc (i + x) < n; ~ i + x < n; n ~= i + x; up s; n < i + x;
	      n < Max |]
	   ==> i + x - n < Max - Suc (i + x) + (Max - n)
    *)



(*lem_lift_5_0 proves an intersection involving ~goingup and goingup,
  i.e. the trivial disjunction, leading to an asymmetrical proof.*)
Goal "0<N ==> Req n Int (metric n -``{N}) <= goingup Un goingdown";
by (asm_simp_tac
    (simpset() addsimps (always_defs@abbrev_defs@[metric_def,vimage_def])) 1);
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "E_thm16c";


(*lift_5*)
Goal "0<N ==> LeadsTo Lprg (closed Int Req n Int (metric n -`` {N}))   \
\                          (moving Int Req n Int (metric n -`` lessThan N))";
by (rtac ([subset_imp_LeadsTo, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (etac E_thm16b 4);
by (etac E_thm16a 3);
by (rtac id_in_Acts 2);
by (dtac E_thm16c 1);
by (Blast_tac 1);
qed "lift_5";


(** towards lift_3 **)

(*lemma used to prove lem_lift_3_1*)
Goal "[| metric n s = 0;  Min <= floor s;  floor s <= Max |] ==> floor s = n";
by (etac rev_mp 1);
  (*MUCH faster than metric_simps*)
by (asm_simp_tac (simpset() addsimps [metric_def]) 1);
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "metric_eq_0D";

AddDs [metric_eq_0D];


(*lem_lift_3_1*)
Goal "LeadsTo Lprg (moving Int Req n Int (metric n -`` {0}))   \
\                  (stopped Int atFloor n)";
by (cut_facts_tac [bounded] 1);
by (ensures_tac "request_act" 1);
by Auto_tac;
qed "E_thm11";

(*lem_lift_3_5*)
Goal "LeadsTo Lprg \
\       (moving Int Req n Int (metric n -`` {N}) Int {s. floor s : req s})   \
\       (stopped Int Req n Int (metric n -`` {N}) Int {s. floor s : req s})";
by (ensures_tac "request_act" 1);
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "E_thm13";

(*lem_lift_3_6*)
Goal "0 < N ==> \
\     LeadsTo Lprg \
\       (stopped Int Req n Int (metric n -`` {N}) Int {s. floor s : req s}) \
\       (opened Int Req n Int (metric n -`` {N}))";
by (ensures_tac "open_act" 1);
by (REPEAT_FIRST (eresolve_tac mov_metrics));
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "E_thm14";

(*lem_lift_3_7*)
Goal "LeadsTo Lprg \
\       (opened Int Req n Int (metric n -`` {N}))  \
\       (closed Int Req n Int (metric n -`` {N}))";
by (ensures_tac "close_act" 1);
by (auto_tac (claset(), simpset() addsimps metric_simps));
qed "E_thm15";


(** the final steps **)

Goal "0 < N ==> \
\     LeadsTo Lprg \
\       (moving Int Req n Int (metric n -`` {N}) Int {s. floor s : req s})   \
\       (moving Int Req n Int (metric n -`` lessThan N))";
by (blast_tac (claset() addSIs [E_thm13, E_thm14, E_thm15, lift_5]
	                addIs [LeadsTo_Trans]) 1);
qed "lift_3_Req";


Goal "LeadsTo Lprg (moving Int Req n) (stopped Int atFloor n)";
by (rtac (allI RS LessThan_induct) 1);
by (exhaust_tac "m" 1);
by Auto_tac;
by (rtac E_thm11 1);
by (rtac ([asm_rl, Un_upper1] MRS LeadsTo_weaken_R) 1);
by (rtac ([subset_imp_LeadsTo, LeadsTo_Un] MRS LeadsTo_Trans) 1);
by (rtac lift_3_Req 4);
by (rtac lift_4 3);
by Auto_tac;
qed "lift_3";


Goal "LeadsTo Lprg (Req n) (opened Int atFloor n)";
by (rtac LeadsTo_Trans 1);
by (rtac (E_thm04 RS LeadsTo_Un) 2);
by (rtac LeadsTo_Un_post' 2);
by (rtac (E_thm01 RS LeadsTo_Trans_Un') 2);
by (rtac (lift_3 RS LeadsTo_Trans_Un') 2);
by (rtac (lift_2 RS LeadsTo_Trans_Un') 2);
by (rtac (E_thm03 RS LeadsTo_Trans_Un') 2);
by (rtac E_thm02 2);
by (rtac (open_move RS Invariant_LeadsToI) 1);
by (rtac (open_stop RS Invariant_LeadsToI) 1);
by (rtac subset_imp_LeadsTo 1);
by (rtac id_in_Acts 2);
by (Clarify_tac 1);
(*The case split is not essential but makes Blast_tac much faster.
  Must also be careful to prevent simplification from looping*)
by (case_tac "open x" 1);
by (ALLGOALS (rotate_tac ~1));
by (ALLGOALS Asm_full_simp_tac);
by (Blast_tac 1);
qed "lift_1";

Close_locale;
