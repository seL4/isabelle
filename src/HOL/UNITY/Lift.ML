(*  Title:      HOL/UNITY/Lift
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Lift-Control Example
*)

(*ARITH.ML??*)
Goal "m-1 < n ==> m <= n";
by (exhaust_tac "m" 1);
by (auto_tac (claset(), simpset() addsimps [Suc_le_eq]));
qed "pred_less_imp_le";


val always_defs = [above_def, below_def, queueing_def, 
		   goingup_def, goingdown_def, ready_def];

val cmd_defs = [Lprg_def, 
		request_act_def, open_act_def, close_act_def,
		req_up_act_def, req_down_act_def, move_up_def, move_down_def];

Goalw [Lprg_def] "id : Acts Lprg";
by (Simp_tac 1);
qed "id_in_Acts";
AddIffs [id_in_Acts];


(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

(*Simplification for records*)
Addsimps (thms"state.update_defs");

Addsimps [Suc_le_eq];

Addsimps [bounded_def, open_stop_def, open_move_def, stop_floor_def,
	  moving_up_def, moving_down_def];

AddIffs [min_le_max];


val nat_exhaust_le_pred = 
    read_instantiate_sg (sign_of thy) [("P", "?m <= ?y-1")] nat.exhaust;

val nat_exhaust_pred_le = 
    read_instantiate_sg (sign_of thy) [("P", "?y-1 <= ?m")] nat.exhaust;

Goal "0 < n ==> (m <= n-1) = (m<n)";
by (exhaust_tac "n" 1);
by Auto_tac;
qed "le_pred_eq";

Goal "0 < n ==> (m-1 < n) = (m<=n)";
by (exhaust_tac "m" 1);
by (auto_tac (claset(), simpset() addsimps [Suc_le_eq]));
qed "less_pred_eq";

Goal "m < n ==> m <= n-1";
by (asm_simp_tac (simpset() addsimps [gr_implies_gr0 RS le_pred_eq]) 1);
qed "less_imp_le_pred";


Goalw [Lprg_def] "Invariant Lprg open_stop";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "open_stop";

Goalw [Lprg_def] "Invariant Lprg stop_floor";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "stop_floor";

(*This one needs open_stop, which was proved above*)
Goal "Invariant Lprg open_move";
by (rtac InvariantI 1);
br (open_stop RS Invariant_ConstrainsI RS StableI) 2;
bw Lprg_def;
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
qed "open_move";

Goalw [Lprg_def] "Invariant Lprg moving_up";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (blast_tac (claset() addDs [le_imp_less_or_eq]) 1);
qed "moving_up";

Goalw [Lprg_def] "Invariant Lprg moving_down";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (dres_inst_tac [("m","f")] le_imp_less_or_eq 3);
by (auto_tac (claset(),
	      simpset() addsimps [gr_implies_gr0 RS le_pred_eq]));
qed "moving_down";


Goal "Invariant Lprg bounded";
by (rtac InvariantI 1);
br (Invariant_Int_rule [moving_up, moving_down] RS Invariant_StableI) 2;
bw Lprg_def;
by (Force_tac 1);
by (constrains_tac (cmd_defs@always_defs) 1);
by (TRYALL (resolve_tac [nat_exhaust_le_pred, nat_exhaust_pred_le]));
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq]));
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq, le_eq_less_or_eq]));
qed "bounded";



(*** Progress ***)


val abbrev_defs = [moving_def, stopped_def, 
		   opened_def, closed_def, atFloor_def, Req_def];

val defs = cmd_defs@always_defs@abbrev_defs;


(** The HUG'93 paper mistakenly omits the Req n from these! **)

Goal "LeadsTo Lprg (stopped Int atFloor n) (opened Int atFloor n)";
by (cut_facts_tac [stop_floor] 1);
by (ensures_tac defs "open_act" 1);
qed "E_thm01";

Goal "LeadsTo Lprg (Req n Int stopped - atFloor n) \
\                  (Req n Int opened - atFloor n)";
by (cut_facts_tac [stop_floor] 1);
by (ensures_tac defs "open_act" 1);
qed "E_thm02";

Goal "LeadsTo Lprg (Req n Int opened - atFloor n) \
\                  (Req n Int closed - (atFloor n - queueing))";
by (ensures_tac defs "close_act" 1);
qed "E_thm03";

Goal "LeadsTo Lprg (Req n Int closed Int (atFloor n - queueing)) \
\                  (opened Int atFloor n)";
by (ensures_tac defs "open_act" 1);
qed "E_thm04";


(** Theorem 5.  Statements of thm05a and thm05b were wrong! **)

Open_locale "floor"; 

AddIffs [thm "min_le_n", thm "n_le_max"];

(*NOT an ensures property, but a mere inclusion*)
Goal "LeadsTo Lprg (Req n Int closed - (atFloor n - queueing))   \
\                  ((closed Int goingup Int Req n)  Un \
\                   (closed Int goingdown Int Req n))";
br subset_imp_LeadsTo 1;
by (auto_tac (claset() addSEs [nat_neqE], simpset() addsimps defs));
qed "E_thm05c";

Goal "LeadsTo Lprg (Req n Int closed - (atFloor n - queueing))   \
\                  (moving Int Req n)";
br ([E_thm05c, LeadsTo_Un] MRS LeadsTo_Trans) 1;
by (ensures_tac defs "req_down_act" 2);
by (ensures_tac defs "req_up_act" 1);
qed "lift_2";



val LeadsTo_Un_post' = id_in_Acts RS LeadsTo_Un_post
and LeadsTo_Trans_Un' = rotate_prems 1 (id_in_Acts RS LeadsTo_Trans_Un);
(* [| LeadsTo Lprg B C; LeadsTo Lprg A B |] ==> LeadsTo Lprg (A Un B) C *)

val [lift_3] = 
goal thy "LeadsTo Lprg (moving Int Req n) (stopped Int atFloor n) ==> LeadsTo Lprg (Req n) (opened Int atFloor n)";
br LeadsTo_Trans 1;
br (E_thm04 RS LeadsTo_Un) 2;
br LeadsTo_Un_post' 2;
br (E_thm01 RS LeadsTo_Trans_Un') 2;
br (lift_3 RS LeadsTo_Trans_Un') 2;
br (lift_2 RS LeadsTo_Trans_Un') 2;
br (E_thm03 RS LeadsTo_Trans_Un') 2;
br E_thm02 2;
br (open_move RS Invariant_LeadsToI) 1;
br (open_stop RS Invariant_LeadsToI) 1;
br subset_imp_LeadsTo 1;
by (rtac id_in_Acts 2);
bws defs;
by (Clarify_tac 1);
	(*stops simplification from looping*)
by (asm_full_simp_tac (simpset() setsubgoaler simp_tac) 1);
by (REPEAT (Safe_step_tac 1 ORELSE Blast_tac 1));
qed "lift_1";


val rev_mp' = read_instantiate_sg (sign_of thy) 
                 [("P", "0 < metric ?n ?s")] rev_mp;


Goal "0<N ==> LeadsTo Lprg (closed Int Req n Int {s. metric n s = N} Int goingup) \
\                  (moving Int Req n Int {s. metric n s < N})";
by (ensures_tac defs "req_up_act" 1);
by (REPEAT_FIRST (etac rev_mp'));
by (auto_tac (claset() addIs [diff_Suc_less_diff], 
	      simpset() addsimps [arith1, arith2, metric_def]));
qed "E_thm16a";


(*arith1 comes from
 1. !!s i.
       [| n : req s; stop s; ~ open s; move s; floor s < i; i <= max;
          i : req s; ALL i. i < floor s --> min <= i --> i ~: req s;
          ~ n < Suc (floor s); ~ n < floor s; ~ up s; floor s < n;
          Suc (floor s) < n; 0 < floor s - min |]
       ==> n - Suc (floor s) < floor s - min + (n - min)
*)

(*arith2 comes from
 2. !!s i.
       [| n : req s; stop s; ~ open s; move s; floor s < i; i <= max;
          i : req s; ALL i. i < floor s --> min <= i --> i ~: req s;
          ~ n < floor s; ~ up s; floor s < n; ~ n < Suc (floor s);
          Suc (floor s) < n; min < n |]
       ==> n - Suc (floor s) < floor s - min + (n - min)
*)


xxxxxxxxxxxxxxxx;

Goal "j<=i ==> i - j < Suc i - j";
by (REPEAT (etac rev_mp 1));
by (res_inst_tac [("m","i"),("n","j")] diff_induct 1);
by Auto_tac;
qed "diff_less_Suc_diff";


Goal "0<N ==> LeadsTo Lprg (closed Int Req n Int {s. metric n s = N} Int goingdown) \
\                  (moving Int Req n Int {s. metric n s < N})";
by (ensures_tac defs "req_down_act" 1);
be rev_mp 2;
be rev_mp 1;
by (dtac less_eq_Suc_add 2);
by (Clarify_tac 2);
by (Asm_full_simp_tac 2);
by (dtac less_eq_Suc_add 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);

by (asm_simp_tac (simpset() addsimps [metric_def]) 1);
by (REPEAT (Safe_step_tac 1));
by(blast_tac (claset() addEs [less_asym, less_irrefl, less_SucE]) 1);
by (REPEAT (Safe_step_tac 1));
by(blast_tac (claset() addEs [less_asym, less_irrefl, less_SucE]) 1);
by (REPEAT (Safe_step_tac 1));







Goal "[| i + k < n;  Suc (i + k) < n |] ==> i + k - m < Suc (i + k) - m";
by (REPEAT (etac rev_mp 1));
by (arith_oracle_tac 1);


by (asm_simp_tac (simpset() addsimps [metric_def]) 2);
by (REPEAT (Safe_step_tac 2));
by(Blast_tac 2);
by(Blast_tac 2);
by(Blast_tac 2);
by (REPEAT (Safe_step_tac 2));
by(Blast_tac 2);
by(blast_tac (claset() addEs [less_asym]) 2);
by (REPEAT (Safe_step_tac 2));
by(blast_tac (claset() addEs [less_asym]) 2);
by(blast_tac (claset() addEs [less_asym, less_irrefl, less_SucE]) 2);
by (REPEAT (Safe_step_tac 2));
by(blast_tac (claset() addEs [less_asym, less_irrefl, less_SucE]) 2);


by (asm_simp_tac (simpset() addsimps [less_not_sym] setsubgoaler simp_tac) 1);


by (REPEAT (Safe_step_tac 2));
by (REPEAT (Safe_step_tac 2 THEN Blast_tac 2));

by (auto_tac (claset() addIs [diff_Suc_less_diff], 
	      simpset() addsimps [metric_def]));
qed "E_thm16b";



Goal "[|  m <= i; i < fl; ~ fl < n; fl - 1 < n |] ==> ~ n < fl - 1 --> n < fl --> fl - 1 - m + (n - m) < fl - n";


not_less_iff_le

Goal "[|  ~ m < n; m - 1 < n |] ==> n = m";
by (cut_facts_tac [less_linear] 1);
by (blast_tac (claset() addSEs [less_irrefl]) 1);
 by (REPEAT (etac rev_mp 1));
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (arith_oracle_tac 1);







(**in the postscript file, but too horrible**)

Goal "0<N ==> LeadsTo Lprg (closed Int Req n Int {s. metric n s = N} - goingup) \
\                  (moving Int Req n Int {s. metric n s < N})";
by (ensures_tac defs "req_down_act" 1);
by (REPEAT_FIRST (etac rev_mp'));

by (dtac less_eq_Suc_add 2);
by (Clarify_tac 2);
by (Asm_full_simp_tac 2);
by (asm_simp_tac (simpset() addsimps [metric_def]) 2);


yyyyyyyyyyyyyyyy;

by (REPEAT (Safe_step_tac 2));
by(blast_tac (claset() addEs [less_asym]) 2);
by (REPEAT (Safe_step_tac 2));
by(Blast_tac 2);
by(Blast_tac 2);
by (REPEAT (Safe_step_tac 2));
by(Blast_tac 2);
by(Blast_tac 2);
by (REPEAT (Safe_step_tac 2));
by(blast_tac (claset() addEs [less_asym]) 2);
by(blast_tac (claset() addDs [le_anti_sym]
		       addSDs [leI, pred_less_imp_le]) 2);
by(blast_tac (claset() addEs [less_asym, less_irrefl, less_SucE]) 2);


by(Blast_tac 3);







Goal "m < fl ==> n - Suc (fl) < fl - m + (n - m)";
fe rev_mp;
by (res_inst_tac [("m","MIN"),("n","fl")] diff_induct 1);
		by (ALLGOALS Asm_simp_tac);

by (arith_oracle_tac 1);


Goal "[| Suc (fl) < n; m < n |] ==> n - Suc (fl) < fl - m + (n - m)";
by (REPEAT (etac rev_mp 1));
by (arith_oracle_tac 1);







infixr TRANS;
fun th1 TRANS th2 = [th1, th2] MRS LeadsTo_Trans_Un';

E_thm02 TRANS E_thm03 TRANS (lift_2 RS LeadsTo_Un_post');



[E_thm02, 
 E_thm03 RS LeadsTo_Un_post'] MRS LeadsTo_Trans_Un';


val sact = "open_act";
val sact = "move_up_act";

val (main_def::CDEFS) = defs;

by (REPEAT (Invariant_Int_tac 1));

by (etac Invariant_LeadsTo_Basis 1 
	          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
		  REPEAT (ares_tac [LeadsTo_Basis, ensuresI] 1));

by (res_inst_tac [("act", sact)] transient_mem 2);
by (simp_tac (simpset() addsimps (Domain_partial_func::CDEFS)) 3);
by (force_tac (claset(), simpset() addsimps [main_def]) 2);
by (constrains_tac (main_def::CDEFS) 1);
by (rewrite_goals_tac CDEFS);
by (ALLGOALS Clarify_tac);
by (Auto_tac);

by(Force_tac 2);



yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy;



Goalw [transient_def]
     "transient acts A = (EX act:acts. A <= act^-1 ^^ (Compl A))";
by Safe_tac;
by (ALLGOALS (rtac bexI));
by (TRYALL assume_tac);
by (Blast_tac 1);
br conjI 1;
by (Blast_tac 1);
(*remains to show  
  [| act : acts; A <= act^-1 ^^ Compl A |] ==> act ^^ A <= Compl A
*)

