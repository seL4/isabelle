(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator

Stop using o (composition)?

guarantees_PLam_I looks wrong: refers to lift_prog
*)

(*Eliminating the "o" operator gives associativity for free*)
val o_simp = simplify (simpset() addsimps [o_def]);

Goal "(ALL i: lessThan n. f i <= g i) --> sum f n <= sum g n";
by (induct_tac "n" 1);
by Auto_tac;
by (dres_inst_tac [("x","n")] bspec 1);
by Auto_tac;
by (arith_tac 1);
qed_spec_mp "sum_mono";

Goal "ALL xs. xs <= ys --> tokens xs <= tokens ys";
by (induct_tac "ys" 1);
by (auto_tac (claset(), simpset() addsimps [prefix_Cons]));
qed_spec_mp "tokens_mono_prefix";

Goalw [mono_def] "mono tokens";
by (blast_tac (claset() addIs [tokens_mono_prefix]) 1);
qed "mono_tokens";

(*Generalized version allowing different clients*)
Goal "[| Alloc : alloc_spec;  \
\        Client : (lessThan Nclients) funcset client_spec;  \
\        Network : network_spec |] \
\     ==> (extend sysOfAlloc Alloc) \
\         Join (extend sysOfClient (PLam (lessThan Nclients) Client)) \
\         Join Network : system_spec";

Goal "System : system_spec";


Goalw [sysOfAlloc_def] "inj sysOfAlloc";
by (rtac injI 1);
by (auto_tac (claset() addSWrapper record_split_wrapper, simpset()));
qed "inj_sysOfAlloc";

Goalw [sysOfAlloc_def] "surj sysOfAlloc";
by (res_inst_tac [("f", "%s. ((| allocGiv = allocGiv s,    \
\                                allocAsk = allocAsk s,    \
\                                allocRel = allocRel s |), \
\                             client s)")] surjI 1);
by (auto_tac (claset() addSWrapper record_split_wrapper, simpset()));
qed "surj_sysOfAlloc";

AddIffs [inj_sysOfAlloc, surj_sysOfAlloc];

Goalw [good_map_def] "good_map sysOfAlloc";
by Auto_tac;
qed "good_map_sysOfAlloc";
Addsimps [good_map_sysOfAlloc];

(*MUST BE AUTOMATED: even the statement of such results*)
Goal "!!s. inv sysOfAlloc s = \
\            ((| allocGiv = allocGiv s,   \
\                allocAsk = allocAsk s,   \
\                allocRel = allocRel s|), \
\             client s)";
by (rtac (inj_sysOfAlloc RS inv_f_eq) 1);
by (auto_tac (claset() addSWrapper record_split_wrapper, 
	      simpset() addsimps [sysOfAlloc_def]));
qed "inv_sysOfAlloc_eq";
Addsimps [inv_sysOfAlloc_eq];


(*SHOULD NOT BE NECESSARY????????????????
Goal "!!z. (| allocGiv = allocGiv z, allocAsk = allocAsk z, \
\             allocRel = allocRel z |) = z";
by (auto_tac (claset() addSWrapper record_split_wrapper, 
	      simpset()));
qed "allocState_eq";
Addsimps [allocState_eq];
????*)

(**SHOULD NOT BE NECESSARY: The various injections into the system
   state need to be treated symmetrically or done automatically*)
Goalw [sysOfClient_def] "inj sysOfClient";
by (rtac injI 1);
by (auto_tac (claset() addSDs [inj_sysOfAlloc RS injD]
		       addSWrapper record_split_wrapper, 
	      simpset()));
qed "inj_sysOfClient";

Goalw [sysOfClient_def] "surj sysOfClient";
by (cut_facts_tac [surj_sysOfAlloc] 1);
by (rewtac surj_def);
by Auto_tac;
by (Blast_tac 1);
qed "surj_sysOfClient";

AddIffs [inj_sysOfClient, surj_sysOfClient];

Goalw [good_map_def] "good_map sysOfClient";
by Auto_tac;
qed "good_map_sysOfClient";
Addsimps [good_map_sysOfClient];

(*MUST BE AUTOMATED: even the statement of such results*)
Goal "!!s. inv sysOfClient s = \
\            (client s, \
\             (| allocGiv = allocGiv s, \
\                allocAsk = allocAsk s, \
\                allocRel = allocRel s|) )";
by (rtac (inj_sysOfClient RS inv_f_eq) 1);
by (auto_tac (claset() addSWrapper record_split_wrapper, 
	      simpset() addsimps [sysOfAlloc_def, sysOfClient_def]));
qed "inv_sysOfClient_eq";
Addsimps [inv_sysOfClient_eq];


Open_locale "System";

val Alloc = thm "Alloc";
val Client = thm "Client";
val Network = thm "Network";
val System_def = thm "System_def";

AddIffs [finite_lessThan];

(*Client : <unfolded specification> *)
val Client_Spec =
    rewrite_rule [client_spec_def, client_increasing_def,
		  client_bounded_def, client_progress_def] Client;

Goal "Client : UNIV guarantees Increasing ask";
by (cut_facts_tac [Client_Spec] 1);
by (asm_full_simp_tac (simpset() addsimps [guarantees_Int_right]) 1);
qed "Client_Increasing_ask";

Goal "Client : UNIV guarantees Increasing rel";
by (cut_facts_tac [Client_Spec] 1);
by (asm_full_simp_tac (simpset() addsimps [guarantees_Int_right]) 1);
qed "Client_Increasing_rel";

AddIffs [Client_Increasing_ask, Client_Increasing_rel];

Goal "Client : UNIV guarantees Always {s. ALL elt : set (ask s). elt <= NbT}";
by (cut_facts_tac [Client_Spec] 1);
by Auto_tac;
qed "Client_Bounded";

(*Client_Progress is cumbersome to state*)
val Client_Progress = Client_Spec RS IntD2;


(*Network : <unfolded specification> *)
val Network_Spec =
    rewrite_rule [network_spec_def, network_ask_def,
		  network_giv_def, network_rel_def] Network;

(*CANNOT use bind_thm: it puts the theorem into standard form, in effect
  exporting it from the locale*)
val Network_Ask = Network_Spec RS IntD1 RS IntD1 RS INT_D;
val Network_Giv = Network_Spec RS IntD1 RS IntD2 RS INT_D;
val Network_Rel = Network_Spec RS IntD2 RS INT_D;


(*Alloc : <unfolded specification> *)
val Alloc_Spec =
    rewrite_rule [alloc_spec_def, alloc_increasing_def,
		  alloc_safety_def, alloc_progress_def] Alloc;

Goal "i < Nclients ==> Alloc : UNIV guarantees Increasing (sub i o allocGiv)";
by (cut_facts_tac [Alloc_Spec] 1);
by (asm_full_simp_tac (simpset() addsimps [guarantees_INT_right]) 1);
qed "Alloc_Increasing";

val Alloc_Safety = Alloc_Spec RS IntD1 RS IntD2;
val Alloc_Progress = (Alloc_Spec RS IntD2
                      |> simplify (simpset() addsimps [guarantees_INT_right]))
                     RS bspec RS spec;
		     


(*Not sure what to say about the other components because they involve
  extend*)
Goalw [System_def] "Network <= System";
by (blast_tac (claset() addIs [componentI]) 1);
qed "Network_component_System";

Goalw [System_def] "(extend sysOfAlloc Alloc) <= System";
by (blast_tac (claset() addIs [componentI]) 1);
qed "Alloc_component_System";

AddIffs [Network_component_System, Alloc_component_System];


fun alloc_export th = good_map_sysOfAlloc RS export th |> simplify (simpset());

fun client_export th = good_map_sysOfClient RS export th |> simplify (simpset());

(*NEED AUTOMATIC PROPAGATION of Alloc_Increasing*)
Goal "i < Nclients \
\ ==> extend sysOfAlloc Alloc : UNIV guarantees Increasing (sub i o allocGiv)";
by (dtac (Alloc_Increasing RS alloc_export extend_guar_Increasing) 1);
by (auto_tac (claset(), simpset() addsimps [o_def]));
qed "extend_Alloc_Increasing_allocGiv";

Goalw [System_def]
     "i < Nclients ==> System : Increasing (sub i o allocGiv)";
by (rtac (extend_Alloc_Increasing_allocGiv RS 
	  guarantees_Join_I1 RS guaranteesD) 1);
by Auto_tac;
qed "System_Increasing_allocGiv";



Goalw [System_def]
     "i < Nclients ==> System : Increasing (ask o sub i o client)";
by (rtac (client_export extend_guar_Increasing RS guarantees_Join_I2 
	  RS guaranteesD) 1);
by (rtac (lift_prog_guar_Increasing RS guarantees_PLam_I) 1);
by Auto_tac;
qed "System_Increasing_ask";

Goalw [System_def]
     "i < Nclients ==> System : Increasing (rel o sub i o client)";
by (rtac (client_export extend_guar_Increasing RS guarantees_Join_I2 
	  RS guaranteesD) 1);
by (rtac (lift_prog_guar_Increasing RS guarantees_PLam_I) 1);
(*gets Client_Increasing_rel from simpset*)
by Auto_tac;
qed "System_Increasing_rel";


(** Follows consequences.
    The "Always (INT ...) formulation expresses the general safety property
    and allows it to be combined using Always_Int_rule below. **)

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (giv o sub i o client) s <= (sub i o allocGiv) s})";
by (auto_tac (claset(), 
	      simpset() delsimps [o_apply]
	                addsimps [Always_INT_distrib, Follows_Bounded,
				  Network_Giv RS component_guaranteesD,
	     extend_Alloc_Increasing_allocGiv RS component_guaranteesD]));
qed "Always_giv_le_allocGiv";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (sub i o allocAsk) s <= (ask o sub i o client) s})";
by (auto_tac (claset(), 
	      simpset() delsimps [o_apply]
	      addsimps [Always_INT_distrib, Follows_Bounded,
	     [Network_Ask, System_Increasing_ask] MRS component_guaranteesD]));
qed "Always_allocAsk_le_ask";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (sub i o allocRel) s <= (rel o sub i o client) s})";
by (auto_tac (claset(), 
	      simpset() delsimps [o_apply]
	                addsimps [Always_INT_distrib, Follows_Bounded,
	     [Network_Rel, System_Increasing_rel] MRS component_guaranteesD]));
qed "Always_allocRel_le_rel";


(*** Proof of the safety property (1) ***)

(*safety (1), step 1 is System_Increasing_rel*)

(*safety (1), step 2*)
Goal "i < Nclients ==> System : Increasing (sub i o allocRel)";
by (rtac Follows_Increasing1 1);
by (blast_tac (claset() addIs [Network_Rel RS component_guaranteesD,
			       System_Increasing_rel]) 1);
qed "System_Increasing_allocRel";



(*safety (1), step 3*)
Goal "System : Always {s. sum (%i. (tokens o sub i o allocGiv) s) Nclients \
\                  <= NbT + sum (%i. (tokens o sub i o allocRel) s) Nclients}";
by (res_inst_tac 
    [("X", "(INT i : lessThan Nclients. Increasing (sub i o allocRel))")] 
    component_guaranteesD 1);
by (rtac Alloc_component_System 3);
by (force_tac (claset(), simpset() addsimps [System_Increasing_allocRel]) 2);
by (rtac (Alloc_Safety RS project_guarantees) 1);
(*1: Increasing precondition*)
by (rtac (alloc_export projecting_Increasing RS projecting_weaken RS 
	  projecting_INT) 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [o_def]) 1);
(*2: Always postcondition*)
by (rtac ((alloc_export extending_Always RS extending_weaken)) 1);
by Auto_tac;
by (asm_full_simp_tac
     (simpset() addsimps [alloc_export Collect_eq_extend_set RS sym]) 1);
qed "System_sum_bounded";

(** Follows reasoning **)

Goal "System : Always (INT i: lessThan Nclients. \
\                         {s. (tokens o giv o sub i o client) s \
\                          <= (tokens o sub i o allocGiv) s})";
by (rtac (Always_giv_le_allocGiv RS Always_weaken) 1);
by (auto_tac (claset() addIs [tokens_mono_prefix], simpset()));
qed "Always_tokens_giv_le_allocGiv";

Goal "System : Always (INT i: lessThan Nclients. \
\                         {s. (tokens o sub i o allocRel) s \
\                          <= (tokens o rel o sub i o client) s})";
by (rtac (Always_allocRel_le_rel RS Always_weaken) 1);
by (auto_tac (claset() addIs [tokens_mono_prefix], simpset()));
qed "Always_tokens_allocRel_le_rel";

(*safety (1), step 4 (final result!) *)
Goal "System : Always {s. sum (%i. (tokens o giv o sub i o client)s) Nclients \
\              <= NbT + sum (%i. (tokens o rel o sub i o client)s) Nclients}";
by (rtac (Always_Int_rule [System_sum_bounded, Always_tokens_giv_le_allocGiv, 
			   Always_tokens_allocRel_le_rel] RS Always_weaken) 1);
by Auto_tac;
by (rtac (sum_mono RS order_trans) 1);
by (dtac order_trans 2);
by (rtac ([order_refl, sum_mono] MRS add_le_mono) 2);
by (assume_tac 3);
by Auto_tac;
qed "System_safety";



(*** Proof of the progress property (2) ***)

(*we begin with proofs identical to System_Increasing_rel and
  System_Increasing_allocRel: tactics needed!*)

(*progress (2), step 1 is System_Increasing_ask and System_Increasing_rel*)

(*progress (2), step 2; see also System_Increasing_allocRel*)
Goal "i < Nclients ==> System : Increasing (sub i o allocAsk)";
by (rtac Follows_Increasing1 1);
by (blast_tac (claset() addIs [Network_Ask RS component_guaranteesD,
			       System_Increasing_ask]) 1);
qed "System_Increasing_allocAsk";

val Client_i_Bounded =
    [Client_Bounded, projecting_UNIV, lift_export extending_Always] 
    MRS drop_prog_guarantees;

val UNIV_guar_Always =
    [asm_rl, projecting_UNIV, extending_Always] 
    MRS project_guarantees;


(*progress (2), step 3*)
(*All this trouble just to lift "Client_Bounded" through two extend ops*)
Goalw [System_def]
     "i < Nclients \
\   ==> System : Always \
\                 {s. ALL elt : set ((ask o sub i o client) s). elt <= NbT}";
by (rtac (guarantees_PLam_I RS client_export UNIV_guar_Always RS
	  guarantees_Join_I2 RS guaranteesD RS Always_weaken) 1);
by (rtac Client_i_Bounded 1);
by (auto_tac(claset(),
	 simpset() addsimps [lift_export Collect_eq_extend_set RS sym,
			     client_export Collect_eq_extend_set RS sym]));
qed "System_Bounded_ask";

(*progress (2), step 4*)
Goal "System : Always {s. ALL i : lessThan Nclients. \
\                          ALL elt : set ((sub i o allocAsk) s). elt <= NbT}";
by (auto_tac (claset(), 
	      simpset() addsimps [Collect_ball_eq, Always_INT_distrib]));
by (rtac (Always_Int_rule [Always_allocAsk_le_ask, System_Bounded_ask] 
    RS Always_weaken) 1);
by (auto_tac(claset() addDs [set_mono], simpset()));
qed "System_Bounded_allocAsk";

(*progress (2), step 5*)

Goal "i < Nclients ==> System : Increasing (giv o sub i o client)";
by (rtac Follows_Increasing1 1);
by (blast_tac (claset() addIs [Network_Giv RS component_guaranteesD,
			       System_Increasing_allocGiv]) 1);
qed "System_Increasing_giv";

(*progress (2), step 6*)

(*A LOT of work just to lift "Client_Progress" to the array*)
Goal "lift_prog i Client \
\  : Increasing (giv o sub i) Int ((%z. z i) LocalTo (lift_prog i Client)) \
\    guarantees \
\    (INT h. {s. h <=  (giv o sub i) s & \
\                       h pfixGe (ask o sub i) s}  \
\            LeadsTo {s. tokens h <= (tokens o rel o sub i) s})";
by (rtac (Client_Progress RS drop_prog_guarantees) 1);
by (rtac (lift_export extending_LeadsTo RS extending_weaken RS extending_INT) 2);
by (rtac subset_refl 4);
by (simp_tac (simpset()addsimps [lift_export Collect_eq_extend_set RS sym]) 3);
by (force_tac (claset(), simpset() addsimps [lift_prog_correct]) 2);
by (rtac (lift_export projecting_Increasing RS projecting_weaken) 1);
by (auto_tac (claset(), simpset() addsimps [o_def]));
qed "Client_i_Progress";

xxxxxxxxxxxxxxxx;

Goalw [System_def]
     "i < Nclients \
\ ==> System : (INT h. {s. h <=  (giv o sub i o client) s & \
\                       h pfixGe (ask o sub i o client) s}  \
\            LeadsTo {s. tokens h <= (tokens o rel o sub i o client) s})";
by (rtac (guarantees_Join_I2 RS guaranteesD) 1);
by (rtac (guarantees_PLam_I RS project_guarantees) 1);
by (rtac Client_i_Progress  1);
by (Force_tac 1);
by (rtac (client_export extending_LeadsTo RS extending_weaken RS extending_INT) 2);
by (rtac subset_refl 4);
by (simp_tac (simpset()addsimps [client_export Collect_eq_extend_set RS sym]) 3);
by (rtac projecting_Int 1);
by (rtac (client_export projecting_Increasing) 1);
by (rtac (client_export projecting_localTo) 1);

by (simp_tac (simpset()addsimps [lift_prog_correct]) 1);

by (rtac (client_export ) 1);

Client_Progress;
