(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator

Stop using o (composition)?

guarantees_PLam_I looks wrong: refers to lift_prog
*)

AddIs [impOfSubs subset_preserves_o];
Addsimps [funPair_o_distrib];

Delsimps [o_apply];

(*Eliminating the "o" operator gives associativity for free*)
val o_simp = simplify (simpset() addsimps [o_def]);

(*for tidying up expressions, but LOOPS with standard simpset.*)
Goal "(%u. f (u i)) = f o sub i";
by (asm_full_simp_tac (simpset() addsimps [o_def]) 1);
qed "sub_fold";

(*Splits up conjunctions & intersections: like CONJUNCTS in the HOL system*)
fun list_of_Int th = 
    (list_of_Int (th RS conjunct1) @ list_of_Int (th RS conjunct2))
    handle THM _ => (list_of_Int (th RS IntD1) @ list_of_Int (th RS IntD2))
    handle THM _ => (list_of_Int (th RS INT_D))
    handle THM _ => [th];

(*useful??*)
val lessThanBspec = lessThan_iff RS iffD2 RSN (2, bspec);
fun normalize th = 
     normalize (th RS spec
		handle THM _ => th RS lessThanBspec
		handle THM _ => th RS bspec
		handle THM _ => th RS (guarantees_INT_right_iff RS iffD1))
     handle THM _ => th;

(*Currently UNUSED, but possibly of interest*)
Goal "F : Increasing func ==> F : Stable {s. h pfixGe (func s)}";
by (asm_full_simp_tac
    (simpset() addsimps [Increasing_def, Stable_def, Constrains_def, 
			 constrains_def]) 1); 
by (blast_tac (claset() addIs [trans_Ge RS trans_genPrefix RS transD,
			       prefix_imp_pfixGe]) 1);
qed "Increasing_imp_Stable_pfixGe";

(*Currently UNUSED, but possibly of interest*)
Goal "ALL z. F : {s. z <= f s} LeadsTo {s. z <= g s} \
\     ==> F : {s. z pfixGe f s} LeadsTo {s. z pfixGe g s}";
by (rtac single_LeadsTo_I 1);
by (dres_inst_tac [("x", "f s")] spec 1);
by (etac LeadsTo_weaken 1);
by (blast_tac (claset() addIs [trans_Ge RS trans_genPrefix RS transD,
			       prefix_imp_pfixGe]) 2);
by (Blast_tac 1);
qed "LeadsTo_le_imp_pfixGe";


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
		  client_bounded_def, client_progress_def,
		  client_preserves_def] Client;

Goal "Client : UNIV guarantees[funPair rel ask] Increasing ask";
by (cut_facts_tac [Client_Spec] 1);
by (asm_full_simp_tac (simpset() addsimps [guarantees_Int_right]) 1);
qed "Client_Increasing_ask";

Goal "Client : UNIV guarantees[funPair rel ask] Increasing rel";
by (cut_facts_tac [Client_Spec] 1);
by (asm_full_simp_tac (simpset() addsimps [guarantees_Int_right]) 1);
qed "Client_Increasing_rel";

AddIffs [Client_Increasing_ask, Client_Increasing_rel];

Goal "Client : UNIV guarantees[ask] \
\              Always {s. ALL elt : set (ask s). elt <= NbT}";
by (cut_facts_tac [Client_Spec] 1);
by Auto_tac;
qed "Client_Bounded";

(*Client_Progress is cumbersome to state*)
val [_, _, Client_Progress, Client_preserves_giv] = list_of_Int Client_Spec;

AddIffs [Client_preserves_giv];	    


(*Network : <unfolded specification> *)
val Network_Spec =
    rewrite_rule [network_spec_def, network_ask_def, network_giv_def, 
		  network_rel_def, network_preserves_def] Network;

(*CANNOT use bind_thm: it puts the theorem into standard form, in effect
  exporting it from the locale*)
val [Network_Ask, Network_Giv, Network_Rel, 
     Network_preserves_allocGiv, Network_preserves_rel_ask] = 
    list_of_Int Network_Spec;

AddIffs  [Network_preserves_allocGiv];

Addsimps (Network_preserves_rel_ask |> simplify (simpset()) |> list_of_Int);


(*Alloc : <unfolded specification> *)
val Alloc_Spec =
    rewrite_rule [alloc_spec_def, alloc_increasing_def, alloc_safety_def, 
		  alloc_progress_def, alloc_preserves_def] Alloc;

val [Alloc_Increasing_0, Alloc_Safety, 
     Alloc_Progress, Alloc_preserves] = list_of_Int Alloc_Spec;

(*Strip off the INT in the guarantees postcondition*)
val Alloc_Increasing = normalize Alloc_Increasing_0;

fun alloc_export th = good_map_sysOfAlloc RS export th |> simplify (simpset());

fun client_export th = good_map_sysOfClient RS export th |> simplify (simpset());

AddIffs (Alloc_preserves |> simplify (simpset()) |> list_of_Int);

(** Components lemmas **)

(*Alternative is to say that System = Network Join F such that F preserves
  certain state variables*)
Goal "(extend sysOfClient (plam x: lessThan Nclients. Client)) Join \
\     (Network Join Alloc)  =  System";
by (simp_tac (simpset() addsimps System_def::Join_ac) 1);
qed "Client_component_System";

Goal "Network Join \
\     ((extend sysOfClient (plam x: lessThan Nclients. Client)) Join Alloc) \
\     = System";
by (simp_tac (simpset() addsimps System_def::Join_ac) 1);
qed "Network_component_System";

Goal "Alloc Join \
\      ((extend sysOfClient (plam x: lessThan Nclients. Client)) Join \
\       Network)  =  System";
by (simp_tac (simpset() addsimps System_def::Join_ac) 1);
qed "Alloc_component_System";

AddIffs [Client_component_System, Network_component_System, 
	 Alloc_component_System];

(** These preservation laws should be generated automatically **)

(*technical lemma*)
bind_thm ("extend_sysOfClient_preserves_o", 
	  inj_sysOfClient RS export inj_extend_preserves RS 
	  impOfSubs subset_preserves_o
	  |> simplify (simpset() addsimps [o_def]));

Goal "extend sysOfClient F : preserves allocGiv";
by (cut_inst_tac [("w", "allocGiv")] (extend_sysOfClient_preserves_o) 1);
by Auto_tac;
qed "extend_sysOfClient_preserves_allocGiv";

Goal "extend sysOfClient F : preserves allocAsk";
by (cut_inst_tac [("w", "allocAsk")] (extend_sysOfClient_preserves_o) 1);
by Auto_tac;
qed "extend_sysOfClient_preserves_allocAsk";

Goal "extend sysOfClient F : preserves allocRel";
by (cut_inst_tac [("w", "allocRel")] (extend_sysOfClient_preserves_o) 1);
by Auto_tac;
qed "extend_sysOfClient_preserves_allocRel";

AddIffs [extend_sysOfClient_preserves_allocGiv,
	 extend_sysOfClient_preserves_allocAsk,
	 extend_sysOfClient_preserves_allocRel];


(* (extend sysOfClient F : preserves (v o client)) = (F : preserves v) *)
bind_thm ("extend_sysOfClient_preserves_o_client",
	  client_export extend_preserves);
AddIffs [extend_sysOfClient_preserves_o_client];


Goalw [System_def]
     "i < Nclients ==> System : Increasing (sub i o allocGiv)";
by (rtac (Alloc_Increasing RS guarantees_Join_I1 RS guaranteesD) 1);
by Auto_tac;
qed "System_Increasing_allocGiv";


Goal "i < Nclients ==> System : Increasing (ask o sub i o client)";
by (rtac ([client_export extend_guar_Increasing,
	   Client_component_System] MRS component_guaranteesD) 1);
by (rtac (lift_prog_guar_Increasing RS guarantees_PLam_I) 1);
by Auto_tac;
qed "System_Increasing_ask";

Goal "i < Nclients ==> System : Increasing (rel o sub i o client)";
by (rtac ([client_export extend_guar_Increasing,
	   Client_component_System] MRS component_guaranteesD) 1);
by (rtac (lift_prog_guar_Increasing RS guarantees_PLam_I) 1);
(*gets Client_Increasing_rel from simpset*)
by Auto_tac;
qed "System_Increasing_rel";

(** Follows consequences.
    The "Always (INT ...) formulation expresses the general safety property
    and allows it to be combined using Always_Int_rule below. **)

Goal
  "i < Nclients ==> System : ((sub i o allocRel) Fols (rel o sub i o client))";
by (auto_tac (claset() addSIs [System_Increasing_rel, 
			       Network_Rel RS component_guaranteesD], 
	      simpset()));
qed "System_Follows_rel";

Goal
  "i < Nclients ==> System : ((sub i o allocAsk) Fols (ask o sub i o client))";
by (auto_tac (claset() addSIs [System_Increasing_ask, 
			       Network_Ask RS component_guaranteesD], 
	      simpset()));
qed "System_Follows_ask";

Goal
  "i < Nclients ==> System : (giv o sub i o client) Fols (sub i o allocGiv)";
by (auto_tac (claset() addSIs [Network_Giv RS component_guaranteesD, 
		 Alloc_Increasing RS component_guaranteesD], 
	      simpset()));
qed "System_Follows_allocGiv";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (giv o sub i o client) s <= (sub i o allocGiv) s})";
by (auto_tac (claset(), 
	      simpset() addsimps [Always_INT_distrib]));
by (etac (System_Follows_allocGiv RS Follows_Bounded) 1);
qed "Always_giv_le_allocGiv";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (sub i o allocAsk) s <= (ask o sub i o client) s})";
by (auto_tac (claset(), 
	      simpset() addsimps [Always_INT_distrib]));
by (etac (System_Follows_ask RS Follows_Bounded) 1);
qed "Always_allocAsk_le_ask";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (sub i o allocRel) s <= (rel o sub i o client) s})";
by (auto_tac (claset() addSIs [Follows_Bounded, System_Follows_rel], 
	      simpset() addsimps [Always_INT_distrib]));
qed "Always_allocRel_le_rel";


(*** Proof of the safety property (1) ***)

(*safety (1), step 1 is System_Increasing_rel*)

(*safety (1), step 2*)
Goal "i < Nclients ==> System : Increasing (sub i o allocRel)";
by (etac (System_Follows_rel RS Follows_Increasing1) 1);
qed "System_Increasing_allocRel";

(*safety (1), step 3*)
Goal "System : Always {s. sum (%i. (tokens o sub i o allocGiv) s) Nclients \
\                  <= NbT + sum (%i. (tokens o sub i o allocRel) s) Nclients}";
by (rtac ([Alloc_Safety, Alloc_component_System] MRS component_guaranteesD) 1);
(*preserves*)
by (asm_full_simp_tac (simpset() addsimps [o_def]) 2);
by (force_tac (claset(), simpset() addsimps [System_Increasing_allocRel]) 1);
qed "System_sum_bounded";

(** Follows reasoning **)

Goal "System : Always (INT i: lessThan Nclients. \
\                         {s. (tokens o giv o sub i o client) s \
\                          <= (tokens o sub i o allocGiv) s})";
by (rtac (Always_giv_le_allocGiv RS Always_weaken) 1);
by (auto_tac (claset() addIs [tokens_mono_prefix], 
	      simpset() addsimps [o_apply]));
qed "Always_tokens_giv_le_allocGiv";

Goal "System : Always (INT i: lessThan Nclients. \
\                         {s. (tokens o sub i o allocRel) s \
\                          <= (tokens o rel o sub i o client) s})";
by (rtac (Always_allocRel_le_rel RS Always_weaken) 1);
by (auto_tac (claset() addIs [tokens_mono_prefix], 
	      simpset() addsimps [o_apply]));
qed "Always_tokens_allocRel_le_rel";

(*safety (1), step 4 (final result!) *)
Goalw [system_safety_def] "System : system_safety";
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

(*Now there are proofs identical to System_Increasing_rel and
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
Goal "i < Nclients \
\     ==> System : Always \
\                   {s. ALL elt : set ((ask o sub i o client) s). elt <= NbT}";
by (rtac Always_weaken 1);
by (rtac ([guarantees_PLam_I RS client_export UNIV_guar_Always,
	   Client_component_System] MRS component_guaranteesD) 1);
by (rtac Client_i_Bounded 1);
by (auto_tac(claset(),
	 simpset() addsimps [o_apply, lift_export Collect_eq_extend_set RS sym,
			     client_export Collect_eq_extend_set RS sym]));
qed "System_Bounded_ask";

(*progress (2), step 4*)
Goal "System : Always {s. ALL i : lessThan Nclients. \
\                          ALL elt : set ((sub i o allocAsk) s). elt <= NbT}";
by (auto_tac (claset(), 
	      simpset() addsimps [Collect_ball_eq, Always_INT_distrib]));
by (rtac (Always_Int_rule [Always_allocAsk_le_ask, System_Bounded_ask] 
    RS Always_weaken) 1);
by (auto_tac (claset() addDs [set_mono], simpset()));
qed "System_Bounded_allocAsk";

(*progress (2), step 5 is System_Increasing_allocGiv*)

(*progress (2), step 6*)
Goal "i < Nclients ==> System : Increasing (giv o sub i o client)";
by (rtac Follows_Increasing1 1);
by (auto_tac (claset() addIs [Network_Giv RS component_guaranteesD,
			       System_Increasing_allocGiv], 
	      simpset()));
qed "System_Increasing_giv";

(** A LOT of work just to lift "Client_Progress" to the array **)

(*stability lemma for G*)
Goalw [preserves_def, o_def, stable_def, constrains_def, sub_def]
     "[| ALL z. G : stable      \
\                   (reachable (lift_prog i Client Join G) Int      \
\                    {s. z <= (giv o sub i) s});      \
\         G : preserves (rel o sub i);  G : preserves (ask o sub i) |]      \
\      ==> G : stable      \
\               (reachable (lift_prog i Client Join G) Int      \
\                {s. h <= (giv o sub i) s & h pfixGe (ask o sub i) s} -      \
\                {s. tokens h <= tokens ((rel o sub i) s)})";
by Auto_tac;
by (REPEAT (dres_inst_tac [("x", "rel (xa i)")] spec 2));
by (REPEAT (dres_inst_tac [("x", "ask (xa i)")] spec 1));
by (REPEAT_FIRST ball_tac);
by Auto_tac;
qed "G_stable_lift_prog";

Goal "lift_prog i Client \
\        : Increasing (giv o sub i)  \
\          guarantees[funPair rel ask o sub i] \
\          (INT h. {s. h <=  (giv o sub i) s & \
\                             h pfixGe (ask o sub i) s}  \
\                  Ensures {s. tokens h <= (tokens o rel o sub i) s})";
by (rtac (Client_Progress RS drop_prog_guarantees_raw) 1);
by (rtac (lift_export project_Increasing_I) 1);
by (full_simp_tac (simpset() addsimps [fold_o_sub, lift_prog_correct]) 1);
by (rtac INT_I 1);
by (simp_tac (simpset() addsimps [o_apply]) 1);
by (REPEAT (stac (lift_export Collect_eq_extend_set) 1));
by (rtac (lift_export project_Ensures_D) 1);
by (asm_full_simp_tac (simpset() addsimps [o_apply, lift_prog_correct, 
					   drop_prog_correct]) 1);
by (asm_full_simp_tac
    (simpset() addsimps [all_conj_distrib,
			 Increasing_def, Stable_eq_stable, Join_stable,
			 lift_set_correct RS sym,
			 Collect_eq_lift_set RS sym,
			 lift_prog_correct RS sym]) 1);
by (Clarify_tac 1);
by (dtac G_stable_lift_prog 1);
by (auto_tac (claset(), 
	      simpset() addsimps [o_apply]));
qed "Client_i_Progress";

Goal "i < Nclients \
\   ==> (plam x: lessThan Nclients. Client) \
\        : Increasing (giv o sub i)  \
\          guarantees[funPair rel ask o sub i] \
\          (INT h. {s. h <=  (giv o sub i) s & \
\                             h pfixGe (ask o sub i) s}  \
\                  Ensures {s. tokens h <= (tokens o rel o sub i) s})";
by (rtac guarantees_PLam_I 1);
by (rtac Client_i_Progress 1);
by Auto_tac;
val lemma2 = result();

(*another stability lemma for G*)
Goalw [preserves_def, o_def, stable_def, constrains_def, sub_def]
     "[| ALL z. G : stable      \
\                  (reachable (extend sysOfClient  \
\                              (plam x:lessThan Nclients. Client) Join G) Int \
\                    {s. z <= (giv o sub i o client) s});      \
\         G : preserves (rel o sub i o client);  \
\         G : preserves (ask o sub i o client) |]      \
\ ==> G : stable      \
\          (reachable (extend sysOfClient  \
\                      (plam x:lessThan Nclients. Client) Join G) Int \
\           {s. h <= (giv o sub i o client) s & \
\               h pfixGe (ask o sub i o client) s} - \
\           {s. tokens h <= tokens ((rel o sub i o client) s)})";
by Auto_tac;
by (REPEAT (dres_inst_tac [("x", "rel (client xa i)")] spec 2));
by (REPEAT (dres_inst_tac [("x", "ask (client xa i)")] spec 1));
by (REPEAT_FIRST ball_tac);
by Auto_tac;
qed "G_stable_sysOfClient";

Goal "i < Nclients \
\  ==> extend sysOfClient (plam x: lessThan Nclients. Client) \
\       : Increasing (giv o sub i o client)  \
\         guarantees[funPair rel ask o sub i o client] \
\         (INT h. {s. h <=  (giv o sub i o client) s & \
\                            h pfixGe (ask o sub i o client) s}  \
\                 Ensures {s. tokens h <= (tokens o rel o sub i o client) s})";
by (rtac (lemma2 RS client_export project_guarantees_raw) 1);
by (assume_tac 1);
by (rtac (client_export project_Increasing_I) 1);
by (Simp_tac 1);
by (rtac INT_I 1);
by (simp_tac (simpset() addsimps [o_apply]) 1);
by (REPEAT (stac (client_export Collect_eq_extend_set) 1));
by (rtac (client_export project_Ensures_D) 1);
by (asm_full_simp_tac (simpset() addsimps [o_apply]) 1);
by (asm_full_simp_tac
    (simpset() addsimps [all_conj_distrib,
			 Increasing_def, Stable_eq_stable, Join_stable,
			 Collect_eq_extend_set RS sym]) 1);
by (Clarify_tac 1);
by (dtac G_stable_sysOfClient 1);
by (auto_tac (claset(), 
	      simpset() addsimps [o_apply,
				client_export Collect_eq_extend_set RS sym]));
qed "sysOfClient_i_Progress";


(*progress (2), step 7*)
Goal
 "System : (INT i : lessThan Nclients. \
\           INT h. {s. h <= (giv o sub i o client) s & \
\                      h pfixGe (ask o sub i o client) s}  \
\               Ensures {s. tokens h <= (tokens o rel o sub i o client) s})";
by (rtac INT_I 1);
(*Couldn't have just used Auto_tac since the "INT h" must be kept*)
by (rtac ([sysOfClient_i_Progress,
	   Client_component_System] MRS component_guaranteesD) 1);
by (asm_full_simp_tac
    (simpset() addsimps [System_Increasing_giv]) 2);
by Auto_tac;
qed "System_Client_Progress";

val lemma =
    [System_Follows_ask RS Follows_Bounded,
     System_Follows_allocGiv RS Follows_LeadsTo] MRS Always_LeadsToD;

val lemma2 = [lemma, 
	      System_Follows_ask RS Follows_Increasing1 RS IncreasingD]
             MRS PSP_Stable;

Goal "i < Nclients \
\     ==> System : {s. h <= (sub i o allocGiv) s &      \
\                      h pfixGe (sub i o allocAsk) s}   \
\                  LeadsTo  \
\                  {s. h <= (giv o sub i o client) s &  \
\                      h pfixGe (ask o sub i o client) s}";
by (rtac single_LeadsTo_I 1);
by (res_inst_tac [("k6", "h"), ("x2", "(sub i o allocAsk) s")]
    (lemma2 RS LeadsTo_weaken) 1);
by Auto_tac;
by (blast_tac (claset() addIs [trans_Ge RS trans_genPrefix RS transD,
			       prefix_imp_pfixGe]) 1);
val lemma3 = result();


(*progress (2), step 8: Client i's "release" action is visible system-wide*)
Goal "i < Nclients  \
\     ==> System : {s. h <= (sub i o allocGiv) s & \
\                      h pfixGe (sub i o allocAsk) s}  \
\                  LeadsTo {s. tokens h <= (tokens o sub i o allocRel) s}";
by (rtac LeadsTo_Trans 1);
by (dtac (System_Follows_rel RS impOfSubs (mono_tokens RS mono_Follows_o) RS 
	  Follows_LeadsTo) 2);
by (asm_full_simp_tac (simpset() addsimps [o_assoc]) 2);
by (rtac LeadsTo_Trans 1);
by (cut_facts_tac [System_Client_Progress] 2);
by (blast_tac (claset() addIs [LeadsTo_Basis]) 2);
by (etac lemma3 1);
qed "System_Alloc_Client_Progress";



(*progress (2), step 9*)
Goal
 "System : (INT i : lessThan Nclients. \
\           INT h. {s. h <= (sub i o allocAsk) s}  \
\                  LeadsTo {s. h pfixLe (sub i o allocGiv) s})";
by (rtac ([Alloc_Progress, Alloc_component_System] 
	  MRS component_guaranteesD) 1);
(*preserves*)
by (asm_full_simp_tac (simpset() addsimps [o_def]) 2);
(*the guarantees precondition*)
by (auto_tac (claset(), 
	      simpset() addsimps [System_Increasing_allocRel,
				  System_Increasing_allocAsk]));
by (rtac System_Bounded_allocAsk 1);
by (etac System_Alloc_Client_Progress 1);
qed "System_Alloc_Progress";


(*progress (2), step 10 (final result!) *)
Goalw [system_progress_def] "System : system_progress";
by (Clarify_tac 1);
by (rtac LeadsTo_Trans 1);
by (etac (System_Follows_allocGiv RS Follows_LeadsTo_pfixLe) 2);
by (rtac LeadsTo_Trans 1);
by (cut_facts_tac [System_Alloc_Progress] 2);
by (Blast_tac 2);
by (etac (System_Follows_ask RS Follows_LeadsTo) 1);
qed "System_Progress";


(*Ultimate goal*)
Goalw [system_spec_def] "System : system_spec";
by (blast_tac (claset() addIs [System_safety, System_Progress]) 1);
qed "System_correct";

