(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator
*)

AddIs [impOfSubs subset_preserves_o];
Addsimps [funPair_o_distrib];
Addsimps [Always_INT_distrib];
Delsimps [o_apply];

(*Eliminate the "o" operator*)
val o_simp = simplify (simpset() addsimps [o_def]);

(*For rewriting of specifications related by "guarantees"*)
Addsimps [rename_image_constrains, rename_image_stable, 
	  rename_image_increasing, rename_image_invariant,
	  rename_image_Constrains, rename_image_Stable,
	  rename_image_Increasing, rename_image_Always,
	  rename_image_leadsTo, rename_image_LeadsTo,
	  rename_preserves,
	  bij_image_INT, bij_is_inj RS image_Int, bij_image_Collect_eq];

(*Splits up conjunctions & intersections: like CONJUNCTS in the HOL system*)
fun list_of_Int th = 
    (list_of_Int (th RS conjunct1) @ list_of_Int (th RS conjunct2))
    handle THM _ => (list_of_Int (th RS IntD1) @ list_of_Int (th RS IntD2))
    handle THM _ => (list_of_Int (th RS INT_D))
    handle THM _ => [th];

(*Used just once, for Alloc_Increasing*)
val lessThanBspec = lessThan_iff RS iffD2 RSN (2, bspec);
fun normalize th = 
     normalize (th RS spec
		handle THM _ => th RS lessThanBspec
		handle THM _ => th RS bspec
		handle THM _ => th RS (guarantees_INT_right_iff RS iffD1))
     handle THM _ => th;


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


(*** bijectivity of sysOfAlloc [MUST BE AUTOMATED] ***)

val record_auto_tac =
    auto_tac (claset() addIs [ext] addSWrapper record_split_wrapper, 
	      simpset() addsimps [sysOfAlloc_def, sysOfClient_def,
				  client_map_def, non_extra_def, funPair_def,
				  o_apply, Let_def]);


Goalw [sysOfAlloc_def, Let_def] "inj sysOfAlloc";
by (rtac injI 1);
by record_auto_tac;
qed "inj_sysOfAlloc";
AddIffs [inj_sysOfAlloc];

(*We need the inverse; also having it simplifies the proof of surjectivity*)
Goal "!!s. inv sysOfAlloc s = \
\            (| allocGiv = allocGiv s,   \
\               allocAsk = allocAsk s,   \
\               allocRel = allocRel s,   \
\               allocState_u.extra = (client s, extra s) |)";
by (rtac (inj_sysOfAlloc RS inv_f_eq) 1);
by record_auto_tac;
qed "inv_sysOfAlloc_eq";
Addsimps [inv_sysOfAlloc_eq];

Goal "surj sysOfAlloc";
by (simp_tac (simpset() addsimps [surj_iff, expand_fun_eq, o_apply]) 1);
by record_auto_tac;
qed "surj_sysOfAlloc";
AddIffs [surj_sysOfAlloc];

Goal "bij sysOfAlloc";
by (blast_tac (claset() addIs [bijI]) 1);
qed "bij_sysOfAlloc";
AddIffs [bij_sysOfAlloc];


(*** bijectivity of sysOfClient ***)

Goalw [sysOfClient_def] "inj sysOfClient";
by (rtac injI 1);
by record_auto_tac;
qed "inj_sysOfClient";
AddIffs [inj_sysOfClient];

Goal "!!s. inv sysOfClient s = \
\            (client s, \
\             (| allocGiv = allocGiv s, \
\                allocAsk = allocAsk s, \
\                allocRel = allocRel s, \
\                allocState_u.extra = systemState.extra s|) )";
by (rtac (inj_sysOfClient RS inv_f_eq) 1);
by record_auto_tac;
qed "inv_sysOfClient_eq";
Addsimps [inv_sysOfClient_eq];

Goal "surj sysOfClient";
by (simp_tac (simpset() addsimps [surj_iff, expand_fun_eq, o_apply]) 1);
by record_auto_tac;
qed "surj_sysOfClient";
AddIffs [surj_sysOfClient];

Goal "bij sysOfClient";
by (blast_tac (claset() addIs [bijI]) 1);
qed "bij_sysOfClient";
AddIffs [bij_sysOfClient];


(*** bijectivity of client_map ***)

Goalw [inj_on_def] "inj client_map";
by record_auto_tac;
qed "inj_client_map";
AddIffs [inj_client_map];

Goal "!!s. inv client_map s = \
\            (%(x,y).(|giv = giv x, ask = ask x, rel = rel x, \
\                      clientState_u.extra = y|)) s";
by (rtac (inj_client_map RS inv_f_eq) 1);
by record_auto_tac;
qed "inv_client_map_eq";
Addsimps [inv_client_map_eq];

Goal "surj client_map";
by (simp_tac (simpset() addsimps [surj_iff, expand_fun_eq, o_apply]) 1);
by record_auto_tac;
qed "surj_client_map";
AddIffs [surj_client_map];

Goal "bij client_map";
by (blast_tac (claset() addIs [bijI]) 1);
qed "bij_client_map";
AddIffs [bij_client_map];


(** o-simprules for client_map **)

Goalw [client_map_def] "fst o client_map = non_extra";
by (rtac fst_o_funPair 1);
qed "fst_o_client_map";
Addsimps (make_o_equivs fst_o_client_map);

Goalw [client_map_def] "snd o client_map = clientState_u.extra";
by (rtac snd_o_funPair 1);
qed "snd_o_client_map";
Addsimps (make_o_equivs snd_o_client_map);

(** o-simprules for sysOfAlloc [MUST BE AUTOMATED] **)

Goal "client o sysOfAlloc = fst o allocState_u.extra ";
by record_auto_tac;
qed "client_o_sysOfAlloc";
Addsimps (make_o_equivs client_o_sysOfAlloc);

Goal "allocGiv o sysOfAlloc = allocGiv";
by record_auto_tac;
qed "allocGiv_o_sysOfAlloc_eq";
Addsimps (make_o_equivs allocGiv_o_sysOfAlloc_eq);

Goal "allocAsk o sysOfAlloc = allocAsk";
by record_auto_tac;
qed "allocAsk_o_sysOfAlloc_eq";
Addsimps (make_o_equivs allocAsk_o_sysOfAlloc_eq);

Goal "allocRel o sysOfAlloc = allocRel";
by record_auto_tac;
qed "allocRel_o_sysOfAlloc_eq";
Addsimps (make_o_equivs allocRel_o_sysOfAlloc_eq);

(** o-simprules for sysOfClient [MUST BE AUTOMATED] **)

Goal "client o sysOfClient = fst";
by record_auto_tac;
qed "client_o_sysOfClient";
Addsimps (make_o_equivs client_o_sysOfClient);

Goal "allocGiv o sysOfClient = allocGiv o snd ";
by record_auto_tac;
qed "allocGiv_o_sysOfClient_eq";
Addsimps (make_o_equivs allocGiv_o_sysOfClient_eq);

Goal "allocAsk o sysOfClient = allocAsk o snd ";
by record_auto_tac;
qed "allocAsk_o_sysOfClient_eq";
Addsimps (make_o_equivs allocAsk_o_sysOfClient_eq);

Goal "allocRel o sysOfClient = allocRel o snd ";
by record_auto_tac;
qed "allocRel_o_sysOfClient_eq";
Addsimps (make_o_equivs allocRel_o_sysOfClient_eq);



(**
Open_locale "System";

val Alloc = thm "Alloc";
val Client = thm "Client";
val Network = thm "Network";
val System_def = thm "System_def";

(*CANNOT use bind_thm: it puts the theorem into standard form, in effect
  exporting it from the locale*)
**)

AddIffs [finite_lessThan];

(*Client : <unfolded specification> *)
val Client_Spec =
    rewrite_rule [client_spec_def, client_increasing_def,
		  client_bounded_def, client_progress_def,
		  client_preserves_def] Client;

val [Client_Increasing_ask, Client_Increasing_rel,
     Client_Bounded, Client_Progress, Client_preserves_giv,
     Client_preserves_extra] =
        Client_Spec 
          |> simplify (simpset() addsimps [guarantees_Int_right]) 
          |> list_of_Int;

AddIffs [Client_Increasing_ask, Client_Increasing_rel, Client_Bounded,
	 Client_preserves_giv, Client_preserves_extra];


(*Network : <unfolded specification> *)
val Network_Spec =
    rewrite_rule [network_spec_def, network_ask_def, network_giv_def, 
		  network_rel_def, network_preserves_def] Network;

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

AddIffs (Alloc_preserves |> simplify (simpset()) |> list_of_Int);

(** Components lemmas [MUST BE AUTOMATED] **)

Goal "Network Join \
\     ((rename sysOfClient \
\       (plam x: lessThan Nclients. rename client_map Client)) Join \
\      rename sysOfAlloc Alloc) \
\     = System";
by (simp_tac (simpset() addsimps System_def::Join_ac) 1);
qed "Network_component_System";

Goal "(rename sysOfClient \
\      (plam x: lessThan Nclients. rename client_map Client)) Join \
\     (Network Join rename sysOfAlloc Alloc)  =  System";
by (simp_tac (simpset() addsimps System_def::Join_ac) 1);
qed "Client_component_System";

Goal "rename sysOfAlloc Alloc Join \
\      ((rename sysOfClient (plam x: lessThan Nclients. rename client_map Client)) Join \
\       Network)  =  System";
by (simp_tac (simpset() addsimps System_def::Join_ac) 1);
qed "Alloc_component_System";

AddIffs [Client_component_System, Network_component_System, 
	 Alloc_component_System];

(** These preservation laws should be generated automatically **)

AddIs    [impOfSubs subset_preserves_o];
Addsimps [impOfSubs subset_preserves_o];


(*The proofs of rename_Client_Increasing, rename_Client_Bounded and
  rename_Client_Progress are similar.  All require copying out the original
  Client property.  A forward proof can be constructed as follows:

  Client_Increasing_ask RS
      (bij_client_map RS rename_rename_guarantees_eq RS iffD2)
  RS (lift_lift_guarantees_eq RS iffD2)
  RS guarantees_PLam_I
  RS (bij_sysOfClient RS rename_rename_guarantees_eq RS iffD2)
  |> simplify (simpset() addsimps [lift_image_eq_rename, o_def, split_def, 
				   surj_rename RS surj_range]);

However, the "preserves" property remains to be discharged, and the unfolding
of "o" and "sub" complicates subsequent reasoning.

The following tactic works for all three proofs, though it certainly looks
ad-hoc!
*)
val rename_client_map_tac =
  EVERY [
    simp_tac (simpset() addsimps [rename_guarantees_eq_rename_inv]) 1,
    rtac guarantees_PLam_I 1,
    assume_tac 2,
	 (*preserves: routine reasoning*)
    asm_simp_tac (simpset() addsimps [lift_preserves_sub]) 2,
	 (*the guarantee for  "lift i (rename client_map Client)" *)
    asm_simp_tac
	(simpset() addsimps [lift_guarantees_eq_lift_inv,
			     rename_guarantees_eq_rename_inv,
			     bij_imp_bij_inv, surj_rename RS surj_range,
			     inv_inv_eq]) 1,
    asm_simp_tac
        (simpset() addsimps [o_def, non_extra_def, guarantees_Int_right]) 1];


(*Lifting Client_Increasing to systemState*)
Goal "i : I \
\     ==> rename sysOfClient (plam x: I. rename client_map Client) : \
\           UNIV \
\           guarantees[(funPair rel ask) o sub i o client]  \
\             Increasing (ask o sub i o client) Int \
\             Increasing (rel o sub i o client)";
by rename_client_map_tac;
qed "rename_Client_Increasing";

Goal "i < Nclients \
\     ==> System : Increasing (ask o sub i o client) Int \
\                  Increasing (rel o sub i o client)";
by (rtac ([rename_Client_Increasing,
	   Client_component_System] MRS component_guaranteesD) 1);
by Auto_tac;
qed "System_Increasing";

bind_thm ("rename_guarantees_sysOfAlloc_I",
	  bij_sysOfAlloc RS rename_rename_guarantees_eq RS iffD2);


(*Lifting Alloc_Increasing up to the level of systemState*)
val rename_Alloc_Increasing = 
    Alloc_Increasing RS rename_guarantees_sysOfAlloc_I
     |> simplify (simpset() addsimps [surj_rename RS surj_range, o_def]);

Goalw [System_def]
     "i < Nclients ==> System : Increasing (sub i o allocGiv)";
by (simp_tac (simpset() addsimps [o_def]) 1);
by (rtac (rename_Alloc_Increasing RS guarantees_Join_I1 RS guaranteesD) 1);
by Auto_tac;
qed "System_Increasing_allocGiv";

AddSIs (list_of_Int System_Increasing);

(** Follows consequences.
    The "Always (INT ...) formulation expresses the general safety property
    and allows it to be combined using Always_Int_rule below. **)

Goal
  "i < Nclients ==> System : ((sub i o allocRel) Fols (rel o sub i o client))";
by (auto_tac (claset() addSIs [Network_Rel RS component_guaranteesD], 
	      simpset()));
qed "System_Follows_rel";

Goal
  "i < Nclients ==> System : ((sub i o allocAsk) Fols (ask o sub i o client))";
by (auto_tac (claset() addSIs [Network_Ask RS component_guaranteesD], 
	      simpset()));
qed "System_Follows_ask";

Goal
  "i < Nclients ==> System : (giv o sub i o client) Fols (sub i o allocGiv)";
by (auto_tac (claset() addSIs [Network_Giv RS component_guaranteesD, 
		 rename_Alloc_Increasing RS component_guaranteesD], 
	      simpset()));
by (ALLGOALS (simp_tac (simpset() addsimps [o_def, non_extra_def])));
by (auto_tac
    (claset() addSIs [rename_Alloc_Increasing RS component_guaranteesD],
     simpset()));
qed "System_Follows_allocGiv";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (giv o sub i o client) s <= (sub i o allocGiv) s})";
by Auto_tac;
by (etac (System_Follows_allocGiv RS Follows_Bounded) 1);
qed "Always_giv_le_allocGiv";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (sub i o allocAsk) s <= (ask o sub i o client) s})";
by Auto_tac;
by (etac (System_Follows_ask RS Follows_Bounded) 1);
qed "Always_allocAsk_le_ask";

Goal "System : Always (INT i: lessThan Nclients. \
\                      {s. (sub i o allocRel) s <= (rel o sub i o client) s})";
by (auto_tac (claset() addSIs [Follows_Bounded, System_Follows_rel], 
	      simpset()));
qed "Always_allocRel_le_rel";


(*** Proof of the safety property (1) ***)

(*safety (1), step 1 is System_Increasing_rel*)

(*safety (1), step 2*)
Goal "i < Nclients ==> System : Increasing (sub i o allocRel)";
by (etac (System_Follows_rel RS Follows_Increasing1) 1);
qed "System_Increasing_allocRel";

(*Lifting Alloc_safety up to the level of systemState*)
val rename_Alloc_Safety = 
    Alloc_Safety RS rename_guarantees_sysOfAlloc_I
     |> simplify (simpset() addsimps [o_def]);

(*safety (1), step 3*)
Goal "System : Always {s. sum (%i. (tokens o sub i o allocGiv) s) Nclients \
\                  <= NbT + sum (%i. (tokens o sub i o allocRel) s) Nclients}";
by (simp_tac (simpset() addsimps [o_apply]) 1);
by (rtac (rename_Alloc_Safety RS component_guaranteesD) 1);
by (auto_tac (claset(), 
	       simpset() addsimps [o_simp System_Increasing_allocRel]));
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
by (etac (System_Follows_ask RS Follows_Increasing1) 1);
qed "System_Increasing_allocAsk";

(*progress (2), step 3*)
(*All this trouble just to lift "Client_Bounded" to systemState
  (though it is similar to that for Client_Increasing*)
Goal "i : I \
\   ==> rename sysOfClient (plam x: I. rename client_map Client) : \
\         UNIV \
\         guarantees[ask o sub i o client]  \
\           Always {s. ALL elt : set ((ask o sub i o client) s). elt <= NbT}";
by rename_client_map_tac;
qed "rename_Client_Bounded";

Goal "i < Nclients \
\     ==> System : Always \
\                   {s. ALL elt : set ((ask o sub i o client) s). elt <= NbT}";
by (rtac ([rename_Client_Bounded,
	   Client_component_System] MRS component_guaranteesD) 1);
by Auto_tac;
qed "System_Bounded_ask";

(*progress (2), step 4*)
Goal "System : Always {s. ALL i : lessThan Nclients. \
\                          ALL elt : set ((sub i o allocAsk) s). elt <= NbT}";
by (auto_tac (claset(), 
	      simpset() addsimps [Collect_ball_eq]));
by (rtac (Always_Int_rule [Always_allocAsk_le_ask, System_Bounded_ask] 
    RS Always_weaken) 1);
by (auto_tac (claset() addDs [set_mono], simpset()));
qed "System_Bounded_allocAsk";

(*progress (2), step 5 is System_Increasing_allocGiv*)

(*progress (2), step 6*)
Goal "i < Nclients ==> System : Increasing (giv o sub i o client)";
by (etac (System_Follows_allocGiv RS Follows_Increasing1) 1);
qed "System_Increasing_giv";


Goal "i: I \
\  ==> rename sysOfClient (plam x: I. rename client_map Client) \
\       : Increasing (giv o sub i o client)  \
\         guarantees[funPair rel ask o sub i o client] \
\         (INT h. {s. h <= (giv o sub i o client) s & \
\                           h pfixGe (ask o sub i o client) s}  \
\                 LeadsTo {s. tokens h <= (tokens o rel o sub i o client) s})";
by rename_client_map_tac;
by (asm_simp_tac
    (simpset() addsimps [rewrite_rule [o_def] Client_Progress]) 1);
qed "rename_Client_Progress";


(*progress (2), step 7*)
Goal
 "System : (INT i : lessThan Nclients. \
\           INT h. {s. h <= (giv o sub i o client) s & \
\                      h pfixGe (ask o sub i o client) s}  \
\               LeadsTo {s. tokens h <= (tokens o rel o sub i o client) s})";
by (rtac INT_I 1);
(*Couldn't have just used Auto_tac since the "INT h" must be kept*)
by (rtac ([rename_Client_Progress,
	   Client_component_System] MRS component_guaranteesD) 1);
by (asm_full_simp_tac (simpset() addsimps [System_Increasing_giv]) 2);
by Auto_tac;
qed "System_Client_Progress";

(*Concludes
 System : {s. k <= (sub i o allocGiv) s} 
          LeadsTo
          {s. (sub i o allocAsk) s <= (ask o sub i o client) s} Int
          {s. k <= (giv o sub i o client) s} *)
val lemma =
    [System_Follows_ask RS Follows_Bounded,
     System_Follows_allocGiv RS Follows_LeadsTo] MRS Always_LeadsToD;

(*A more complicated variant of the previous one*)
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

(*Lifting Alloc_Progress up to the level of systemState*)
val rename_Alloc_Progress = 
    Alloc_Progress RS rename_guarantees_sysOfAlloc_I
     |> simplify (simpset() addsimps [o_def]);

(*progress (2), step 9*)
Goal
 "System : (INT i : lessThan Nclients. \
\           INT h. {s. h <= (sub i o allocAsk) s}  \
\                  LeadsTo {s. h pfixLe (sub i o allocGiv) s})";
(*Can't use simpset(): the "INT h" must be kept*)
by (simp_tac (HOL_ss addsimps [o_apply, sub_def]) 1);
by (rtac (rename_Alloc_Progress RS component_guaranteesD) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [o_simp System_Increasing_allocRel,
				  o_simp System_Increasing_allocAsk,
				  o_simp System_Bounded_allocAsk,
				  o_simp System_Alloc_Client_Progress]));
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


