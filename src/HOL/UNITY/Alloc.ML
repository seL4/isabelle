(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator
*)

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

(**SHOULD NOT BE NECESSARY: The various injections into the system
   state need to be treated symmetrically or done automatically*)
Goalw [sysOfClient_def] "inj sysOfClient";
by (rtac injI 1);
by (auto_tac (claset() addSDs [inj_sysOfAlloc RS injD]
		       addSWrapper record_split_wrapper, simpset()));
qed "inj_sysOfClient";

Goalw [sysOfClient_def] "surj sysOfClient";
by (cut_facts_tac [surj_sysOfAlloc] 1);
by (rewtac surj_def);
by Auto_tac;
by (Blast_tac 1);
qed "surj_sysOfClient";

AddIffs [inj_sysOfClient, surj_sysOfClient];


(*MUST BE AUTOMATED: even the statement of such results*)
Goal "!!s. inv sysOfClient s = \
\            (client s, \
\             (| allocGiv = allocGiv s, \
\                allocAsk = allocAsk s, \
\                allocRel = allocRel s|) )";
by (rtac (inj_sysOfClient RS inv_f_eq) 1);
by (rewrite_goals_tac [sysOfAlloc_def, sysOfClient_def]);
by (auto_tac (claset() addSWrapper record_split_wrapper, simpset()));
qed "inv_sysOfClient_eq";


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
val Network_Ask = Network_Spec RS IntD1 RS IntD1;
val Network_Giv = Network_Spec RS IntD1 RS IntD2;
val Network_Rel = Network_Spec RS IntD2 RS INT_D;


(*Alloc : <unfolded specification> *)
val Alloc_Spec =
    rewrite_rule [alloc_spec_def, alloc_increasing_def,
		  alloc_safety_def, alloc_progress_def] Alloc;

Goal "i < Nclients ==> Alloc : UNIV guarantees Increasing (sub i o allocAsk)";
by (cut_facts_tac [Alloc_Spec] 1);
by (asm_full_simp_tac (simpset() addsimps [guarantees_INT_right]) 1);
qed "Alloc_Increasing";

val Alloc_Safety = Alloc_Spec RS IntD1 RS IntD2;
val Alloc_Progress = (Alloc_Spec RS IntD2
                      |> simplify (simpset() addsimps [guarantees_INT_right]))
                     RS bspec RS spec;
		     


(*Not sure what to say about the other components because they involve
  extend*)
Goalw [System_def] "Network component System";
by (blast_tac (claset() addIs [componentI]) 1);
qed "Network_component_System";

AddIffs [Network_component_System];


val project_guarantees' =
  [surj_sysOfClient, inj_sysOfClient] MRS export project_guarantees;

(* F : UNIV guarantees Increasing func
   ==> extend sysOfClient F : UNIV guarantees Increasing (func o client) *)
val extend_guar_Increasing' =
  [surj_sysOfClient, inj_sysOfClient] MRS export extend_guar_Increasing
  |> simplify (simpset() addsimps [inv_sysOfClient_eq]);


(** Proof of property (1) **)

(*step 1*)
Goalw [System_def]
     "i < Nclients ==> System : Increasing (rel o sub i o client)";
by (rtac ([guaranteesI RS disjI2 RS guarantees_Join_I, UNIV_I] 
	  MRS guaranteesD) 1);
by (asm_simp_tac 
    (simpset() addsimps [guarantees_PLam_I, 
			 extend_guar_Increasing' RS guaranteesD,
			 lift_prog_guar_Increasing]) 1);
qed "System_Increasing_rel";

(*Note: the first step above performs simple quantifier reasoning.  It could
  be replaced by a proof mentioning no guarantees primitives*)


(*step 2*)
Goal "i < Nclients ==> System : Increasing (sub i o allocRel)";
by (rtac Follows_Increasing1 1);
by (blast_tac (claset() addIs [Network_Rel RS component_guaranteesD,
			       System_Increasing_rel, Network]) 1);
qed "System_Increasing_allocRel";

Goal "i < Nclients \
\ ==> System : Always {s. sum (%i. (tokens o sub i o allocGiv) s) Nclients \
\                  <= NbT + sum (%i. (tokens o sub i o allocRel) s) Nclients}";
fr component_guaranteesD;

val extend_guar_Increasing'' =
  [surj_sysOfAlloc, inj_sysOfAlloc] MRS export extend_guar_Increasing
  |> simplify (simpset() addsimps [inv_sysOfAlloc_eq]);

by (rtac (Alloc_Safety RS component_guaranteesD) 1);
