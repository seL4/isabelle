(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator
*)


Goal "~ f #2 ==> ~ (!t::nat. (#0 <= t & t <= #10) --> f t)";

(*Useful examples:  singletonI RS subst_elem,  subst_elem RSN (2,IntI) *)
Goal "[| b:A;  a=b |] ==> a:A";
by (etac ssubst 1);
by (assume_tac 1);
qed "subst_elem";




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

val bij_sysOfAlloc = [inj_sysOfAlloc, surj_sysOfAlloc] MRS bijI;

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

val bij_sysOfClient = [inj_sysOfClient, surj_sysOfClient] MRS bijI;

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
Goalw [System_def] "Network <= System";
by (blast_tac (claset() addIs [componentI]) 1);
qed "Network_component_System";

Goalw [System_def] "(extend sysOfAlloc Alloc) <= System";
by (blast_tac (claset() addIs [componentI]) 1);
qed "Alloc_component_System";

AddIffs [Network_component_System, Alloc_component_System];


(* F : UNIV guarantees Increasing func
   ==> extend sysOfClient F : UNIV guarantees Increasing (func o client) *)
val extend_Client_guar_Increasing =
  bij_sysOfClient RS export extend_guar_Increasing
  |> simplify (simpset() addsimps [inv_sysOfClient_eq]);


(** Proof of property (1) **)

(*step 1*)
Goalw [System_def]
     "i < Nclients ==> System : Increasing (rel o sub i o client)";
by (rtac ([guaranteesI RS disjI2 RS guarantees_Join_I, UNIV_I] 
	  MRS guaranteesD) 1);
by (asm_simp_tac 
    (simpset() addsimps [guarantees_PLam_I, 
			 extend_Client_guar_Increasing RS guaranteesD,
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


(*NEED TO PROVE something like this (maybe without premise)*)
Goal "i < Nclients ==> System : (sub i o allocRel) localTo Network";

fun alloc_export th = bij_sysOfAlloc RS export th;

val extend_Alloc_guar_Increasing =
  alloc_export extend_guar_Increasing
  |> simplify (simpset() addsimps [inv_sysOfAlloc_eq]);

Goal "System : Always {s. sum (%i. (tokens o sub i o allocGiv) s) Nclients \
\                  <= NbT + sum (%i. (tokens o sub i o allocRel) s) Nclients}";
by (res_inst_tac 
    [("X", "(INT i : lessThan Nclients. (sub i o allocRel) localTo Network \
\                                       Int Increasing (sub i o allocRel))")] 
    component_guaranteesD 1);;
br Alloc_component_System 3;
br project_guarantees 1;
br Alloc_Safety 1;
by (dtac (alloc_export (project_extend_Join RSN (2, subst_elem RS project_Always_D))) 2 
     THEN
     full_simp_tac
     (simpset() addsimps [inv_sysOfAlloc_eq,
			  alloc_export Collect_eq_extend_set RS sym]) 2);
auto();
by (force_tac (claset(), simpset() addsimps [System_Increasing_allocRel]) 3);

bd bspec 1;
by (Blast_tac 1);


xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;

       [| i < Nclients;
          extend sysOfAlloc Alloc Join G
          : (sub i o allocRel) localTo Network &
          extend sysOfAlloc Alloc Join G : Increasing (sub i o allocRel) |]
       ==> Alloc Join project sysOfAlloc G : Increasing (sub i o allocRel)


       [| i < Nclients;
          H : (sub i o allocRel) localTo Network &
          H : Increasing (sub i o allocRel) |]
       ==> project sysOfAlloc H : Increasing (sub i o allocRel)

Open_locale"Extend";

Goal "(H : (func o f) localTo G) ==> (project h H : func localTo (project h G))";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, 
			 project_extend_Join RS sym,
			 Diff_project_stable,
			 Collect_eq_extend_set RS sym]) 1);
auto();
br Diff_project_stable 1;
PROBABLY FALSE;

by (Clarify_tac 1);
by (dres_inst_tac [("x","z")] spec 1);

br (alloc_export project_Always_D) 2;

by (rtac (alloc_export extend_Always RS iffD2) 2);

xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;

br guaranteesI 1;

by (res_inst_tac 
    [("X", "(INT i : lessThan Nclients. Increasing (sub i o allocRel))")] 
    component_guaranteesD 1);;


by (rtac (Alloc_Safety RS component_guaranteesD) 1);


br (alloc_export guarantees_imp_extend_guarantees RS guarantees_weaken) 1;
br Alloc_Safety 1;
