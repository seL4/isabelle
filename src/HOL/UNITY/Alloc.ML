(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator
*)

		Goal "(%(x,y). f(x,y)) = f";
		by (rtac ext 1);
		by (pair_tac "x" 1);
		by (Simp_tac 1);
		qed "split_Pair_apply";

		Goal "(SOME x. P x) = (SOME (a,b). P(a,b))";
		by (simp_tac (simpset() addsimps [split_Pair_apply]) 1);
		qed "split_paired_Eps";

		Goal "[| inj(f);  f x = y |] ==> inv f y = x";
		by (etac subst 1);
		by (etac inv_f_f 1);
		qed "inv_f_eq";

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

(**THESE SHOULD NOT BE NECESSARY...THE VARIOUS INJECTIONS INTO THE SYSTEM
   STATE NEED TO BE TREATED SYMMETRICALLY OR DONE AUTOMATICALLY*)
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


Open_locale "System";

val Alloc = thm "Alloc";
val Client = thm "Client";
val Network = thm "Network";
val System_def = thm "System_def";

AddIffs [finite_lessThan];


Goal "Client : UNIV guar Increasing ask";
by (cut_facts_tac [Client] 1);
by (asm_full_simp_tac
    (simpset() addsimps [client_spec_def, client_increasing_def,
			 guarantees_Int_right]) 1);
qed "Client_Increasing_ask";

Goal "Client : UNIV guar Increasing rel";
by (cut_facts_tac [Client] 1);
by (asm_full_simp_tac
    (simpset() addsimps [client_spec_def, client_increasing_def,
			 guarantees_Int_right]) 1);
qed "Client_Increasing_rel";

AddIffs [Client_Increasing_ask, Client_Increasing_rel];

Goal "Client : UNIV guar Always {s. ALL elt : set (ask s). elt <= NbT}";
by (cut_facts_tac [Client] 1);
by (asm_full_simp_tac
    (simpset() addsimps [client_spec_def, client_bounded_def]) 1);
qed "Client_Bounded";

(*Client_Progress we omit for now, since it's cumbersome to state*)



Goal "lift_prog i Client : UNIV guar Increasing (rel o sub i)";
by (rtac (Client_Increasing_rel RS lift_prog_guar_Increasing) 1);
qed "lift_prog_Client_Increasing_rel";



(*Comp.ML??????????*)



val project_guarantees' =
  [inj_sysOfClient, surj_sysOfClient] MRS export project_guarantees;

val extend_guar_Increasing' =
  [inj_sysOfClient, surj_sysOfClient] MRS export extend_guar_Increasing;


(*MUST BE AUTOMATED: even the statement of such results*)
Goal "!!s. inv sysOfClient s = \
\            (client s, \
\             (| allocGiv = allocGiv s, \
\                allocAsk = allocAsk s, \
\                allocRel = allocRel s|) )";
by (rtac (inj_sysOfClient RS inv_f_eq) 1);
by (rewrite_goals_tac [sysOfAlloc_def, sysOfClient_def]);
by (auto_tac (claset() addSWrapper record_split_wrapper, simpset()));
qed "inv_sysOfClient";




val prems =
Goalw [PLam_def]
     "[| !!i. i:I ==> F i : X i guar Y i;  \
\        !!i H. [| i:I; H : XX i |] ==> drop_prog i H : X i;  \
\        !!i G. [| i:I; F i Join drop_prog i G : Y i |] \
\               ==> lift_prog i (F i) Join G : YY i |] \
\        ==> (PLam I F) : (INTER I XX) guar (INTER I YY)";
by (rtac (drop_prog_guarantees RS guarantees_JN_INT) 1);
by (REPEAT (ares_tac prems 1));
qed "drop_prog_guarantees_PLam";


(*for proof of property (1) *)
Goal "i < Nclients ==> System : Increasing (rel o sub i o client)";
by (full_simp_tac (simpset() addsimps [System_def]) 1);
by (rtac ([asm_rl, UNIV_I] MRS guaranteesD) 1);
by (rtac (disjI2 RS guarantees_Join_I) 1);
by (rtac project_guarantees' 1);
by (rtac subset_refl 2);
by (Clarify_tac 2);
by (rtac ([extend_guar_Increasing',subset_refl] MRS 
    guarantees_weaken RS guaranteesD) 2);
by (rtac UNIV_I 4);
by (force_tac (claset(),
	       simpset() addsimps [inv_sysOfClient]) 3);
by (asm_simp_tac (simpset() addsimps [guarantees_PLam_I, 
		      Client_Increasing_rel RS lift_prog_guar_Increasing]) 2);

by (rtac (Client_Increasing_rel RS drop_prog_guarantees_PLam RS guarantees_weaken) 1);
by (force_tac (claset() addIs [lift_prog_Join_Stable],
	       simpset() addsimps [Increasing_def]) 2);
by Auto_tac;
qed "System_Increasing_rel";


yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy;



(*partial system...*)
Goal "[| Alloc : alloc_spec;  Network : network_spec |] \
\     ==> (extend sysOfAlloc Alloc) Join Network : system_spec";

(*partial system...*)
Goal "[| Client : client_spec;  Network : network_spec |] \
\     ==> (extend sysOfClient (plam x: lessThan Nclients. Client)) \
\         Join Network : system_spec";



Goal "[| Alloc : alloc_spec;  Client : client_spec;  \
\        Network : network_spec |] \
\     ==> (extend sysOfAlloc Alloc) \
\         Join (extend sysOfClient (plam x: lessThan Nclients. Client)) \
\         Join Network : system_spec";
by (full_simp_tac
    (simpset() addsimps [system_spec_def, system_safety_def]) 1);
by Auto_tac;
by (full_simp_tac
    (simpset() addsimps [client_spec_def, client_increasing_def,
			 guarantees_Int_right]) 1);
by Auto_tac;
by (dtac (UNIV_I RSN (2, guaranteesD)) 1);
back();
by (full_simp_tac
    (simpset() addsimps [network_spec_def, network_rel_def]) 1);


by (full_simp_tac
    (simpset() addsimps [alloc_spec_def, alloc_safety_def]) 1);
by Auto_tac;

by (Simp_tac 1);
