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
by Auto_tac;
qed "inj_sysOfAlloc";

Goalw [sysOfAlloc_def] "surj sysOfAlloc";
by (res_inst_tac [("f", "%s. ((| allocGiv = allocGiv s,    \
\                                allocAsk = allocAsk s,    \
\                                allocRel = allocRel s |), \
\                             client s)")] surjI 1);
by Auto_tac;
qed "surj_sysOfAlloc";

AddIffs [inj_sysOfAlloc, surj_sysOfAlloc];


Open_locale "System";

val Alloc = thm "Alloc";
val Client = thm "Client";
val Network = thm "Network";
val System_def = thm "System_def";

AddIffs [finite_lessThan];



Goal "i < Nclients ==> \
\     lift_prog i Client : UNIV guar Increasing (rel o sub i)";








by (stac Acts_eq 1);

fr conjI;
by (Clarify_tac 1);
by (stac Init_eq 1);


{GX. EX G:X. lift_prog i G component GX}
{GY. EX G:Y. lift_prog i G component GY}



uuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuu;




Goal "i < Nclients ==> System : Increasing (sub i o allocRel)";
by (cut_facts_tac [Client] 1);
by (full_simp_tac
    (simpset() addsimps [System_def,
			 client_spec_def, client_increasing_def,
			 guarantees_Int_right]) 1);
by Auto_tac;
by (dtac lift_prog_guarantees 1);
by (dtac (UNIV_I RSN (2, guaranteesD)) 1);
back();
by (dtac (lessThan_iff RS iffD2 RS const_PLam_Increasing RS iffD2) 1);
by Auto_tac;


by (full_simp_tac (simpset() addsimps [read_instantiate [("f1","rel"),("I1","lessThan Nclients")] (const_PLam_Increasing RS sym)]) 1);

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

by (subgoal_tac "" 1);
by (full_simp_tac
    (simpset() addsimps [alloc_spec_def, alloc_safety_def]) 1);
by Auto_tac;

by (Simp_tac 1);
