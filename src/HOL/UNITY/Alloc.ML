(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator
*)

Addsimps [sub_def];

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

(*could move to PPROD.ML, but function "sub" is needed there*)
Goal "lift_set i {s. P (f s)} = {s. P (f (sub i s))}";
by (asm_simp_tac (simpset() addsimps [lift_set_def]) 1);
qed "lift_set_sub";

(*ONE OF THESE IS REDUNDANT!*)
Goal "lift_set i {s. P (f s)} = {s. P (f (s i))}";
by (asm_simp_tac (simpset() addsimps [lift_set_def]) 1);
qed "lift_set_sub2";

Goalw [Increasing_def]
     "[| i: I;  finite I |]  \
\     ==> ((PPI x:I. F) : Increasing (f o sub i)) = (F : Increasing f)";
by (subgoal_tac "ALL z. {s. z <= (f o sub i) s} = lift_set i {s. z <= f s}" 1);
by (asm_simp_tac (simpset() addsimps [lift_set_sub]) 2);
by (asm_full_simp_tac (simpset() addsimps [PFUN_Stable]) 1);
qed "PFUN_Increasing";

(*FUN.ML*)
(*left-to-right inclusion holds even if I is empty*)
Goalw [inj_on_def]
   "[| inj_on f C;  ALL i:I. B i <= C;  j:I |] \
\   ==> f `` (INT i:I. B i) = (INT i:I. f `` B i)";
by (Blast_tac 1);
qed "inj_on_image_INT";



Goal "lift_prog i `` Increasing f <= Increasing (f o sub i)";
by (asm_simp_tac 
    (simpset() addsimps [Increasing_def,
			 inj_lift_prog RS inj_on_image_INT]) 1);
auto();
by (dres_inst_tac [("x","z")] spec 1);
auto();
by (asm_simp_tac (simpset() addsimps [lift_set_sub2 RS sym,
				      lift_prog_Stable_eq]) 1);
qed "image_lift_prog_Increasing";


Goal "i < Nclients ==> \
\     lift_prog i Client : range (lift_prog i) guar Increasing (rel o sub i)";



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
by (dtac (lessThan_iff RS iffD2 RS PFUN_Increasing RS iffD2) 1);
by Auto_tac;


by (full_simp_tac (simpset() addsimps [read_instantiate [("f1","rel"),("I1","lessThan Nclients")] (PFUN_Increasing RS sym)]) 1);

xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;


Goal "System : system_spec";

by (full_simp_tac
    (simpset() addsimps [alloc_spec_def, alloc_safety_def, System_def]) 1);






(*partial system...*)
Goal "[| Alloc : alloc_spec;  Network : network_spec |] \
\     ==> (extend sysOfAlloc Alloc) Join Network : system_spec";

(*partial system...*)
Goal "[| Client : client_spec;  Network : network_spec |] \
\     ==> (extend sysOfClient (PPI x: lessThan Nclients. Client)) \
\         Join Network : system_spec";



Goal "[| Alloc : alloc_spec;  Client : client_spec;  \
\        Network : network_spec |] \
\     ==> (extend sysOfAlloc Alloc) \
\         Join (extend sysOfClient (PPI x: lessThan Nclients. Client)) \
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




(*Generalized version allowing different clients*)
Goal "[| Alloc : alloc_spec;  \
\        Client : (lessThan Nclients) funcset client_spec;  \
\        Network : network_spec |] \
\     ==> (extend sysOfAlloc Alloc) \
\         Join (extend sysOfClient (PPROD (lessThan Nclients) Client)) \
\         Join Network : system_spec";

