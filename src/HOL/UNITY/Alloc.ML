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
Goal "lift_set i {s. P s} = {s. P (sub i s)}";
by (asm_simp_tac (simpset() addsimps [lift_set_def]) 1);
qed "lift_set_sub";

(*ONE OF THESE IS REDUNDANT!*)
Goal "lift_set i {s. P s} = {s. P (s i)}";
by (asm_simp_tac (simpset() addsimps [lift_set_def]) 1);
qed "lift_set_sub2";

Goalw [Increasing_def]
     "[| i: I;  finite I |]  \
\     ==> ((plam x:I. F) : Increasing (f o sub i)) = (F : Increasing f)";
by (subgoal_tac "ALL z. {s. z <= (f o sub i) s} = lift_set i {s. z <= f s}" 1);
by (asm_simp_tac (simpset() addsimps [lift_set_sub]) 2);
by (asm_full_simp_tac (simpset() addsimps [const_PLam_Stable]) 1);
qed "const_PLam_Increasing";


(*The other direction fails: having FF : Stable {s. z <= f (s i)} does not
  ensure that F has the form lift_prog i F for some F.*)
Goal "lift_prog i `` Stable {s. P (f s)} <= Stable {s. P (f (s i))}";
by Auto_tac;
by (stac (lift_set_sub2 RS sym) 1); 
by (asm_simp_tac (simpset() addsimps [lift_prog_Stable_eq]) 1);
qed "image_lift_prog_Stable";

Goal "lift_prog i `` Increasing f <= Increasing (f o sub i)";
by (simp_tac (simpset() addsimps [Increasing_def,
				  inj_lift_prog RS image_INT]) 1);
by (blast_tac (claset() addIs [impOfSubs image_lift_prog_Stable]) 1);
qed "image_lift_prog_Increasing";


(*****************PPROD.ML******************)

(*???????????????*)
Goal "[| F : (drop_prog i `` X) guar (drop_prog i `` Y);  modular i Y |] \
\     ==> lift_prog i F : X guar Y";
by (rtac guaranteesI 1);
by (dtac guaranteesD 1);
by (rtac image_eqI 1);
by (rtac (drop_prog_lift_prog_Join RS sym) 1);
by (assume_tac 1);
by Auto_tac;
by (full_simp_tac (simpset() addsimps [modular_def,
				       drop_prog_lift_prog_Join RS sym]) 1);
by (dtac sym 1);
by (Blast_tac 1);
qed "drop_prog_guarantees";

Goalw [constrains_def]
     "(drop_prog i F : A co B)  =  \
\     (F : (lift_set i A) co (lift_set i B))";
by Auto_tac;
by (force_tac (claset(), 
	       simpset() addsimps [drop_act_def]) 2);
by (blast_tac (claset() addIs [drop_act_I]) 1);
qed "drop_prog_constrains_eq";

Goal "(drop_prog i F : stable A)  =  (F : stable (lift_set i A))";
by (simp_tac (simpset() addsimps [stable_def, drop_prog_constrains_eq]) 1);
qed "drop_prog_stable_eq";

Goal "modular i (stable {s. P(s i)})";
by (simp_tac (simpset() addsimps [modular_def, lift_set_sub2 RS sym,
				  drop_prog_stable_eq RS sym]) 1);
by Auto_tac;
qed "modular_stable_i";


(** Weak Constrains and Stable **)

Goal "f : reachable F ==> f i : reachable (drop_prog i F)";
by (etac reachable.induct 1);
by (force_tac (claset() addIs [reachable.Acts, drop_act_I],
	       simpset()) 2);
by (force_tac (claset() addIs [reachable.Init, drop_set_I],
	       simpset()) 1);
qed "reachable_imp_reachable_drop_prog";

Goalw [Constrains_def]
     "drop_prog i F : A Co B ==> F : (lift_set i A) Co (lift_set i B)";
by (full_simp_tac (simpset() addsimps [drop_prog_constrains_eq]) 1);
by (etac constrains_weaken_L 1);
by Auto_tac;
by (etac reachable_imp_reachable_drop_prog 1);
qed "drop_prog_Constrains_D";

Goalw [Stable_def]
     "drop_prog i F : Stable A ==> F : Stable (lift_set i A)";
by (asm_simp_tac (simpset() addsimps [drop_prog_Constrains_D]) 1);
qed "drop_prog_Stable_D";

(***?????????????
Goal "i ~= j ==> lift_prog i `` UNIV <= stable {s. P (f (s j))}";
by Auto_tac;
by (stac (lift_set_sub2 RS sym) 1); 
by (asm_simp_tac (simpset() addsimps [lift_prog_Stable_eq]) 1);
qed "image_lift_prog_Stable";
??????????????*)



(****UNITY.ML?  BUT it's not clear that Idle is good for anything.
     Could equally want to forbid actions that are subsets of Id 
   OR can simple constraints on actions prevent this?****)
Goalw [constrains_def, Idle_def] "F : Idle ==> (F : A co B) = (A<=B)";
by (Blast_tac 1);
qed "constrains_Idle_iff";

Goalw [stable_def,constrains_def,Idle_def] "F : Idle ==> F : stable A";
by (Blast_tac 1);
qed "stable_Idle";

Goalw [drop_act_def, lift_act_def]
     "i~=j ==> drop_act i (lift_act j act) <= Id";
by Auto_tac;
by (etac subst 1);
by (Asm_simp_tac 1);
qed "neq_drop_act_lift_act";

Goal "drop_prog i (JN j:I - {i}. lift_prog j F) : Idle";
by (simp_tac (simpset() addsimps [Acts_JN,Idle_def]) 1);
by Auto_tac;
by (rtac ccontr 1);  
  (*otherwise PROOF FAILED because tactics don't get negated conclusion*)
by (blast_tac (claset() addSDs [impOfSubs neq_drop_act_lift_act]) 1);
qed "drop_prog_JN_other_Idle";

Goal "[| F component G;  G : Idle |] ==> F : Idle";
by (full_simp_tac (simpset() addsimps [Idle_def, component_eq_subset]) 1);
by Auto_tac;
qed "component_Idle";

Goal "G component (JN j: I-{i}. JN H: UNIV. lift_prog j H) \
\     ==> drop_prog i G : Idle";
by (dtac drop_prog_mono 1);
by (etac component_Idle 1);
by (simp_tac (simpset() addsimps [drop_prog_JN_other_Idle, 
				  lift_prog_JN RS sym]) 1);
qed "component_JN_neq_imp_Idle";

Goal "drop_prog i G : Idle ==> G : stable (lift_set i A)";
by (simp_tac (simpset() addsimps [drop_prog_stable_eq RS sym]) 1);
by (blast_tac (claset() addIs [stable_Idle]) 1);
qed "Idle_imp_stable_lift_set";

(*like neq_drop_act_lift_act but stronger premises and conclusion*)
Goal "[| i~=j;  act ~= {} |] ==> drop_act i (lift_act j act) = Id";
by (rtac equalityI 1);
by (etac neq_drop_act_lift_act 1);
by (asm_simp_tac (simpset() addsimps [drop_act_def, lift_act_def]) 1);
by Auto_tac;
ren "s s'" 1;
by (dres_inst_tac [("x", "f(i:=x,j:=s)")] spec 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x", "f(i:=x,j:=s')")] spec 1);
by (Asm_full_simp_tac 1);
by (swap_res_tac [ext] 1);
by (Asm_simp_tac 1);
qed "neq_drop_act_lift_act_eq";


Goal "act ~= {} ==> drop_act i (lift_act j act) = (if i=j then act else Id)";
by (asm_simp_tac (simpset() addsimps [neq_drop_act_lift_act_eq]) 1);
qed "drop_act_lift_act_eq";


(*first premise says that the system has an initial state*)
Goalw [PLam_def]
     "[| ALL j:I. f0 j : Init (F j);   \
\        ALL j:I. {}  ~: Acts (F j);   i: I |] \
\     ==> drop_prog i (plam j:I. F j) = F i";
by (simp_tac (simpset() addsimps [Acts_JN, lift_prog_def, drop_prog_def]) 1);
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [drop_set_INT_lift_set]) 1);
by (Asm_simp_tac 1);
by (subgoal_tac
    "drop_act i `` (UN i:I. lift_act i `` Acts (F i)) = Acts (F i)" 1);
by (Asm_simp_tac 1);
by Auto_tac;
ren "act" 1;
by (subgoal_tac "act ~= {}" 1);
by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [drop_act_lift_act_eq]) 1);
by (rtac image_eqI 1);
by (rtac (lift_act_inverse RS sym) 1);
by Auto_tac;
qed "drop_prog_plam_eq";

xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;

(**STILL trying to lift the guarantees propery from one client to a family.
   first with a "localTo" precondition.  Then to look at the void (UNIV) 
   precondition.**)

(*CANNOT be proved because the premise tells us NOTHING AT ALL about
  actions outside i [rather than telling us there aren't any]
  MAY UNIVERSALLY QUANTIFY both premise and conclusion???**)
Goal "F : stable (lift_set i A) ==> x = lift_prog i (drop_prog i x)";

(*I.E TRY THIS*)
Goal "{F. F = (plam j:UNIV. drop_prog j F)} Int (INT i. stable (lift_set i A)) \
\     <= (INT i. lift_prog i `` stable A)";


Goal "{F. F = (plam j:UNIV. drop_prog j F)} Int stable (lift_set i A) \
\     <= lift_prog i `` stable A";
by Auto_tac;
fr image_eqI;
by (etac (drop_prog_stable_eq RS iffD2) 2);
by (etac ssubst 1);
by (stac drop_prog_plam_eq 1);
by Auto_tac;


by (asm_simp_tac (simpset() addsimps [lift_prog_Stable_eq]) 1);
qed "image_lift_prog_Stable";


Goal "{F. F = (plam i:UNIV. drop_prog i F)} Int stable {s. P (f (s i))} \
\     <= lift_prog i `` stable {s. P (f s)}";
by (stac (lift_set_sub2 RS sym) 1); 


Goal "Cl : (f localTo F) guar Increasing f   ==> \
\ lift_prog i Cl : (f o sub i) localTo (lift_prog i F)  \
\                  guar Increasing (f o sub i)";
by (dtac lift_prog_guarantees 1);
by (etac guarantees_weaken 1);
by (rtac image_lift_prog_Increasing 2);







Goal "(f o sub i) localTo (lift_prog i F) <= lift_prog i `` (f localTo F)";






Goal "(f o sub i) localTo (lift_prog i F) <= lift_prog i `` (f localTo F)";
by (simp_tac (simpset() addsimps [localTo_def]) 1);
by Auto_tac;
by (dres_inst_tac [("x","z")] spec 1);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [lift_set_sub2 RS sym,
				      lift_prog_stable_eq]) 1);
qed "image_lift_prog_?";

Goal "{GX. EX G: UNIV. lift_prog i G component GX} = UNIV";
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by (asm_full_simp_tac (simpset() addsimps [lift_set_def]) 1);
ren "GX" 1;
by (res_inst_tac [("x", "mk_program((%f. f i)``(Init GX), drop_act i `` Acts GX)")] exI 1);
by Auto_tac;




(*quantified formula's too strong and yet too weak.
  Close to what's needed, but maybe need further restrictions on X, Y*)
Goal "[| F : (drop_prog i `` X) guar (drop_prog i `` Y);  \
\        ALL j: -{i}. drop_prog j `` X <= drop_prog j `` Y |] \
\     ==> lift_prog i F : X guar Y";
by (rtac guaranteesI 1);
by (dtac guaranteesD 1);
by (rtac image_eqI 1);
by (rtac (drop_prog_lift_prog_Join RS sym) 1);
by (assume_tac 1);
by Auto_tac;
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join RS sym]) 1);
by (subgoal_tac "ALL k. drop_prog k (lift_prog i F Join G) = drop_prog k x" 1);
by (Clarify_tac 2);
by (case_tac "k=i" 2);
by (Blast_tac 2);

by (dres_inst_tac [("f", "lift_prog i")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [singleton_drop_prog_inverse]) 1);

by (dtac sym 1);
by (Blast_tac 1);
qed "drop_prog_guarantees";

Goalw [guarantees_def]
    "[| F : (X Int A) guar (Y Int A);  \
\       F : (X Int B) guar (Y Int B);  \
\       UNIV <= A Un B |] \
\    ==> F : X guar Y";
by (Blast_tac 1);
qed "guarantees_Un_partition_I";

Goalw [guarantees_def]
    "[| ALL i:I. F : (X Int A i) guar (Y Int A i);  UNIV <= UNION I A |] \
\    ==> F : X guar Y";
by (Blast_tac 1);
qed "guarantees_UN_partition_I";

Goal "{G. G component (JN j: I-{i}. JN H: UNIV. lift_prog j H)} \
\     <= stable (lift_set i A)";
by (Clarify_tac 1);
by (etac (component_JN_neq_imp_Idle RS Idle_imp_stable_lift_set) 1);
result();

Goal "i~=j ==> (lift_prog j `` UNIV) <= Increasing (f o sub i)";
by (rewtac Increasing_def);
by Auto_tac;
by (stac (lift_set_sub2 RS sym) 1); 
by (blast_tac (claset() addIs [neq_imp_lift_prog_Stable]) 1);
result();

Goal "Cl : UNIV guar Increasing f   ==> \
\ lift_prog i Cl : {G. G component (JN j: I. JN H: UNIV. lift_prog j H)} \
\                  guar Increasing (f o sub i)";
by (rtac guarantees_partition_I 1);
by (simp_tac (simpset() addsimps []) 1);

by (dtac lift_prog_guarantees 1);
by (etac guarantees_weaken 1);
by Auto_tac;
by (rtac (impOfSubs image_lift_prog_Increasing) 1);
by Auto_tac;
result();


Goal "drop_prog i `` UNIV = UNIV";
by Auto_tac;
fr image_eqI;
by (rtac (lift_prog_inverse RS sym) 1);
by Auto_tac;
result();


Goal "x : reachable (drop_prog i F) ==> x : drop_set i (reachable F)";
by (etac reachable.induct 1);
by Auto_tac;
by (rewtac drop_set_def);
by (force_tac (claset() addIs [reachable.Init, drop_set_I],
	       simpset()) 1);
by (rewtac drop_act_def);
by Auto_tac;
by (rtac imageI 1);
by (rtac reachable.Acts 1);
by (assume_tac 1);
by (assume_tac 1);


Goal "reachable (drop_prog i F) = drop_set i (reachable F)";
by (rewtac drop_set_def);
by Auto_tac;
by (etac reachable_imp_reachable_drop_prog 2);





Goalw [Constrains_def]
     "(F : (lift_set i A) Co (lift_set i B)) \
\     ==> (drop_prog i F : A Co B)";
by (full_simp_tac (simpset() addsimps [drop_prog_constrains_eq]) 1);
by (etac constrains_weaken_L 1);

by Auto_tac;
by (force_tac (claset(), 
	       simpset() addsimps [drop_act_def]) 2);
by (blast_tac (claset() addIs [drop_act_I]) 1);
qed "drop_prog_Constrains_eq";


(*Does NOT appear to be provable, so this notion of modular is too strong*)
Goal "lift_prog i `` drop_prog i `` Increasing (f o sub i) \
\        <= Increasing (f o sub i)";
by (simp_tac (simpset() addsimps [Increasing_def]) 1);
by Auto_tac;
by (stac (lift_set_sub2 RS sym) 1); 
by (simp_tac (simpset() addsimps [lift_prog_Stable_eq]) 1);





Goal "[| F : (drop_prog i `` X) guar (drop_prog i `` Y);  \
\        X <= (UN F. {lift_prog i F});  \
\        lift_prog i `` drop_prog i `` Y <= Y |] \
\     ==> lift_prog i F : X guar Y";
by (rtac guaranteesI 1);
by (set_mp_tac 1);
by (Clarify_tac 1);
by (dtac guaranteesD 1);
by (rtac image_eqI 1);
by (rtac (drop_prog_lift_prog_Join RS sym) 1);
by (assume_tac 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join RS sym]) 1);
by Auto_tac;
qed "drop_prog_guarantees";



NEW NOTION OF MODULAR


Goal "(ALL H:X. lift_prog i (drop_prog i H) : X) = \
\     (lift_prog i `` drop_prog i `` X <= X)";
by Auto_tac;
qed "modular_equiv";

Goal "lift_prog i `` drop_prog i `` (lift_prog i `` F) <= lift_prog i `` F";
by (simp_tac (simpset() addsimps [image_compose RS sym, o_def]) 1);
result();

Goal "[| F : (drop_prog i `` X) guar (drop_prog i `` Y);  \
\        lift_prog i `` drop_prog i `` X <= X;  \
\        lift_prog i `` drop_prog i `` Y <= Y|] \
\     ==> lift_prog i F : X guar Y";
by (full_simp_tac (simpset() addsimps [modular_equiv RS sym]) 1);
by (rtac guaranteesI 1);
by (ball_tac 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by (dtac guaranteesD 1);
by (rtac image_eqI 1);
by (assume_tac 2);back();
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by (ALLGOALS Clarify_tac);
by (dres_inst_tac [("f", "lift_prog i")] arg_cong 1);

by (rtac guaranteesI 1);
by (dtac guaranteesD 1);
by (ALLGOALS Clarify_tac);
by (rtac image_eqI 1);
by (rtac (drop_prog_lift_prog_Join RS sym) 1);
by (assume_tac 1);
by (full_simp_tac (simpset() addsimps [modular_equiv RS sym]) 1);
by (REPEAT (ball_tac 1));
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
ren "H" 1;
by (dtac sym 1);
by (asm_full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
????????????????;

by Auto_tac;

by (dres_inst_tac [("f", "drop_prog i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by (assume_tac 1);
by (ALLGOALS Clarify_tac);
by (set_mp_tac 1);
by (ALLGOALS Clarify_tac);
by Auto_tac;
by (dres_inst_tac [("f", "drop_prog i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by Auto_tac;
qed "drop_prog_guarantees";








Goal "(lift_prog i `` F) <= lift_prog i `` drop_prog i `` (lift_prog i `` F)";
by (simp_tac (simpset() addsimps [image_compose RS sym, o_def]) 1);
by Auto_tac;
result();





(*FAILS*)
Goal "modular i (lift_prog i `` Y)";





Goal "Cl : UNIV guar Increasing f \
\     ==>lift_prog i Cl : UNIV guar Increasing (f o sub i)";
by (rtac drop_prog_guarantees 1);
by (rewtac Increasing_def);
by (etac guarantees_weaken 1);
by Auto_tac;
by (rtac image_eqI 1);
by (rtac (lift_prog_inverse RS sym) 1);
by Auto_tac;
by (stac (lift_set_sub2 RS sym) 1); 
by (asm_simp_tac (simpset() addsimps [lift_prog_Stable_eq]) 1);



(*could move to PPROD.ML, but function "sub" is needed there*)
Goalw [drop_set_def] "drop_set i {s. P (f (sub i s))} = {s. P (f s)}";
by Auto_tac;
qed "drop_set_sub";

Goal "lift_set i (reachable (drop_prog i F)) = reachable F";

(*False?*)
Goal "modular i ((f o sub i) localTo (lift_prog i F))";
by (simp_tac (simpset() addsimps [localTo_def, modular_def]) 1);
by Auto_tac;



(*FAILS*)
Goal "(drop_prog i F : A Co B)  =  \
\     (F : (lift_set i A) Co (lift_set i B))";
by (simp_tac (simpset() addsimps [Constrains_def, drop_prog_constrains_eq,
				  lift_set_Int]) 1);

??
by (simp_tac (simpset() addsimps [Constrains_def, reachable_drop_prog,
				  drop_set_Int RS sym,
				  drop_prog_constrains_eq]) 1);
qed "drop_prog_Constrains_eq";

(*FAILS*)
Goal "(drop_prog i F : Stable A)  =  (F : Stable (lift_set i A))";
by (simp_tac (simpset() addsimps [Stable_def, drop_prog_Constrains_eq]) 1);
qed "drop_prog_Stable_eq";


(*FAILS*)
Goal "modular i (Stable {s. P(s i)})";
by (full_simp_tac (simpset() addsimps [modular_def,
				       drop_prog_lift_prog_Join RS sym]) 1);
by (full_simp_tac (simpset() addsimps [lift_set_sub2 RS sym,
				      lift_prog_Stable_eq]) 1);
by Auto_tac;



Goal "modular i (Increasing (rel o sub i))";
by (full_simp_tac (simpset() addsimps [modular_def, Increasing_def,
				       drop_prog_lift_prog_Join RS sym]) 1);


Goal "modular i (lift_prog i `` X)";
by (full_simp_tac (simpset() addsimps [modular_def,
				       drop_prog_lift_prog_Join RS sym]) 1);



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


!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!;
(*Precondition is TOO STRONG*)
Goal "Cl : UNIV guar Increasing f \
\     ==>lift_prog i Cl : (lift_prog i `` UNIV) guar Increasing (f o sub i)";
by (rtac drop_prog_guarantees 1);
by (etac guarantees_weaken 1);
by Auto_tac;
by (rtac (impOfSubs image_lift_prog_Increasing) 2);
by (rtac image_eqI 1);
by (rtac (lift_prog_inverse RS sym) 1);
by (rtac (impOfSubs image_lift_prog_Increasing) 1);
by Auto_tac;
fr imageI;

by (stac (lift_set_sub2 RS sym) 1); 
by (asm_simp_tac (simpset() addsimps [lift_prog_Stable_eq]) 1);



by (full_simp_tac
    (simpset() addsimps [alloc_spec_def, alloc_safety_def, System_def]) 1);




Goal "[| F : (drop_prog i `` XX) guar Y;    \
\        ALL Z:XX. Z component (JN i:UNIV. JN G:UNIV. lift_prog i G) |] \
\     ==> lift_prog i F : XX guar (lift_prog i `` Y)";
by (rtac guaranteesI 1);
by (dtac guaranteesD 1);
by (ball_tac 1);
by (full_simp_tac (simpset() addsimps [Join_component_iff]) 1);
by (full_simp_tac (simpset() addsimps [component_eq_subset, Acts_JN]) 1);

by (rtac image_eqI 2);
by (assume_tac 3);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join RS sym]) 2);

by (rtac (drop_prog_lift_prog_Join RS sym) 1);
by (assume_tac 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join RS sym]) 1);
by (rtac image_eqI 1);
by (assume_tac 2);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);

by (rtac guaranteesI 1);
by (dtac guaranteesD 1);
by (rtac image_eqI 1);
by (rtac (drop_prog_lift_prog_Join RS sym) 1);
by (assume_tac 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join RS sym]) 1);
by (rtac image_eqI 1);
by (assume_tac 2);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);


by (dtac sym 1);
by (Blast_tac 1);


by (rtac guaranteesI 1);
by (dtac guaranteesD 1);
by (rtac image_eqI 2);
by (assume_tac 3);


Goal "F : X guar Y \
\     ==> lift_prog i F : XX guar (lift_prog i `` Y)";
by (rtac guaranteesI 1);
by (dtac guaranteesD 1);
by (rtac image_eqI 2);
by (assume_tac 3);

by Auto_tac;
by (blast_tac (claset() addDs [lift_prog_Join_eq_lift_prog_D, guaranteesD]) 1);
qed "lift_prog_guarantees";








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




Goal "[| F : (drop_prog i `` X) guar (drop_prog i `` Y);  \
\        X <= lift_prog i `` drop_prog i `` X;  \
\        Y <= lift_prog i `` drop_prog i `` Y |] \
\     ==> lift_prog i F : X guar Y";
by (rtac guaranteesI 1);
by (set_mp_tac 1);
by (ALLGOALS Clarify_tac);
by (dtac guaranteesD 1);
by (rtac image_eqI 1);
by (dres_inst_tac [("f", "drop_prog i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by (assume_tac 1);
by (ALLGOALS Clarify_tac);
by (set_mp_tac 1);
by (ALLGOALS Clarify_tac);
by Auto_tac;
by (dres_inst_tac [("f", "drop_prog i")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [drop_prog_lift_prog_Join]) 1);
by Auto_tac;
qed "drop_prog_guarantees";




(*****SINGLETON LEMMAS: GOOD FOR ANYTHING??????***)

(*Because A and B could differ outside i, cannot generalize result to 
   drop_set i (A Int B) = drop_set i A Int drop_set i B
*)
Goal "[| ALL j. j = i; f i = g i |] ==> f = g";
by (rtac ext 1);
by (dres_inst_tac [("x", "x")] spec 1);
by Auto_tac;
qed "singleton_ext";

Goalw [lift_set_def, drop_set_def]
     "ALL j. j = i ==> lift_set i (drop_set i A) = A";
by (blast_tac (claset() addSDs [singleton_ext]) 1);
qed "singleton_drop_set_inverse";

Goal "ALL j. j = i ==> f(i:= g i) = g";
by (dres_inst_tac [("x", "x")] spec 1);
by Auto_tac;
qed "singleton_update_eq";

Goalw [lift_act_def, drop_act_def]
     "ALL j. j = i ==> lift_act i (drop_act i act) = act";
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [singleton_update_eq]) 1);
by (dtac singleton_ext 1);
by (assume_tac 1);
by (auto_tac (claset() addSIs [exI, image_eqI], 
	      simpset() addsimps [singleton_update_eq]));
qed "singleton_drop_act_inverse";

Goal "ALL j. j = i ==> lift_prog i (drop_prog i F) = F";
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [singleton_drop_set_inverse]) 1);
by (asm_simp_tac (simpset() addsimps [image_compose RS sym, o_def,
				      singleton_drop_act_inverse]) 1);
qed "singleton_drop_prog_inverse";

