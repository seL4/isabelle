(*  Title:      HOL/UNITY/AllocImpl
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Implementation of a multiple-client allocator from a single-client allocator

add_path "../Induct";
time_use_thy "AllocImpl";
*)

AddIs [impOfSubs subset_preserves_o];
Addsimps [funPair_o_distrib];
Addsimps [Always_INT_distrib];
Delsimps [o_apply];

(*Eliminate the "o" operator*)
val o_simp = simplify (simpset() addsimps [o_def]);

Goalw [merge_spec_def,merge_eqOut_def]
     "[| M: merge_spec; G: preserves merge.Out; G: preserves merge.iOut |] \
\ ==> M Join G : Always {s. length (merge.Out s) = length (merge.iOut s)}";  
by (force_tac (claset() addDs [guaranteesD], simpset()) 1);
qed "Merge_Always_Out_eq_iOut";


Goal "M : merge_spec \
\ ==> M : (INT i: lessThan Nclients. Increasing (sub i o merge.In)) \
\             guarantees[funPair merge.Out merge.iOut]  \
\                (bag_of o merge.Out) Fols \
\                (%s. setsum (%i. (bag_of o sub i o merge.In) s) \
\                            (lessThan Nclients))";
by (rtac guaranteesI 1);
by (res_inst_tac [("f", "%s. bag_of (sublist (merge.Out s) {..length(merge.iOut s)(})")] 
                  Always_Follows 1);
by (etac (Merge_Always_Out_eq_iOut RS Always_Compl_Un_eq RS iffD1) 1);
by (force_tac (claset() addIs [UNIV_AlwaysI], simpset() addsimps [o_apply]) 3);
by (Asm_full_simp_tac 1); 
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() delsimps [sublist_upt_eq_take]
                                 addsimps [bag_of_sublist]) 1); 
by (rtac Follows_trans 1); 
by (rtac Follows_setsum 2);
by (asm_full_simp_tac (simpset() addsimps []) 3);
by (Clarify_tac 2); 
by (asm_full_simp_tac (simpset() addsimps [o_assoc RS sym]) 2); 
by (rtac (impOfSubs (mono_bag_of RS mono_Follows_o)) 2);

(*Now need to invoke the merge_follows guarantee*)
 
by (asm_full_simp_tac (simpset() addsimps [merge_spec_def,merge_follows_def]) 2); 


by (res_inst_tac [("f", "%s. bag_of (sublist (merge.Out s) {..length(merge.iOut s)(})")] 
                  Always_Follows 1);

setsum (%i. if i < length l then {# nth l i #} else {#}) {..length (iOut s)(}

             : (%s. bag_of
                     (sublist (merge.Out s) {..length (iOut s)(})) Fols
               (%s. setsum (%i. (bag_of o sub i o merge.In) s)
                     {..Nclients(})


	  (%s. sublist (merge.Out s) 
                       {k. k < size(merge.iOut s) & nth(merge.iOut s)k = i})
	  Fols (sub i o merge.In))"


by Auto_tac;
by (dtac guaranteesD 1);
by Auto_tac;
by (rtac guaranteesI 1);

merge_eqOut

Always_Int_eq


by (simp_tac (simpset() addsimps [o_def]) 1);
by (subgoal_tac
    "ALL s. merge.Out s = sublist (merge.Out s) {..length(merge.iOut s)(}" 1);
by (etac ssubst 1);
by (asm_simp_tac (simpset() addsimps [bag_of_sublist]) 1);
by (stac bag_of_sublist 1);

