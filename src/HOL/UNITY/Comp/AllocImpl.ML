(*  Title:      HOL/UNITY/AllocImpl
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Implementation of a multiple-client allocator from a single-client allocator
*)

AddIs [impOfSubs subset_preserves_o];
Addsimps [funPair_o_distrib];
Addsimps [Always_INT_distrib];
Delsimps [o_apply];

Open_locale "Merge";

val Merge = thm "Merge_spec";

Goal "Allowed M = (preserves merge.Out) Int (preserves merge.iOut)";
by (cut_facts_tac [Merge] 1);
by (auto_tac (claset(), 
              simpset() addsimps [merge_spec_def, merge_allowed_acts_def, 
                                  Allowed_def, safety_prop_Acts_iff]));  
qed "Merge_Allowed";

Goal "M ok G = (G: preserves merge.Out & G: preserves merge.iOut & \
\                    M : Allowed G)";
by (auto_tac (claset(), simpset() addsimps [Merge_Allowed, ok_iff_Allowed]));  
qed "M_ok_iff";
AddIffs [M_ok_iff];

Goal "[| G: preserves merge.Out; G: preserves merge.iOut; M : Allowed G |] \
\     ==> M Join G : Always {s. length (merge.Out s) = length (merge.iOut s)}";
by (cut_facts_tac [Merge] 1);
by (force_tac (claset() addDs [guaranteesD], 
               simpset() addsimps [merge_spec_def, merge_eqOut_def]) 1); 
qed "Merge_Always_Out_eq_iOut";

Goal "[| G: preserves merge.iOut; G: preserves merge.Out; M : Allowed G |] \
\     ==> M Join G: Always {s. ALL elt : set (merge.iOut s). elt < Nclients}";
by (cut_facts_tac [Merge] 1);
by (force_tac (claset() addDs [guaranteesD], 
               simpset() addsimps [merge_spec_def, merge_bounded_def]) 1); 
qed "Merge_Bounded";

Goal "[| G: preserves merge.iOut; G: preserves merge.Out; M : Allowed G |] \
\ ==> M Join G : Always \
\         {s. (\\<Sum>i: lessThan Nclients. bag_of (sublist (merge.Out s) \
\                                 {k. k < length (iOut s) & iOut s ! k = i})) = \
\             (bag_of o merge.Out) s}";
by (rtac ([[Merge_Always_Out_eq_iOut, Merge_Bounded] MRS Always_Int_I,
	   UNIV_AlwaysI] MRS (Always_Compl_Un_eq RS iffD1)) 1);
     by Auto_tac; 
by (stac (bag_of_sublist_UN_disjoint RS sym) 1); 
  by (Simp_tac 1);
 by (Blast_tac 1); 
by (asm_full_simp_tac (simpset() addsimps [set_conv_nth]) 1); 
by (subgoal_tac
    "(UN i:lessThan Nclients. {k. k < length (iOut x) & iOut x ! k = i}) = \
\    lessThan (length (iOut x))" 1);
 by (Blast_tac 2); 
by (asm_simp_tac (simpset() addsimps [o_def]) 1); 
qed "Merge_Bag_Follows_lemma";

Goal "M : (INT i: lessThan Nclients. Increasing (sub i o merge.In)) \
\         guarantees  \
\            (bag_of o merge.Out) Fols \
\            (%s. \\<Sum>i: lessThan Nclients. (bag_of o sub i o merge.In) s)";
by (rtac (Merge_Bag_Follows_lemma RS Always_Follows1 RS guaranteesI) 1);
by Auto_tac;  
by (rtac Follows_setsum 1);
by (cut_facts_tac [Merge] 1);
by (auto_tac (claset(), 
              simpset() addsimps [merge_spec_def, merge_follows_def, o_def]));
by (dtac guaranteesD 1); 
by (best_tac
    (claset() addIs [impOfSubs (mono_bag_of RS mono_Follows_apply)]) 3);
by Auto_tac;  
qed "Merge_Bag_Follows";

Close_locale "Merge";


(** Distributor **)

Open_locale "Distrib";

val Distrib = thm "Distrib_spec";
  

Goal "D : Increasing distr.In Int Increasing distr.iIn Int \
\         Always {s. ALL elt : set (distr.iIn s). elt < Nclients} \
\         guarantees \
\         (INT i : lessThan Nclients. Increasing (sub i o distr.Out))";
by (cut_facts_tac [Distrib] 1);
by (full_simp_tac (simpset() addsimps [distr_spec_def, distr_follows_def]) 1); 
by (Clarify_tac 1); 
by (blast_tac (claset() addIs [guaranteesI, Follows_Increasing1]
                        addDs [guaranteesD]) 1);
qed "Distr_Increasing_Out";

Goal "[| G : preserves distr.Out; \
\        D Join G : Always {s. ALL elt: set (distr.iIn s). elt < Nclients} |] \
\ ==> D Join G : Always \
\         {s. (\\<Sum>i: lessThan Nclients. bag_of (sublist (distr.In s) \
\                                 {k. k < length (iIn s) & iIn s ! k = i})) = \
\             bag_of (sublist (distr.In s) (lessThan (length (iIn s))))}";
by (etac ([asm_rl, UNIV_AlwaysI] MRS (Always_Compl_Un_eq RS iffD1)) 1);
by Auto_tac; 
by (stac (bag_of_sublist_UN_disjoint RS sym) 1); 
  by (Simp_tac 1);
 by (Blast_tac 1); 
by (asm_full_simp_tac (simpset() addsimps [set_conv_nth]) 1); 
by (subgoal_tac
    "(UN i:lessThan Nclients. {k. k < length (iIn x) & iIn x ! k = i}) = \
\    lessThan (length (iIn x))" 1);
 by (Blast_tac 2); 
by (Asm_simp_tac 1); 
qed "Distr_Bag_Follows_lemma";

Goal "D ok G = (G: preserves distr.Out & D : Allowed G)";
by (cut_facts_tac [Distrib] 1);
by (auto_tac (claset(), 
     simpset() addsimps [distr_spec_def, distr_allowed_acts_def, 
                         Allowed_def, safety_prop_Acts_iff, ok_iff_Allowed]));
qed "D_ok_iff";
AddIffs [D_ok_iff];

Goal
 "D : Increasing distr.In Int Increasing distr.iIn Int \
\     Always {s. ALL elt : set (distr.iIn s). elt < Nclients} \
\     guarantees  \
\      (INT i : lessThan Nclients. \
\       (%s. \\<Sum>i: lessThan Nclients. (bag_of o sub i o distr.Out) s) \
\       Fols \
\       (%s. bag_of (sublist (distr.In s) (lessThan (length(distr.iIn s))))))";
by (rtac guaranteesI 1);
by (Clarify_tac 1); 
by (rtac (Distr_Bag_Follows_lemma RS Always_Follows2) 1);
by Auto_tac;  
by (rtac Follows_setsum 1);
by (cut_facts_tac [Distrib] 1);
by (auto_tac (claset(), 
              simpset() addsimps [distr_spec_def, distr_follows_def, o_def]));
by (dtac guaranteesD 1); 
by (best_tac (claset() addIs [impOfSubs (mono_bag_of RS mono_Follows_apply)]) 3);
by Auto_tac;  
qed "Distr_Bag_Follows";

Close_locale "Distrib";


Goal "!!f::nat=>nat. (INT i: lessThan n. {s. f i <= g i s})  \
\     <= {s. (\\<Sum>i: lessThan n. f i) <= (\\<Sum>i: lessThan n. g i s)}";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [lessThan_Suc]));
qed "alloc_refinement_lemma";

Goal
"(INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int  \
\                            Increasing (sub i o allocRel))     \
\ Int   \
\ Always {s. ALL i. i<Nclients -->      \
\             (ALL elt : set ((sub i o allocAsk) s). elt <= NbT)}       \
\ Int   \
\ (INT i : lessThan Nclients.   \
\  INT h. {s. h <= (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}  \
\          LeadsTo {s. tokens h <= (tokens o sub i o allocRel)s})        \
\ <=     \
\(INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int  \
\                            Increasing (sub i o allocRel))     \
\ Int   \
\ Always {s. ALL i. i<Nclients -->      \
\             (ALL elt : set ((sub i o allocAsk) s). elt <= NbT)}       \
\ Int   \
\ (INT hf. (INT i : lessThan Nclients.  \
\        {s. hf i <= (sub i o allocGiv)s & hf i pfixGe (sub i o allocAsk)s}) \
\ LeadsTo {s. (\\<Sum>i: lessThan Nclients. tokens (hf i)) <=         \
\   (\\<Sum>i: lessThan Nclients. (tokens o sub i o allocRel)s)})";
by (auto_tac (claset(), simpset() addsimps [ball_conj_distrib]));  
by (rename_tac "F hf" 1);
by (rtac ([Finite_stable_completion, alloc_refinement_lemma]
          MRS LeadsTo_weaken_R) 1);
  by (Blast_tac 1); 
 by (Blast_tac 1); 
by (subgoal_tac "F : Increasing (tokens o (sub i o allocRel))" 1);
 by (blast_tac
     (claset() addIs [impOfSubs (mono_tokens RS mono_Increasing_o)]) 2);
by (asm_full_simp_tac (simpset() addsimps [Increasing_def, o_assoc]) 1);
qed "alloc_refinement";


