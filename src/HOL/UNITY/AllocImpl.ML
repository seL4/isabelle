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

Goalw [merge_spec_def,merge_eqOut_def]
     "[| M: merge_spec; G: preserves merge.Out; G: preserves merge.iOut |] \
\ ==> M Join G : Always {s. length (merge.Out s) = length (merge.iOut s)}";  
by (force_tac (claset() addDs [guaranteesD], simpset()) 1);
qed "Merge_Always_Out_eq_iOut";

Goalw [merge_spec_def,merge_bounded_def]
     "[| M: merge_spec; G: preserves merge.iOut |] \
\ ==> M Join G : Always {s. ALL elt : set (merge.iOut s). elt < Nclients}";  
by (force_tac (claset() addDs [guaranteesD], simpset()) 1);
qed "Merge_Bounded";

Goal "[| M : merge_spec;  G : preserves (funPair merge.Out iOut) |] \
\ ==> M Join G : Always \
\         {s. setsum (%i. bag_of (sublist (merge.Out s) \
\                                 {k. k < length (iOut s) & iOut s ! k = i})) \
\                    (lessThan Nclients)   =  \
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

Goal "M : merge_spec \
\ ==> M : (INT i: lessThan Nclients. Increasing (sub i o merge.In)) \
\             guarantees[funPair merge.Out merge.iOut]  \
\                (bag_of o merge.Out) Fols \
\                (%s. setsum (%i. (bag_of o sub i o merge.In) s) \
\                            (lessThan Nclients))";
by (rtac (Merge_Bag_Follows_lemma RS Always_Follows1 RS guaranteesI) 1);
by Auto_tac;
by (rtac Follows_setsum 1);
by (auto_tac (claset(), 
              simpset() addsimps [merge_spec_def,merge_follows_def, o_def]));
by (best_tac (claset() addIs [impOfSubs (mono_bag_of RS mono_Follows_apply)]
                       addDs [guaranteesD]) 1);
qed "Merge_Bag_Follows";

(*Declare a locale for M : merge_spec and 
  G : preserves (funPair merge.Out iOut)? *)



(** Distributor **)
	 
Goalw [distr_follows_def]
     "D : distr_follows \
\ ==> D : Increasing distr.In Int Increasing distr.iIn Int \
\        Always {s. ALL elt : set (distr.iIn s). elt < Nclients} \
\        guarantees[distr.Out] \
\        (INT i : lessThan Nclients. Increasing (sub i o distr.Out))";
by (blast_tac (claset() addIs [guaranteesI, Follows_Increasing1]
                        addDs [guaranteesD]) 1);
qed "Distr_Increasing_Out";


Goal "[| G : preserves distr.Out; \
\        D Join G : Always {s. ALL elt: set (distr.iIn s). elt < Nclients} |] \
\ ==> D Join G : Always \
\         {s. setsum (%i. bag_of (sublist (distr.In s) \
\                                 {k. k < length (iIn s) & iIn s ! k = i})) \
\                    (lessThan Nclients)   = \
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


Goal "D : distr_follows \
\ ==> D : Increasing distr.In Int Increasing distr.iIn Int \
\     Always {s. ALL elt : set (distr.iIn s). elt < Nclients} \
\     guarantees[distr.Out] \
\      (INT i : lessThan Nclients. \
\       (%s. setsum (%i. (bag_of o sub i o distr.Out) s) (lessThan Nclients)) \
\       Fols \
\       (%s. bag_of (sublist (distr.In s) (lessThan (length(distr.iIn s))))))";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (rtac (Distr_Bag_Follows_lemma RS Always_Follows2) 1);
by Auto_tac;
by (rtac Follows_setsum 1);
by (auto_tac (claset(), 
              simpset() addsimps [distr_follows_def, o_def]));
by (best_tac (claset() addIs [impOfSubs (mono_bag_of RS mono_Follows_apply)]
                       addDs [guaranteesD]) 1);
qed "Distr_Bag_Follows";

(*
(INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int
	                             Increasing (sub i o allocRel))
         Int
         Always {s. ALL i. i<Nclients -->
		     (ALL elt : set ((sub i o allocAsk) s). elt <= NbT)}
         Int
         (INT i : lessThan Nclients. 
	  INT h. {s. h <= (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}
		 LeadsTo
	         {s. tokens h <= (tokens o sub i o allocRel)s})
<=
(INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int
	                             Increasing (sub i o allocRel))
         Int
         Always {s. ALL i. i<Nclients -->
		     (ALL elt : set ((sub i o allocAsk) s). elt <= NbT)}
         Int
         (INT h. {s. h <= (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}
		 LeadsTo
	         {s. tokens h <= (tokens o sub i o allocRel)s})
*)
