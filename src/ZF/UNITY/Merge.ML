(*  Title: ZF/UNITY/Merge
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

A multiple-client allocator from a single-client allocator:
Merge specification
*)
Open_locale "Merge";
val all_distinct_vars = thm "all_distinct_vars";
val var_assumes = thm "var_assumes";
val type_assumes = thm "type_assumes";
val default_val_assumes  = thm "default_val_assumes";

Addsimps [var_assumes, default_val_assumes,  type_assumes];

Goalw [state_def]
"s \\<in> state ==> s`In(n):list(A)";
by (dres_inst_tac [("a", "In(n)")] apply_type 1);
by Auto_tac;
qed "In_value_type";
AddTCs [In_value_type];
Addsimps [In_value_type];

Goalw [state_def]
"s \\<in> state ==> s`Out \\<in> list(A)";
by (dres_inst_tac [("a", "Out")] apply_type 1);
by Auto_tac;
qed "Out_value_type";
AddTCs [Out_value_type];
Addsimps [Out_value_type];

Goalw [state_def]
"s \\<in> state ==> s`iOut \\<in> list(nat)";
by (dres_inst_tac [("a", "iOut")] apply_type 1);
by Auto_tac;
qed "Out_value_type";
AddTCs [Out_value_type];
Addsimps [Out_value_type];


val merge = thm "merge_spec";

Goal "M \\<in> program";
by (cut_facts_tac [merge] 1);
by (auto_tac (claset() addDs [guarantees_type RS subsetD], 
              simpset() addsimps [merge_spec_def, merge_increasing_def]));
qed "M_in_program";
Addsimps [M_in_program];
AddTCs [M_in_program];

Goal 
"Allowed(M) = (preserves(lift(Out)) Int preserves(lift(iOut)))";
by (cut_facts_tac [merge, inst "v"  "lift(Out)" preserves_type] 1);
by (auto_tac (claset(), simpset() addsimps 
         [merge_spec_def, merge_allowed_acts_def, 
          Allowed_def,  safety_prop_Acts_iff]));
qed "merge_Allowed";

Goal 
"G \\<in> program ==> \
\ M ok G <-> (G \\<in> preserves(lift(Out)) &  \
\      G \\<in> preserves(lift(iOut)) & M \\<in> Allowed(G))";
by (cut_facts_tac [merge] 1); 
by (auto_tac (claset(), simpset() 
         addsimps [merge_Allowed, ok_iff_Allowed]));  
qed "M_ok_iff";

Goal
"[| G \\<in> preserves(lift(Out)); G \\<in> preserves(lift(iOut)); \
\  M \\<in> Allowed(G) |] ==> \
\ M Join G \\<in> Always({s \\<in> state. length(s`Out)=length(s`iOut)})";
by (ftac (preserves_type RS subsetD) 1);
by (subgoal_tac "G \\<in> program" 1);
by (assume_tac 2);
by (ftac M_ok_iff 1);
by (cut_facts_tac [merge] 1);
by (force_tac (claset() addDs [guaranteesD], 
               simpset() addsimps [merge_spec_def, merge_eq_Out_def]) 1); 
qed "merge_Always_Out_eq_iOut";

Goal 
"[| G \\<in> preserves(lift(iOut)); G \\<in> preserves(lift(Out)); \
\   M \\<in> Allowed(G) |] ==> \
\ M Join G: Always({s \\<in> state. \\<forall>elt \\<in> set_of_list(s`iOut). elt<Nclients})";
by (ftac (preserves_type RS subsetD) 1);
by (ftac M_ok_iff 1);
by (cut_facts_tac [merge] 1);
by (force_tac (claset() addDs [guaranteesD], 
               simpset() addsimps [merge_spec_def, merge_bounded_def]) 1); 
qed "merge_Bounded";

Goal 
"[| G \\<in> preserves(lift(iOut)); \
\   G: preserves(lift(Out)); M \\<in> Allowed(G) |] \
\ ==> M Join G : Always \
\   ({s \\<in> state. msetsum(%i. bag_of(sublist(s`Out, \
\     {k \\<in> nat. k < length(s`iOut) & nth(k, s`iOut)=i})), \
\                  Nclients, A) = bag_of(s`Out)})";
by (rtac ([[merge_Always_Out_eq_iOut, merge_Bounded] MRS Always_Int_I,
           state_AlwaysI RS Always_weaken] MRS (Always_Diff_Un_eq RS iffD1)) 1)
;
by Auto_tac; 
by (stac (bag_of_sublist_UN_disjoint RS sym) 1); 
by (auto_tac (claset(), simpset() 
              addsimps [nat_into_Finite, set_of_list_conv_nth])); 
by (subgoal_tac
    "(\\<Union>i \\<in> Nclients. {k \\<in> nat. k < length(x`iOut) & nth(k, x`iOut) = i}) = length(x`iOut)" 1);
by Auto_tac;
by (resolve_tac [equalityI] 1);
by (blast_tac (claset() addDs [ltD]) 1); 
by (Clarify_tac 1); 
by (subgoal_tac "length(x ` iOut) : nat" 1);
by (Asm_full_simp_tac 2);
by (subgoal_tac "xa : nat" 1); 
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [Ord_mem_iff_lt]))); 
by (blast_tac (claset() addIs [lt_trans]) 2);
by (dres_inst_tac [("x", "nth(xa, x`iOut)"),("P","%elt. ?X(elt) --> elt<Nclients")] bspec 1);
by (asm_full_simp_tac (simpset() addsimps [ltI, nat_into_Ord]) 1); 
by (blast_tac (claset() addDs [ltD]) 1); 
qed "merge_bag_Follows_lemma";

Goal
"M : (\\<Inter>n \\<in> Nclients. lift(In(n)) IncreasingWrt prefix(A)/list(A)) \
\       guarantees  \
\ (%s. bag_of(s`Out)) Fols \
\ (%s. msetsum(%i. bag_of(s`In(i)),Nclients, A)) Wrt MultLe(A, r)/Mult(A)";
by (cut_facts_tac [merge] 1);
by (rtac (merge_bag_Follows_lemma RS Always_Follows1 RS guaranteesI) 1);
by (ALLGOALS(rotate_tac ~1 ));
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [M_ok_iff])));
by Auto_tac;
by (rtac Follows_state_ofD1 1);
by (rtac Follows_msetsum_UN 1);
by (ALLGOALS(Clarify_tac));
by (resolve_tac [conjI] 2);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct1] 2);
by (resolve_tac [conjI] 3);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct2] 3);
by (resolve_tac [conjI] 4);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct1] 4);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct2] 5);
by (ALLGOALS(Asm_simp_tac));
by (resolve_tac [nat_into_Finite] 2);
by (Asm_simp_tac 2);
by (asm_full_simp_tac (simpset() addsimps [INT_iff,
                      merge_spec_def, merge_follows_def]) 1);
by Auto_tac;
by (cut_facts_tac [merge] 1);
by (subgoal_tac "M ok G" 1);
by (dtac guaranteesD 1); 
by (assume_tac 1);
by (force_tac (claset() addIs[M_ok_iff RS iffD2], simpset()) 4);
by (rewrite_goal_tac [merge_spec_def, merge_follows_def] 1);
by (Blast_tac 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [rewrite_rule [comp_def] (mono_bag_of RS subset_Follows_comp RS subsetD), 
             refl_prefix, trans_on_MultLe] 
            addcongs [Follows_cong]) 1); 
qed "merge_bag_Follows";
Close_locale "Merge";

