(*  Title: ZF/UNITY/Distributor
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

A multiple-client allocator from a single-client allocator:
Distributor specification
*)

Open_locale "Distributor";
val all_distinct_vars = thm "all_distinct_vars";
val var_assumes = thm "var_assumes";
val type_assumes = thm "type_assumes";
val default_val_assumes  = thm "default_val_assumes";

Addsimps [var_assumes, default_val_assumes,  type_assumes];

Goalw [state_def]
"s:state ==> s`In:list(A)";
by (dres_inst_tac [("a", "In")] apply_type 1);
by Auto_tac;
qed "In_value_type";
AddTCs [In_value_type];
Addsimps [In_value_type];

Goalw [state_def]
"s:state ==> s`iIn:list(nat)";
by (dres_inst_tac [("a", "iIn")] apply_type 1);
by Auto_tac;
qed "iIn_value_type";
AddTCs [iIn_value_type];
Addsimps [iIn_value_type];

Goalw [state_def]
"s:state ==> s`Out(n):list(A)";
by (dres_inst_tac [("a", "Out(n)")] apply_type 1);
by Auto_tac;
qed "Out_value_type";
AddTCs [Out_value_type];
Addsimps [Out_value_type];

val distrib = thm "distr_spec";

Goal "D:program";
by (cut_facts_tac [distrib] 1);
by (auto_tac (claset(), simpset() addsimps 
           [distr_spec_def, distr_allowed_acts_def]));
qed "D_in_program";
Addsimps [D_in_program];
AddTCs [D_in_program];

Goal "G:program ==> \
\   D ok G <-> \
\  ((ALL n:nat. G:preserves(lift(Out(n)))) & D:Allowed(G))";
by (cut_facts_tac [distrib] 1);
by (auto_tac (claset(), 
     simpset() addsimps [INT_iff, distr_spec_def, distr_allowed_acts_def, 
                         Allowed_def, ok_iff_Allowed]));
by (rotate_tac ~1 2);
by (dres_inst_tac [("x", "G")] bspec 2);
by Auto_tac;
by (dresolve_tac [rotate_prems 1 (safety_prop_Acts_iff RS iffD1)] 1);
by (auto_tac (claset() addIs [safety_prop_Inter], simpset()));
qed "D_ok_iff";

Goal 
"D : ((lift(In) IncreasingWrt prefix(A)/list(A)) Int \
\     (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) Int \
\     Always({s:state. ALL elt:set_of_list(s`iIn). elt<Nclients})) \
\     guarantees \
\         (INT n: Nclients. lift(Out(n)) IncreasingWrt \
\                           prefix(A)/list(A))";
by (cut_facts_tac [D_in_program, distrib] 1);
by (full_simp_tac (simpset() addsimps [distr_spec_def, distr_follows_def]) 1); 
by (auto_tac (claset() addSIs [guaranteesI]  addIs [Follows_imp_Increasing_left]
                        addSDs [guaranteesD], 
               simpset() addsimps []));
qed "distr_Increasing_Out";

val state_AlwaysI2 = state_AlwaysI RS Always_weaken;

Goal
"[| ALL n:nat. G:preserves(lift(Out(n))); \
\  D Join G:Always({s:state. \
\         ALL elt:set_of_list(s`iIn). elt < Nclients}) |] \
\ ==> D Join G : Always \
\         ({s:state. msetsum(%n. bag_of (sublist(s`In, \
\                      {k:nat. k < length(s`iIn) &\
\                         nth(k, s`iIn)= n})), \
\                        Nclients, A) = \
\             bag_of(sublist(s`In, length(s`iIn)))})";
by (cut_facts_tac [D_in_program] 1);
by (subgoal_tac "G:program" 1);
by (blast_tac (claset() addDs [preserves_type RS subsetD]) 2);
by (etac ([asm_rl, state_AlwaysI2] MRS (Always_Diff_Un_eq RS iffD1)) 1);
by Auto_tac;
by (stac (bag_of_sublist_UN_disjoint RS sym) 1); 
by (asm_simp_tac (simpset() addsimps [nat_into_Finite]) 1); 
by (Blast_tac 1); 
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [set_of_list_conv_nth]) 1); 
by (subgoal_tac
    "(UN i: Nclients. {k:nat. k < length(x`iIn) & nth(k, x`iIn) = i}) = \
\    length(x`iIn)" 1);
by (Asm_simp_tac 1);
by (resolve_tac [equalityI] 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [ltD]) 1);
by (subgoal_tac "length(x ` iIn) : nat" 1);
by Typecheck_tac; 
by (subgoal_tac "xa : nat" 1); 
by (dres_inst_tac [("x", "nth(xa, x`iIn)"),("P","%elt. ?X(elt) --> elt<Nclients")] bspec  1);
by (asm_full_simp_tac (simpset() addsimps [ltI, nat_into_Ord]) 1); 
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [Ord_mem_iff_lt]))); 
by (blast_tac (claset() addDs [ltD]) 1); 
by (blast_tac (claset() addIs [lt_trans]) 1);
qed "distr_bag_Follows_lemma";


val prems =
Goal "[|A=A'; r=r'; !!x. x:state ==> f(x)=f'(x); !!x. x:state ==> g(x)=g'(x)|] ==> Follows(A, r, f, g) = Follows(A', r', f', g')";
by (asm_full_simp_tac (simpset() addsimps [Increasing_def,Follows_def]@prems) 1);
qed "Follows_cong";
(*????????????????*)

Goal
 "D : ((lift(In) IncreasingWrt prefix(A)/list(A)) Int \
\      (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) Int  \
\       Always({s:state. ALL elt: set_of_list(s`iIn). elt < Nclients})) \
\     guarantees  \
\      (INT n: Nclients. \
\       (%s. msetsum(%i. bag_of(s`Out(i)),  Nclients, A)) \
\       Fols \
\       (%s. bag_of(sublist(s`In, length(s`iIn)))) \
\       Wrt MultLe(A, r)/Mult(A))";
by (cut_facts_tac [distrib] 1);
by (rtac guaranteesI 1);
by (Clarify_tac 1); 
by (Simp_tac 2);
by (rtac (distr_bag_Follows_lemma RS Always_Follows2) 1);
by Auto_tac;  
by (rtac Follows_state_ofD1 2);
by (rtac Follows_msetsum_UN 2);
by (ALLGOALS(Clarify_tac));
by (resolve_tac [conjI] 3);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct1] 3);
by (resolve_tac [conjI] 4);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct2] 4);
by (resolve_tac [conjI] 5);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct1] 5);
by (resolve_tac [inst "A" "A" bag_of_multiset RS conjunct2] 6);
by (Clarify_tac 4);
by (asm_full_simp_tac (simpset() addsimps []) 3);
by (asm_full_simp_tac (simpset() addsimps []) 3);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [nat_into_Finite])));
by (rotate_tac 2 1);
by (asm_full_simp_tac (simpset() addsimps [D_ok_iff]) 1);
by (auto_tac (claset(), 
              simpset() addsimps [distr_spec_def, distr_follows_def]));
by (dtac guaranteesD 1); 
by (assume_tac 1);
by (force_tac (claset(), simpset() addsimps []) 1); 
by (force_tac (claset(), simpset() addsimps []) 1); 
by (asm_full_simp_tac
    (simpset() addsimps [rewrite_rule [comp_def] (mono_bag_of RS subset_Follows_comp RS subsetD), 
             refl_prefix, trans_on_MultLe] 
            addcongs [Follows_cong]) 1); 
qed  "distr_bag_Follows";
Close_locale "Distributor";
