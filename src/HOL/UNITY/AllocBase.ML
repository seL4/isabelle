(*  Title:      HOL/UNITY/AllocBase
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Basis declarations for Chandy and Charpentier's Allocator

add_path "../Induct";
time_use_thy "AllocBase";
*)

Goal "!!f :: nat=>nat. \
\     (ALL i. i<n --> f i <= g i) --> \
\     setsum f (lessThan n) <= setsum g (lessThan n)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [lessThan_Suc]));
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1);
qed_spec_mp "setsum_fun_mono";

Goal "ALL xs. xs <= ys --> tokens xs <= tokens ys";
by (induct_tac "ys" 1);
by (auto_tac (claset(), simpset() addsimps [prefix_Cons]));
qed_spec_mp "tokens_mono_prefix";

Goalw [mono_def] "mono tokens";
by (blast_tac (claset() addIs [tokens_mono_prefix]) 1);
qed "mono_tokens";


(** bag_of **)

Goal "bag_of (l@l') = bag_of l + bag_of l'";
by (induct_tac "l" 1);
 by (asm_simp_tac (simpset() addsimps (thms "plus_ac0")) 2);
by (Simp_tac 1);
qed "bag_of_append";
Addsimps [bag_of_append];

Goal "mono (bag_of :: 'a list => ('a::order) multiset)";
by (rtac monoI 1); 
by (rewtac prefix_def);
by (etac genPrefix.induct 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [union_le_mono]) 1); 
by (etac order_trans 1); 
by (rtac union_upper1 1); 
qed "mono_bag_of";

(** setsum **)

Addcongs [setsum_cong];

Goal "setsum (%i. {#if i<k then f i else g i#}) (A Int lessThan k) = \
\     setsum (%i. {#f i#}) (A Int lessThan k)";
by (rtac setsum_cong 1);
by Auto_tac;  
qed "bag_of_sublist_lemma";

Goal "bag_of (sublist l A) = \
\     setsum (%i. {# l!i #}) (A Int lessThan (length l))";
by (res_inst_tac [("xs","l")] rev_induct 1);
by (Simp_tac 1);
by (asm_simp_tac
    (simpset() addsimps [sublist_append, Int_insert_right, lessThan_Suc, 
                    nth_append, bag_of_sublist_lemma] @ thms "plus_ac0") 1);
qed "bag_of_sublist";


Goal "bag_of (sublist l (A Un B)) + bag_of (sublist l (A Int B)) = \
\     bag_of (sublist l A) + bag_of (sublist l B)";
by (subgoal_tac "A Int B Int {..length l(} = \
\                (A Int {..length l(}) Int (B Int {..length l(})" 1);
by (asm_simp_tac (simpset() addsimps [bag_of_sublist, Int_Un_distrib2, 
                                      setsum_Un_Int]) 1);
by (Blast_tac 1);
qed "bag_of_sublist_Un_Int";

Goal "A Int B = {} \
\     ==> bag_of (sublist l (A Un B)) = \
\         bag_of (sublist l A) + bag_of (sublist l B)"; 
by (asm_simp_tac (simpset() addsimps [bag_of_sublist_Un_Int RS sym]) 1);
qed "bag_of_sublist_Un_disjoint";

Goal "[| finite I; ALL i:I. ALL j:I. i~=j --> A i Int A j = {} |] \
\     ==> bag_of (sublist l (UNION I A)) =  \
\         setsum (%i. bag_of (sublist l (A i))) I";  
by (asm_simp_tac (simpset() delsimps UN_simps addsimps (UN_simps RL [sym])
			    addsimps [bag_of_sublist]) 1);
by (stac setsum_UN_disjoint 1);
by Auto_tac;  
qed_spec_mp "bag_of_sublist_UN_disjoint";
