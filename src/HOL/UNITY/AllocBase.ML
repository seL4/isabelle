(*  Title:      HOL/UNITY/AllocBase
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Basis declarations for Chandy and Charpentier's Allocator

add_path "../Induct";
time_use_thy "AllocBase";
*)

Goal "(ALL i. i<n --> f i <= (g i :: nat)) --> sum_below f n <= sum_below g n";
by (induct_tac "n" 1);
by Auto_tac;
by (dres_inst_tac [("x","n")] spec 1);
by Auto_tac;
by (arith_tac 1);
qed_spec_mp "sum_mono";

Goal "ALL xs. xs <= ys --> tokens xs <= tokens ys";
by (induct_tac "ys" 1);
by (auto_tac (claset(), simpset() addsimps [prefix_Cons]));
qed_spec_mp "tokens_mono_prefix";

Goalw [mono_def] "mono tokens";
by (blast_tac (claset() addIs [tokens_mono_prefix]) 1);
qed "mono_tokens";


(*** sublist ***)

Goalw [sublist_def] "sublist l {} = []";
by Auto_tac;
qed "sublist_empty";

Goalw [sublist_def] "sublist [] A = []";
by Auto_tac;
qed "sublist_nil";

Goal "map fst [p:zip xs [i..i + length xs(] . snd p : A] =     \
\     map fst [p:zip xs [0..length xs(] . snd p + i : A]";
by (res_inst_tac [("xs","xs")] rev_induct 1);
 by (asm_simp_tac (simpset() addsimps [add_commute]) 2);
by (Simp_tac 1);
qed "sublist_shift_lemma";

Goalw [sublist_def]
     "sublist (l@l') A = sublist l A @ sublist l' {j. j + length l : A}";
by (res_inst_tac [("xs","l'")] rev_induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [inst "i" "0" upt_add_eq_append, 
	                              zip_append, sublist_shift_lemma]) 1);
by (asm_simp_tac (simpset() addsimps [add_commute]) 1);
qed "sublist_append";

Addsimps [sublist_empty, sublist_nil];

Goal "sublist (x#l) A = (if 0:A then [x] else []) @ sublist l {j. Suc j : A}";
by (res_inst_tac [("xs","l")] rev_induct 1);
 by (asm_simp_tac (simpset() delsimps [append_Cons]
	 		     addsimps [append_Cons RS sym, sublist_append]) 2);
by (simp_tac (simpset() addsimps [sublist_def]) 1);
qed "sublist_Cons";

Goal "sublist [x] A = (if 0 : A then [x] else [])";
by (simp_tac (simpset() addsimps [sublist_Cons]) 1);
qed "sublist_singleton";
Addsimps [sublist_singleton];

Goal "sublist l {..n(} = take n l";
by (res_inst_tac [("xs","l")] rev_induct 1);
 by (asm_simp_tac (simpset() addsplits [nat_diff_split]
                             addsimps [sublist_append]) 2);
by (Simp_tac 1);
qed "sublist_upt_eq_take";
Addsimps [sublist_upt_eq_take];


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

Goal "finite A ==> \
\     setsum (%i. if i < Suc(length zs) then {#(zs @ [z]) ! i#} else {#}) A = \
\       setsum (%i. if i < length zs then {#zs ! i#} else {#}) A + \
\       (if length zs : A then {#z#} else {#})";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps (nth_append :: thms "plus_ac0")) 1);
by (subgoal_tac "x < Suc (length zs) & ~ x < length zs --> length zs = x" 1);
by Auto_tac;
qed "bag_of_sublist_lemma";


Goal "finite A \
\     ==> bag_of (sublist l A) = \
\         setsum (%i. if i < length l then {# nth l i #} else {#}) A";
by (res_inst_tac [("xs","l")] rev_induct 1);
by (Simp_tac 1);
by (stac (symmetric Zero_def) 1);
by (etac (setsum_0 RS sym) 1);
by (asm_simp_tac (simpset() addsimps [sublist_append, 
				      bag_of_sublist_lemma]) 1);
qed "bag_of_sublist";


Goal "[| finite A; finite B |] \
\     ==> bag_of (sublist l (A Un B)) + bag_of (sublist l (A Int B)) = \
\         bag_of (sublist l A) + bag_of (sublist l B)";
by (asm_simp_tac (simpset() addsimps [bag_of_sublist, setsum_Un_Int]) 1);
qed "bag_of_sublist_Un_Int";
