(*  Title:      HOL/UNITY/AllocBase
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Basis declarations for Chandy and Charpentier's Allocator

with_path "../Induct" time_use_thy "AllocBase";
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

Goal "length xs <= k --> map fst [p:zip xs [0..length xs(] . snd p < k] = xs";
by (res_inst_tac [("xs","xs")] rev_induct 1);
by Auto_tac;
qed_spec_mp "sublist_length_lemma";

Goalw [sublist_def] "sublist l {..length l(} = l";
by (simp_tac (simpset() addsimps [sublist_length_lemma]) 1);
qed "sublist_length";
