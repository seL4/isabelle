(*  Title:      HOL/Ord.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The type class for ordered types
*)

(** mono **)

val [prem] = goalw Ord.thy [mono_def]
    "[| !!A B. A <= B ==> f(A) <= f(B) |] ==> mono(f)";
by (REPEAT (ares_tac [allI, impI, prem] 1));
qed "monoI";

val [major,minor] = goalw Ord.thy [mono_def]
    "[| mono(f);  A <= B |] ==> f(A) <= f(B)";
by (rtac (major RS spec RS spec RS mp) 1);
by (rtac minor 1);
qed "monoD";


section "Orders";

AddIffs [order_refl];

(*This form is useful with the classical reasoner*)
goal Ord.thy "!!x::'a::order. x = y ==> x <= y";
by (etac ssubst 1);
by (rtac order_refl 1);
qed "order_eq_refl";

goal Ord.thy "~ x < (x::'a::order)";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
qed "order_less_irrefl";
AddIffs [order_less_irrefl];

goal thy "(x::'a::order) <= y = (x < y | x = y)";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
by (Blast_tac 1);
qed "order_le_less";

(** min **)

goalw thy [min_def] "!!least. (!!x. least <= x) ==> min least x = least";
by (Asm_simp_tac 1);
qed "min_leastL";

val prems = goalw thy [min_def]
 "(!!x::'a::order. least <= x) ==> min x least = least";
by (cut_facts_tac prems 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "min_leastR";


section "Linear/Total Orders";

goal thy "!!x::'a::linorder. x<y | x=y | y<x";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
by(cut_facts_tac [linorder_linear] 1);
by (Blast_tac 1);
qed "linorder_less_linear";

goalw thy [max_def] "!!z::'a::linorder. (z <= max x y) = (z <= x | z <= y)";
by (Simp_tac 1);
by(cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "le_max_iff_disj";

goalw thy [max_def] "!!z::'a::linorder. (max x y <= z) = (x <= z & y <= z)";
by (Simp_tac 1);
by(cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "max_le_iff_conj";

goalw thy [min_def] "!!z::'a::linorder. (z <= min x y) = (z <= x & z <= y)";
by (Simp_tac 1);
by(cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "le_min_iff_conj";

goalw thy [min_def] "!!z::'a::linorder. (min x y <= z) = (x <= z | y <= z)";
by (Simp_tac 1);
by(cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "min_le_iff_disj";


