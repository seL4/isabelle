(*  Title:      HOL/Ord.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The type class for ordered types
*)

(*Tell Blast_tac about overloading of < and <= to reduce the risk of
  its applying a rule for the wrong type*)
Blast.overloaded ("op <", domain_type); 
Blast.overloaded ("op <=", domain_type);

(** mono **)

val [prem] = Goalw [mono_def]
    "[| !!A B. A <= B ==> f(A) <= f(B) |] ==> mono(f)";
by (REPEAT (ares_tac [allI, impI, prem] 1));
qed "monoI";
AddXIs [monoI];

Goalw [mono_def] "[| mono(f);  A <= B |] ==> f(A) <= f(B)";
by (Fast_tac 1);
qed "monoD";
AddXDs [monoD];


section "Orders";

(** Reflexivity **)

AddIffs [order_refl];

(*This form is useful with the classical reasoner*)
Goal "!!x::'a::order. x = y ==> x <= y";
by (etac ssubst 1);
by (rtac order_refl 1);
qed "order_eq_refl";

Goal "~ x < (x::'a::order)";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
qed "order_less_irrefl";
Addsimps [order_less_irrefl];

Goal "(x::'a::order) <= y = (x < y | x = y)";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
   (*NOT suitable for AddIffs, since it can cause PROOF FAILED*)
by (blast_tac (claset() addSIs [order_refl]) 1);
qed "order_le_less";

Goal "!!x::'a::order. x < y ==> x <= y";
by (asm_full_simp_tac (simpset() addsimps [order_less_le]) 1);
qed "order_less_imp_le";

(** Asymmetry **)

Goal "(x::'a::order) < y ==> ~ (y<x)";
by (asm_full_simp_tac (simpset() addsimps [order_less_le, order_antisym]) 1);
qed "order_less_not_sym";

(* [| n<m;  ~P ==> m<n |] ==> P *)
bind_thm ("order_less_asym", order_less_not_sym RS swap);

(* Transitivity *)

Goal "!!x::'a::order. [| x < y; y < z |] ==> x < z";
by (asm_full_simp_tac (simpset() addsimps [order_less_le]) 1);
by (blast_tac (claset() addIs [order_trans,order_antisym]) 1);
qed "order_less_trans";

Goal "!!x::'a::order. [| x <= y; y < z |] ==> x < z";
by (asm_full_simp_tac (simpset() addsimps [order_less_le]) 1);
by (blast_tac (claset() addIs [order_trans,order_antisym]) 1);
qed "order_le_less_trans";

Goal "!!x::'a::order. [| x < y; y <= z |] ==> x < z";
by (asm_full_simp_tac (simpset() addsimps [order_less_le]) 1);
by (blast_tac (claset() addIs [order_trans,order_antisym]) 1);
qed "order_less_le_trans";


(** Useful for simplification, but too risky to include by default. **)

Goal "(x::'a::order) < y ==>  (~ y < x) = True";
by (blast_tac (claset() addEs [order_less_asym]) 1);
qed "order_less_imp_not_less";

Goal "(x::'a::order) < y ==>  (y < x --> P) = True";
by (blast_tac (claset() addEs [order_less_asym]) 1);
qed "order_less_imp_triv";

Goal "(x::'a::order) < y ==>  (x = y) = False";
by Auto_tac;
qed "order_less_imp_not_eq";

Goal "(x::'a::order) < y ==>  (y = x) = False";
by Auto_tac;
qed "order_less_imp_not_eq2";


(** min **)

val prems = Goalw [min_def] "(!!x. least <= x) ==> min least x = least";
by (simp_tac (simpset() addsimps prems) 1);
qed "min_leastL";

val prems = Goalw [min_def]
 "(!!x::'a::order. least <= x) ==> min x least = least";
by (cut_facts_tac prems 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "min_leastR";


section "Linear/Total Orders";

Goal "!!x::'a::linorder. x<y | x=y | y<x";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
by (cut_facts_tac [linorder_linear] 1);
by (Blast_tac 1);
qed "linorder_less_linear";

val prems = goal thy
 "[| (x::'a::linorder)<y ==> P; x=y ==> P; y<x ==> P |] ==> P";
by(cut_facts_tac [linorder_less_linear] 1);
by(REPEAT(eresolve_tac (prems@[disjE]) 1));
qed "linorder_less_split";

Goal "!!x::'a::linorder. (~ x < y) = (y <= x)";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
by (cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "linorder_not_less";

Goal "!!x::'a::linorder. (~ x <= y) = (y < x)";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
by (cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "linorder_not_le";

Goal "!!x::'a::linorder. (x ~= y) = (x<y | y<x)";
by (cut_inst_tac [("x","x"),("y","y")] linorder_less_linear 1);
by Auto_tac;
qed "linorder_neq_iff";

(* eliminates ~= in premises *)
bind_thm("linorder_neqE", linorder_neq_iff RS iffD1 RS disjE);

(** min & max **)

Goalw [min_def] "min (x::'a::order) x = x";
by (Simp_tac 1);
qed "min_same";
Addsimps [min_same];

Goalw [max_def] "max (x::'a::order) x = x";
by (Simp_tac 1);
qed "max_same";
Addsimps [max_same];

Goalw [max_def] "!!z::'a::linorder. (z <= max x y) = (z <= x | z <= y)";
by (Simp_tac 1);
by (cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "le_max_iff_disj";

Goal "(x::'a::linorder) <= max x y";
by (simp_tac (simpset() addsimps [le_max_iff_disj]) 1);
qed "le_maxI1";

Goal "(y::'a::linorder) <= max x y";
by (simp_tac (simpset() addsimps [le_max_iff_disj]) 1);
qed "le_maxI2";
(*CANNOT use with AddSIs because blast_tac will give PROOF FAILED.*)

Goalw [max_def] "!!z::'a::linorder. (z < max x y) = (z < x | z < y)";
by (simp_tac (simpset() addsimps [order_le_less]) 1);
by (cut_facts_tac [linorder_less_linear] 1);
by (blast_tac (claset() addIs [order_less_trans]) 1);
qed "less_max_iff_disj";

Goalw [max_def] "!!z::'a::linorder. (max x y <= z) = (x <= z & y <= z)";
by (Simp_tac 1);
by (cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "max_le_iff_conj";
Addsimps [max_le_iff_conj];

Goalw [max_def] "!!z::'a::linorder. (max x y < z) = (x < z & y < z)";
by (simp_tac (simpset() addsimps [order_le_less]) 1);
by (cut_facts_tac [linorder_less_linear] 1);
by (blast_tac (claset() addIs [order_less_trans]) 1);
qed "max_less_iff_conj";
Addsimps [max_less_iff_conj];

Goalw [min_def] "!!z::'a::linorder. (z <= min x y) = (z <= x & z <= y)";
by (Simp_tac 1);
by (cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "le_min_iff_conj";
Addsimps [le_min_iff_conj];
(* AddIffs screws up a blast_tac in MiniML *)

Goalw [min_def] "!!z::'a::linorder. (z < min x y) = (z < x & z < y)";
by (simp_tac (simpset() addsimps [order_le_less]) 1);
by (cut_facts_tac [linorder_less_linear] 1);
by (blast_tac (claset() addIs [order_less_trans]) 1);
qed "min_less_iff_conj";
Addsimps [min_less_iff_conj];

Goalw [min_def] "!!z::'a::linorder. (min x y <= z) = (x <= z | y <= z)";
by (Simp_tac 1);
by (cut_facts_tac [linorder_linear] 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "min_le_iff_disj";

Goalw [min_def] "!!z::'a::linorder. (min x y < z) = (x < z | y < z)";
by (simp_tac (simpset() addsimps [order_le_less]) 1);
by (cut_facts_tac [linorder_less_linear] 1);
by (blast_tac (claset() addIs [order_less_trans]) 1);
qed "min_less_iff_disj";

Goalw [min_def]
 "P(min (i::'a::linorder) j) = ((i <= j --> P(i)) & (~ i <= j --> P(j)))";
by (Simp_tac 1);
qed "split_min";

Goalw [max_def]
 "P(max (i::'a::linorder) j) = ((i <= j --> P(j)) & (~ i <= j --> P(i)))";
by (Simp_tac 1);
qed "split_max";
