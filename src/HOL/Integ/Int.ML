(*  Title:      HOL/Integ/Int.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order
*)

Goal "(w<z) = neg(w-z)";
by (simp_tac (simpset() addsimps [zless_def]) 1);
qed "zless_eq_neg";

Goal "(w=z) = iszero(w-z)";
by (simp_tac (simpset() addsimps [iszero_def, zdiff_eq_eq]) 1);
qed "eq_eq_iszero";

Goal "(w<=z) = (~ neg(z-w))";
by (simp_tac (simpset() addsimps [zle_def, zless_def]) 1);
qed "zle_eq_not_neg";


(*** Inequality lemmas involving int (Suc m) ***)

Goal "(w < z + int (Suc m)) = (w < z + int m | w = z + int m)";
by (auto_tac (claset(),
	      simpset() addsimps [zless_iff_Suc_zadd, zadd_assoc, zadd_int]));
by (cut_inst_tac [("m","m")] int_Suc_int_1 1);
by (cut_inst_tac [("m","n")] int_Suc_int_1 1);
by (Asm_full_simp_tac 1);
by (exhaust_tac "n" 1);
by Auto_tac;
by (cut_inst_tac [("m","m")] int_Suc_int_1 1);
by (full_simp_tac (simpset() addsimps zadd_ac) 1);
by (asm_full_simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
by (auto_tac (claset(),
	      simpset() addsimps [zless_iff_Suc_zadd, zadd_assoc, zadd_int]));
qed "zless_add_int_Suc_eq";


Goal "(w + int (Suc m) <= z) = (w + int m < z)";
by (simp_tac (simpset() addsimps [zle_def, zless_add_int_Suc_eq]) 1);
by (auto_tac (claset() addIs [zle_anti_sym] addEs [zless_asym],
	      simpset() addsimps [zless_imp_zle, symmetric zle_def]));
qed "add_int_Suc_zle_eq";


(* (w < int (Suc m)) = (w < int m | w = int m) *)
bind_thm ("less_int_Suc_eq",
	  simplify (simpset())
	    (read_instantiate  [("z", "int 0")] zless_add_int_Suc_eq));

Goal "(w <= int (Suc m)) = (w <= int m | w = int (Suc m))";
by (simp_tac (simpset() addsimps [less_int_Suc_eq, order_le_less]) 1);
qed "le_int_Suc_eq";


(*** Monotonicity results ***)

Goal "(v+z < w+z) = (v < (w::int))";
by (Simp_tac 1);
qed "zadd_right_cancel_zless";

Goal "(z+v < z+w) = (v < (w::int))";
by (Simp_tac 1);
qed "zadd_left_cancel_zless";

Addsimps [zadd_right_cancel_zless, zadd_left_cancel_zless];

Goal "(v+z <= w+z) = (v <= (w::int))";
by (Simp_tac 1);
qed "zadd_right_cancel_zle";

Goal "(z+v <= z+w) = (v <= (w::int))";
by (Simp_tac 1);
qed "zadd_left_cancel_zle";

Addsimps [zadd_right_cancel_zle, zadd_left_cancel_zle];

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("zadd_zless_mono1", zadd_right_cancel_zless RS iffD2);

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("zadd_zle_mono1", zadd_right_cancel_zle RS iffD2);

Goal "!!z z'::int. [| w'<=w; z'<=z |] ==> w' + z' <= w + z";
by (etac (zadd_zle_mono1 RS zle_trans) 1);
by (Simp_tac 1);
qed "zadd_zle_mono";

Goal "!!z z'::int. [| w'<w; z'<=z |] ==> w' + z' < w + z";
by (etac (zadd_zless_mono1 RS zless_zle_trans) 1);
by (Simp_tac 1);
qed "zadd_zless_mono";


(*** Comparison laws ***)

Goal "(- x < - y) = (y < (x::int))";
by (simp_tac (simpset() addsimps [zless_def, zdiff_def] @ zadd_ac) 1);
qed "zminus_zless_zminus"; 
Addsimps [zminus_zless_zminus];

Goal "(- x <= - y) = (y <= (x::int))";
by (simp_tac (simpset() addsimps [zle_def]) 1);
qed "zminus_zle_zminus"; 
Addsimps [zminus_zle_zminus];

(** The next several equations can make the simplifier loop! **)

Goal "(x < - y) = (y < - (x::int))";
by (simp_tac (simpset() addsimps [zless_def, zdiff_def] @ zadd_ac) 1);
qed "zless_zminus"; 

Goal "(- x < y) = (- y < (x::int))";
by (simp_tac (simpset() addsimps [zless_def, zdiff_def] @ zadd_ac) 1);
qed "zminus_zless"; 

Goal "(x <= - y) = (y <= - (x::int))";
by (simp_tac (simpset() addsimps [zle_def, zminus_zless]) 1);
qed "zle_zminus"; 

Goal "(- x <= y) = (- y <= (x::int))";
by (simp_tac (simpset() addsimps [zle_def, zless_zminus]) 1);
qed "zminus_zle"; 

Goal "- (int (Suc n)) < int 0";
by (simp_tac (simpset() addsimps [zless_def]) 1);
qed "negative_zless_0"; 

Goal "- (int (Suc n)) < int m";
by (rtac (negative_zless_0 RS zless_zle_trans) 1);
by (Simp_tac 1); 
qed "negative_zless"; 
AddIffs [negative_zless]; 

Goal "- int n <= int 0";
by (simp_tac (simpset() addsimps [zminus_zle]) 1);
qed "negative_zle_0"; 

Goal "- int n <= int m";
by (simp_tac (simpset() addsimps [zless_def, zle_def, zdiff_def, zadd_int]) 1);
qed "negative_zle"; 
AddIffs [negative_zle]; 

Goal "~(int 0 <= - (int (Suc n)))";
by (stac zle_zminus 1);
by (Simp_tac 1);
qed "not_zle_0_negative"; 
Addsimps [not_zle_0_negative]; 

Goal "(int n <= - int m) = (n = 0 & m = 0)"; 
by Safe_tac; 
by (Simp_tac 3); 
by (dtac (zle_zminus RS iffD1) 2); 
by (ALLGOALS (dtac (negative_zle_0 RSN(2,zle_trans)))); 
by (ALLGOALS Asm_full_simp_tac); 
qed "int_zle_neg"; 

Goal "~(int n < - int m)";
by (simp_tac (simpset() addsimps [symmetric zle_def]) 1); 
qed "not_int_zless_negative"; 

Goal "(- int n = int m) = (n = 0 & m = 0)"; 
by (rtac iffI 1);
by (rtac (int_zle_neg RS iffD1) 1); 
by (dtac sym 1); 
by (ALLGOALS Asm_simp_tac); 
qed "negative_eq_positive"; 

Addsimps [negative_eq_positive, not_int_zless_negative]; 


Goal "(w <= z) = (EX n. z = w + int n)";
by (auto_tac (claset() addSIs [not_sym RS not0_implies_Suc],
	      simpset() addsimps [zless_iff_Suc_zadd, integ_le_less]));
qed "zle_iff_zadd";


Goalw [zdiff_def,zless_def] "neg x = (x < int 0)";
by Auto_tac; 
qed "neg_eq_less_nat0"; 

Goalw [zle_def] "(~neg x) = (int 0 <= x)";
by (simp_tac (simpset() addsimps [neg_eq_less_nat0]) 1); 
qed "not_neg_eq_ge_nat0"; 


(**** nat: magnitide of an integer, as a natural number ****)

Goalw [nat_def] "nat(int n) = n";
by Auto_tac;
qed "nat_nat";

Goalw [nat_def] "nat(- int n) = 0";
by (auto_tac (claset(),
	      simpset() addsimps [neg_eq_less_nat0, zminus_zless])); 
qed "nat_zminus_nat";

Addsimps [nat_nat, nat_zminus_nat];

Goal "~ neg z ==> int (nat z) = z"; 
by (dtac (not_neg_eq_ge_nat0 RS iffD1) 1); 
by (dtac zle_imp_zless_or_eq 1); 
by (auto_tac (claset(), simpset() addsimps [zless_iff_Suc_zadd])); 
qed "not_neg_nat"; 

Goal "neg x ==> ? n. x = - (int (Suc n))"; 
by (auto_tac (claset(), 
	      simpset() addsimps [neg_eq_less_nat0, zless_iff_Suc_zadd,
				  zdiff_eq_eq RS sym, zdiff_def])); 
qed "negD"; 

Goalw [nat_def] "neg z ==> nat z = 0"; 
by Auto_tac; 
qed "neg_nat"; 

(* a case theorem distinguishing positive and negative int *)  

val prems = Goal "[|!! n. P (int n); !! n. P (- (int (Suc n))) |] ==> P z"; 
by (case_tac "neg z" 1); 
by (blast_tac (claset() addSDs [negD] addSIs prems) 1); 
by (etac (not_neg_nat RS subst) 1);
by (resolve_tac prems 1);
qed "int_cases"; 

fun int_case_tac x = res_inst_tac [("z",x)] int_cases; 

