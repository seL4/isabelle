(*  Title:      HOL/Integ/Int.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order

And many further lemmas
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

Goal "(x = - y) = (y = - (x::int))";
by Auto_tac;
qed "equation_zminus";

Goal "(- x = y) = (- (y::int) = x)";
by Auto_tac;
qed "zminus_equation";

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
qed "neg_eq_less_int0"; 

Goalw [zle_def] "(~neg x) = (int 0 <= x)";
by (simp_tac (simpset() addsimps [neg_eq_less_int0]) 1); 
qed "not_neg_eq_ge_int0"; 


(**** nat: magnitide of an integer, as a natural number ****)

Goalw [nat_def] "nat(int n) = n";
by Auto_tac;
qed "nat_nat";

Goalw [nat_def] "nat(- int n) = 0";
by (auto_tac (claset(),
	      simpset() addsimps [neg_eq_less_int0, zminus_zless])); 
qed "nat_zminus_nat";

Addsimps [nat_nat, nat_zminus_nat];

Goal "~ neg z ==> int (nat z) = z"; 
by (dtac (not_neg_eq_ge_int0 RS iffD1) 1); 
by (dtac zle_imp_zless_or_eq 1); 
by (auto_tac (claset(), simpset() addsimps [zless_iff_Suc_zadd])); 
qed "not_neg_nat"; 

Goal "neg x ==> ? n. x = - (int (Suc n))"; 
by (auto_tac (claset(), 
	      simpset() addsimps [neg_eq_less_int0, zless_iff_Suc_zadd,
				  zdiff_eq_eq RS sym, zdiff_def])); 
qed "negD"; 

Goalw [nat_def] "neg z ==> nat z = 0"; 
by Auto_tac; 
qed "neg_nat"; 

(*An alternative condition is  int 0 <= w  *)
Goal "int 0 < z ==> (nat w < nat z) = (w < z)";
by (stac (zless_int RS sym) 1);
by (asm_simp_tac (simpset() addsimps [not_neg_nat, not_neg_eq_ge_int0, 
				      order_le_less]) 1);
by (case_tac "neg w" 1);
by (asm_simp_tac (simpset() addsimps [not_neg_nat]) 2);
by (asm_full_simp_tac (simpset() addsimps [neg_eq_less_int0, neg_nat]) 1);
by (blast_tac (claset() addIs [order_less_trans]) 1);
val lemma = result();

Goal "z <= int 0 ==> nat z = 0"; 
by (auto_tac (claset(), 
	      simpset() addsimps [order_le_less, neg_eq_less_int0, 
				  zle_def, neg_nat])); 
qed "nat_le_0"; 

Goal "(nat w < nat z) = (int 0 < z & w < z)";
by (case_tac "int 0 < z" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [lemma, nat_le_0, linorder_not_less])); 
qed "zless_nat_conj";


(* a case theorem distinguishing non-negative and negative int *)  

val prems = Goal
     "[|!! n. z = int n ==> P;  !! n. z =  - (int (Suc n)) ==> P |] ==> P"; 
by (case_tac "neg z" 1); 
by (fast_tac (claset() addSDs [negD] addSEs prems) 1); 
by (dtac (not_neg_nat RS sym) 1);
by (eresolve_tac prems 1);
qed "int_cases"; 

fun int_case_tac x = res_inst_tac [("z",x)] int_cases; 


(*** Monotonicity of Multiplication ***)

Goal "i <= (j::int) ==> i * int k <= j * int k";
by (induct_tac "k" 1);
by (stac int_Suc_int_1 2);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2, zadd_zle_mono])));
val lemma = result();

Goal "[| i <= j;  int 0 <= k |] ==> i*k <= j*k";
by (res_inst_tac [("t", "k")] (not_neg_nat RS subst) 1);
by (etac lemma 2);
by (full_simp_tac (simpset() addsimps [not_neg_eq_ge_int0]) 1);
qed "zmult_zle_mono1";

Goal "[| i <= j;  k <= int 0 |] ==> j*k <= i*k";
by (rtac (zminus_zle_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() addsimps [zmult_zminus_right RS sym,
				      zmult_zle_mono1, zle_zminus]) 1);
qed "zmult_zle_mono1_neg";

Goal "[| i <= j;  int 0 <= k |] ==> k*i <= k*j";
by (dtac zmult_zle_mono1 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zle_mono2";

Goal "[| i <= j;  k <= int 0 |] ==> k*j <= k*i";
by (dtac zmult_zle_mono1_neg 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zle_mono2_neg";

(*<=monotonicity, BOTH arguments*)
Goal "[| i <= j;  k <= l;  int 0 <= j;  int 0 <= k |] ==> i*k <= j*l";
by (etac (zmult_zle_mono1 RS order_trans) 1);
by (assume_tac 1);
by (rtac order_trans 1);
by (stac zmult_commute 2);
by (etac zmult_zle_mono1 2);
by (assume_tac 2);
by (simp_tac (simpset() addsimps [zmult_commute]) 1);
qed "zmult_zle_mono";


(** strict, in 1st argument; proof is by induction on k>0 **)

Goal "i<j ==> 0<k --> int k * i < int k * j";
by (induct_tac "k" 1);
by (stac int_Suc_int_1 2);
by (case_tac "n=0" 2);
by (ALLGOALS (asm_full_simp_tac
	      (simpset() addsimps [zadd_zmult_distrib, zadd_zless_mono, 
				   order_le_less])));
val lemma = result() RS mp;

Goal "[| i<j;  int 0 < k |] ==> k*i < k*j";
by (res_inst_tac [("t", "k")] (not_neg_nat RS subst) 1);
by (etac lemma 2);
by (asm_simp_tac (simpset() addsimps [not_neg_eq_ge_int0, 
				      order_le_less]) 1);
by (forward_tac [conjI RS (zless_nat_conj RS iffD2)] 1);
by Auto_tac;
qed "zmult_zless_mono2";

Goal "[| i<j;  int 0 < k |] ==> i*k < j*k";
by (dtac zmult_zless_mono2 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_commute])));
qed "zmult_zless_mono1";

Goal "[| i<j;  k < int 0 |] ==> j*k < i*k";
by (rtac (zminus_zless_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() addsimps [zmult_zminus_right RS sym,
				      zmult_zless_mono1, zless_zminus]) 1);
qed "zmult_zless_mono1_neg";

Goal "[| i<j;  k < int 0 |] ==> k*j < k*i";
by (rtac (zminus_zless_zminus RS iffD1) 1);
by (asm_simp_tac (simpset() addsimps [zmult_zminus RS sym,
				      zmult_zless_mono2, zless_zminus]) 1);
qed "zmult_zless_mono2_neg";


Goal "(m*n = int 0) = (m = int 0 | n = int 0)";
by (case_tac "m < int 0" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [linorder_not_less, order_le_less, 
				  linorder_neq_iff])); 
by (REPEAT 
    (force_tac (claset() addDs [zmult_zless_mono1_neg, zmult_zless_mono1], 
		simpset()) 1));
qed "zmult_eq_iff";


Goal "int 0 < k ==> (m*k < n*k) = (m<n)";
by (safe_tac (claset() addSIs [zmult_zless_mono1]));
by (cut_facts_tac [linorder_less_linear] 1);
by (blast_tac (claset() addIs [zmult_zless_mono1] addEs [order_less_asym]) 1);
qed "zmult_zless_cancel2";

Goal "int 0 < k ==> (k*m < k*n) = (m<n)";
by (dtac zmult_zless_cancel2 1);
by (asm_full_simp_tac (simpset() addsimps [zmult_commute]) 1);
qed "zmult_zless_cancel1";
Addsimps [zmult_zless_cancel1, zmult_zless_cancel2];

Goal "k < int 0 ==> (m*k < n*k) = (n<m)";
by (safe_tac (claset() addSIs [zmult_zless_mono1_neg]));
by (cut_facts_tac [linorder_less_linear] 1);
by (blast_tac (claset() addIs [zmult_zless_mono1_neg] 
                        addEs [order_less_asym]) 1);
qed "zmult_zless_cancel2_neg";

Goal "k < int 0 ==> (k*m < k*n) = (n<m)";
by (dtac zmult_zless_cancel2_neg 1);
by (asm_full_simp_tac (simpset() addsimps [zmult_commute]) 1);
qed "zmult_zless_cancel1_neg";
Addsimps [zmult_zless_cancel1_neg, zmult_zless_cancel2_neg];

Goal "int 0 < k ==> (m*k <= n*k) = (m<=n)";
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
qed "zmult_zle_cancel2";

Goal "int 0 < k ==> (k*m <= k*n) = (m<=n)";
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
qed "zmult_zle_cancel1";
Addsimps [zmult_zle_cancel1, zmult_zle_cancel2];

Goal "k < int 0 ==> (m*k <= n*k) = (n<=m)";
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
qed "zmult_zle_cancel2_neg";

Goal "k < int 0 ==> (k*m <= k*n) = (n<=m)";
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
qed "zmult_zle_cancel1_neg";
Addsimps [zmult_zle_cancel1_neg, zmult_zle_cancel2_neg];

Goal "k ~= int 0 ==> (m*k = n*k) = (m=n)";
by (cut_facts_tac [linorder_less_linear] 1);
by Safe_tac;
by (assume_tac 2);
by (REPEAT 
    (force_tac (claset() addD2 ("mono_neg", zmult_zless_mono1_neg)
                         addD2 ("mono_pos", zmult_zless_mono1), 
		simpset() addsimps [linorder_neq_iff]) 1));
qed "zmult_cancel2";

Goal "k ~= int 0 ==> (k*m = k*n) = (m=n)";
by (dtac zmult_cancel2 1);
by (asm_full_simp_tac (simpset() addsimps [zmult_commute]) 1);
qed "zmult_cancel1";
Addsimps [zmult_cancel1, zmult_cancel2];
