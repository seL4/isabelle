(*  Title:      HOL/Integ/Bin.ML
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
                David Spelt, University of Twente 
    Copyright   1994  University of Cambridge
    Copyright   1996 University of Twente

Arithmetic on binary integers.
*)

(** extra rules for bin_succ, bin_pred, bin_add, bin_mult **)

qed_goal "NCons_Pls_0" Bin.thy
    "NCons Pls False = Pls"
 (fn _ => [(Simp_tac 1)]);

qed_goal "NCons_Pls_1" Bin.thy
    "NCons Pls True = Pls BIT True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "NCons_Min_0" Bin.thy
    "NCons Min False = Min BIT False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "NCons_Min_1" Bin.thy
    "NCons Min True = Min"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_1" Bin.thy
    "bin_succ(w BIT True) = (bin_succ w) BIT False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_0" Bin.thy
    "bin_succ(w BIT False) =  NCons w True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_1" Bin.thy
    "bin_pred(w BIT True) = NCons w False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_0" Bin.thy
    "bin_pred(w BIT False) = (bin_pred w) BIT True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_1" Bin.thy
    "bin_minus(w BIT True) = bin_pred (NCons (bin_minus w) False)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_0" Bin.thy
    "bin_minus(w BIT False) = (bin_minus w) BIT False"
 (fn _ => [(Simp_tac 1)]);


(*** bin_add: binary addition ***)

qed_goal "bin_add_BIT_11" Bin.thy
    "bin_add (v BIT True) (w BIT True) = \
\    NCons (bin_add v (bin_succ w)) False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_BIT_10" Bin.thy
    "bin_add (v BIT True) (w BIT False) = NCons (bin_add v w) True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_BIT_0" Bin.thy
    "bin_add (v BIT False) (w BIT y) = NCons (bin_add v w) y"
 (fn _ => [Auto_tac]);

Goal "bin_add w Pls = w";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_add_Pls_right";

qed_goal "bin_add_BIT_Min" Bin.thy
    "bin_add (v BIT x) Min = bin_pred (v BIT x)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_BIT_BIT" Bin.thy
    "bin_add (v BIT x) (w BIT y) = \
\    NCons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)"
 (fn _ => [(Simp_tac 1)]);


(*** bin_add: binary multiplication ***)

qed_goal "bin_mult_1" Bin.thy
    "bin_mult (v BIT True) w = bin_add (NCons (bin_mult v w) False) w"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_mult_0" Bin.thy
    "bin_mult (v BIT False) w = NCons (bin_mult v w) False"
 (fn _ => [(Simp_tac 1)]);


(**** The carry/borrow functions, bin_succ and bin_pred ****)


(**** integ_of ****)

qed_goal "integ_of_NCons" Bin.thy
    "integ_of(NCons w b) = integ_of(w BIT b)"
 (fn _ =>[(induct_tac "w" 1),
          (ALLGOALS Asm_simp_tac) ]);

Addsimps [integ_of_NCons];

qed_goal "integ_of_succ" Bin.thy
    "integ_of(bin_succ w) = int 1 + integ_of w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac (simpset() addsimps zadd_ac))) ]);

qed_goal "integ_of_pred" Bin.thy
    "integ_of(bin_pred w) = - (int 1) + integ_of w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac (simpset() addsimps zadd_ac))) ]);

Goal "integ_of(bin_minus w) = - (integ_of w)";
by (rtac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset()
		  delsimps [bin_pred_Pls, bin_pred_Min, bin_pred_BIT]
		  addsimps [integ_of_succ,integ_of_pred,
			    zadd_assoc]) 1);
qed "integ_of_minus";

 
val bin_add_simps = [bin_add_BIT_BIT,
                     integ_of_succ, integ_of_pred];

Goal "! w. integ_of(bin_add v w) = integ_of v + integ_of w";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (rtac allI 1);
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps bin_add_simps @ zadd_ac)));
qed_spec_mp "integ_of_add";

val bin_mult_simps = [zmult_zminus, integ_of_minus, integ_of_add];


Goal "integ_of(bin_mult v w) = integ_of v * integ_of w";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (asm_simp_tac
    (simpset() addsimps bin_mult_simps @ [zadd_zmult_distrib] @ zadd_ac) 1);
qed "integ_of_mult";


(** Simplification rules with integer constants **)

Goal "#0 + z = z";
by (Simp_tac 1);
qed "zadd_0";

Goal "z + #0 = z";
by (Simp_tac 1);
qed "zadd_0_right";

Addsimps [zadd_0, zadd_0_right];


(** Converting simple cases of (int n) to numerals **)

(*int 0 = #0 *)
bind_thm ("int_0", integ_of_Pls RS sym);

Goal "int (Suc n) = #1 + int n";
by (simp_tac (simpset() addsimps [zadd_int]) 1);
qed "int_Suc";

val int_simps = [int_0, int_Suc];

Goal "- (#0) = #0";
by (Simp_tac 1);
qed "zminus_0";

Addsimps [zminus_0];


Goal "#0 - x = -x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0";

Goal "x - #0 = x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0_right";

Goal "x - x = #0";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff_self";

Addsimps [zdiff0, zdiff0_right, zdiff_self];

Goal "#0 * z = #0";
by (Simp_tac 1);
qed "zmult_0";

Goal "#1 * z = z";
by (Simp_tac 1);
qed "zmult_1";

Goal "#2 * z = z+z";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib]) 1);
qed "zmult_2";

Goal "z * #0 = #0";
by (Simp_tac 1);
qed "zmult_0_right";

Goal "z * #1 = z";
by (Simp_tac 1);
qed "zmult_1_right";

Goal "z * #2 = z+z";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
qed "zmult_2_right";

Addsimps [zmult_0, zmult_0_right, 
	  zmult_1, zmult_1_right, 
	  zmult_2, zmult_2_right];

Goal "(w < z + #1) = (w<z | w=z)";
by (simp_tac (simpset() addsimps [zless_add_int_Suc_eq]) 1);
qed "zless_add1_eq";

Goal "(w + #1 <= z) = (w<z)";
by (simp_tac (simpset() addsimps [add_int_Suc_zle_eq]) 1);
qed "add1_zle_eq";
Addsimps [add1_zle_eq];

Goal "neg x = (x < #0)";
by (simp_tac (simpset() addsimps [neg_eq_less_nat0]) 1); 
qed "neg_eq_less_0"; 

Goal "(~neg x) = (int 0 <= x)";
by (simp_tac (simpset() addsimps [not_neg_eq_ge_nat0]) 1); 
qed "not_neg_eq_ge_0"; 

Goal "#0 <= int m";
by (Simp_tac 1);
qed "zero_zle_int";
AddIffs [zero_zle_int];


(** Simplification rules for comparison of binary numbers (Norbert Voelker) **)

(** Equals (=) **)

Goalw [iszero_def]
      "(integ_of x = integ_of y) \ 
\      = iszero(integ_of (bin_add x (bin_minus y)))"; 
by (simp_tac (simpset() addsimps
              (zcompare_rls @ [integ_of_add, integ_of_minus])) 1); 
qed "eq_integ_of_eq"; 

Goalw [iszero_def] "iszero (integ_of Pls)"; 
by (Simp_tac 1); 
qed "iszero_integ_of_Pls"; 

Goalw [iszero_def] "~ iszero(integ_of Min)"; 
by (Simp_tac 1);
qed "nonzero_integ_of_Min"; 

Goalw [iszero_def]
     "iszero (integ_of (w BIT x)) = (~x & iszero (integ_of w))"; 
by (Simp_tac 1);
by (int_case_tac "integ_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps zcompare_rls @ 
				  [zminus_zadd_distrib RS sym, 
				   zadd_int]))); 
qed "iszero_integ_of_BIT"; 


(** Less-than (<) **)

Goalw [zless_def,zdiff_def] 
    "integ_of x < integ_of y \
\    = neg (integ_of (bin_add x (bin_minus y)))";
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
qed "less_integ_of_eq_neg"; 

Goal "~ neg (integ_of Pls)"; 
by (Simp_tac 1); 
qed "not_neg_integ_of_Pls"; 

Goal "neg (integ_of Min)"; 
by (Simp_tac 1);
qed "neg_integ_of_Min"; 

Goal "neg (integ_of (w BIT x)) = neg (integ_of w)"; 
by (Asm_simp_tac 1); 
by (int_case_tac "integ_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps [zadd_int, neg_eq_less_nat0, 
				   symmetric zdiff_def] @ zcompare_rls))); 
qed "neg_integ_of_BIT"; 


(** Less-than-or-equals (<=) **)

Goal "(integ_of x <= integ_of y) = (~ integ_of y < integ_of x)";
by (simp_tac (simpset() addsimps [zle_def]) 1);
qed "le_integ_of_eq_not_less"; 

(*Delete the original rewrites, with their clumsy conditional expressions*)
Delsimps [bin_succ_BIT, bin_pred_BIT, bin_minus_BIT, 
          NCons_Pls, NCons_Min, bin_add_BIT, bin_mult_BIT];

(*Hide the binary representation of integer constants*)
Delsimps [integ_of_Pls, integ_of_Min, integ_of_BIT];

(*Add simplification of arithmetic operations on integer constants*)
Addsimps [integ_of_add RS sym,
          integ_of_minus RS sym,
          integ_of_mult RS sym,
          bin_succ_1, bin_succ_0, 
          bin_pred_1, bin_pred_0, 
          bin_minus_1, bin_minus_0,  
          bin_add_Pls_right, bin_add_BIT_Min,
          bin_add_BIT_0, bin_add_BIT_10, bin_add_BIT_11,
          bin_mult_1, bin_mult_0, 
          NCons_Pls_0, NCons_Pls_1, 
          NCons_Min_0, NCons_Min_1, 
          NCons_BIT];

(*... and simplification of relational operations*)
Addsimps [eq_integ_of_eq, iszero_integ_of_Pls, nonzero_integ_of_Min,
	  iszero_integ_of_BIT,
	  less_integ_of_eq_neg,
	  not_neg_integ_of_Pls, neg_integ_of_Min, neg_integ_of_BIT,
	  le_integ_of_eq_not_less];

Goalw [zdiff_def]
     "integ_of v - integ_of w = integ_of(bin_add v (bin_minus w))";
by (Simp_tac 1);
qed "diff_integ_of_eq";

(*... and finally subtraction*)
Addsimps [diff_integ_of_eq];


(** Simplification of arithmetic when nested to the right **)

Goal "integ_of v + (integ_of w + z) = integ_of(bin_add v w) + z";
by (simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "add_integ_of_left";

Goal "integ_of v * (integ_of w * z) = integ_of(bin_mult v w) * z";
by (simp_tac (simpset() addsimps [zmult_assoc RS sym]) 1);
qed "mult_integ_of_left";

Addsimps [add_integ_of_left, mult_integ_of_left];


(** Simplification of inequalities involving numerical constants **)

Goal "(w <= z + #1) = (w<=z | w = z + #1)";
by (simp_tac (simpset() addsimps [integ_le_less, zless_add1_eq]) 1);
qed "zle_add1_eq";

Goal "(w <= z - #1) = (w<z)";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zle_diff1_eq";
Addsimps [zle_diff1_eq];

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w <= z; #0 <= v |] ==> w <= z + v";
by (dtac zadd_zle_mono 1);
by (assume_tac 1);
by (Full_simp_tac 1);
qed "zle_imp_zle_zadd";

Goal "w <= z ==> w <= z + #1";
by (asm_simp_tac (simpset() addsimps [zle_imp_zle_zadd]) 1);
qed "zle_imp_zle_zadd1";

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w < z; #0 <= v |] ==> w < z + v";
by (dtac zadd_zless_mono 1);
by (assume_tac 1);
by (Full_simp_tac 1);
qed "zless_imp_zless_zadd";

Goal "w < z ==> w < z + #1";
by (asm_simp_tac (simpset() addsimps [zless_imp_zless_zadd]) 1);
qed "zless_imp_zless_zadd1";

Goal "(w < z + #1) = (w<=z)";
by (simp_tac (simpset() addsimps [zless_add1_eq, integ_le_less]) 1);
qed "zle_add1_eq_le";
Addsimps [zle_add1_eq_le];

Goal "(z = z + w) = (w = #0)";
by (rtac trans 1);
by (rtac zadd_left_cancel 2);
by (simp_tac (simpset() addsimps [eq_sym_conv]) 1);
qed "zadd_left_cancel0";
Addsimps [zadd_left_cancel0];

(*LOOPS as a simprule!*)
Goal "[| w + v < z; #0 <= v |] ==> w < z";
by (dtac zadd_zless_mono 1);
by (assume_tac 1);
by (full_simp_tac (simpset() addsimps zadd_ac) 1);
qed "zless_zadd_imp_zless";

(*LOOPS as a simprule!  Analogous to Suc_lessD*)
Goal "w + #1 < z ==> w < z";
by (dtac zless_zadd_imp_zless 1);
by (assume_tac 2);
by (Simp_tac 1);
qed "zless_zadd1_imp_zless";

Goal "w + #-1 = w - #1";
by (Simp_tac 1);
qed "zplus_minus1_conv";


(*** nat ***)

Goal "#0 <= z ==> int (nat z) = z"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, not_neg_nat]) 1); 
qed "nat_0_le"; 

Goal "z < #0 ==> nat z = 0"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, neg_nat]) 1); 
qed "nat_less_0"; 

Addsimps [nat_0_le, nat_less_0];

Goal "#0 <= w ==> (nat w = m) = (w = int m)";
by Auto_tac;
qed "nat_eq_iff";

Goal "#0 <= w ==> (nat w < m) = (w < int m)";
by (rtac iffI 1);
by (asm_full_simp_tac 
    (simpset() delsimps [zless_int] addsimps [zless_int RS sym]) 2);
by (etac (nat_0_le RS subst) 1);
by (Simp_tac 1);
qed "nat_less_iff";

Goal "#0 <= w ==> (nat w < nat z) = (w<z)";
by (case_tac "neg z" 1);
by (auto_tac (claset(), simpset() addsimps [nat_less_iff]));
by (auto_tac (claset() addIs [zless_trans], 
	      simpset() addsimps [neg_eq_less_0, zle_def, int_0]));
qed "nat_less_eq_zless";
