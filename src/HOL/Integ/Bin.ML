(*  Title:      HOL/Integ/Bin.ML
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
                David Spelt, University of Twente 
    Copyright   1994  University of Cambridge
    Copyright   1996 University of Twente

Arithmetic on binary integers.
*)

(** extra rules for bin_succ, bin_pred, bin_add, bin_mult **)

qed_goal "norm_Bcons_Plus_0" Bin.thy
    "norm_Bcons PlusSign False = PlusSign"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Plus_1" Bin.thy
    "norm_Bcons PlusSign True = Bcons PlusSign True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Minus_0" Bin.thy
    "norm_Bcons MinusSign False = Bcons MinusSign False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Minus_1" Bin.thy
    "norm_Bcons MinusSign True = MinusSign"
 (fn _ => [(Simp_tac 1)]);

qed_goal "norm_Bcons_Bcons" Bin.thy
    "norm_Bcons (Bcons w x) b = Bcons (Bcons w x) b"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_Bcons1" Bin.thy
    "bin_succ(Bcons w True) = Bcons (bin_succ w) False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_Bcons0" Bin.thy
    "bin_succ(Bcons w False) =  norm_Bcons w True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_Bcons1" Bin.thy
    "bin_pred(Bcons w True) = norm_Bcons w False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_Bcons0" Bin.thy
    "bin_pred(Bcons w False) = Bcons (bin_pred w) True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_Bcons1" Bin.thy
    "bin_minus(Bcons w True) = bin_pred (Bcons(bin_minus w) False)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_Bcons0" Bin.thy
    "bin_minus(Bcons w False) = Bcons (bin_minus w) False"
 (fn _ => [(Simp_tac 1)]);


(*** bin_add: binary addition ***)

qed_goal "bin_add_Bcons_Bcons11" Bin.thy
    "bin_add (Bcons v True) (Bcons w True) = \
\    norm_Bcons (bin_add v (bin_succ w)) False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Bcons10" Bin.thy
    "bin_add (Bcons v True) (Bcons w False) = norm_Bcons (bin_add v w) True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Bcons0" Bin.thy
    "bin_add (Bcons v False) (Bcons w y) = norm_Bcons (bin_add v w) y"
 (fn _ => [Auto_tac]);

qed_goal "bin_add_Bcons_Plus" Bin.thy
    "bin_add (Bcons v x) PlusSign = Bcons v x"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Minus" Bin.thy
    "bin_add (Bcons v x) MinusSign = bin_pred (Bcons v x)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_Bcons_Bcons" Bin.thy
    "bin_add (Bcons v x) (Bcons w y) = \
\    norm_Bcons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)"
 (fn _ => [(Simp_tac 1)]);


(*** bin_add: binary multiplication ***)

qed_goal "bin_mult_Bcons1" Bin.thy
    "bin_mult (Bcons v True) w = bin_add (norm_Bcons (bin_mult v w) False) w"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_mult_Bcons0" Bin.thy
    "bin_mult (Bcons v False) w = norm_Bcons (bin_mult v w) False"
 (fn _ => [(Simp_tac 1)]);


(**** The carry/borrow functions, bin_succ and bin_pred ****)


(**** integ_of ****)

qed_goal "integ_of_norm_Bcons" Bin.thy
    "integ_of(norm_Bcons w b) = integ_of(Bcons w b)"
 (fn _ =>[(induct_tac "w" 1),
          (ALLGOALS Asm_simp_tac) ]);

Addsimps [integ_of_norm_Bcons];

qed_goal "integ_of_succ" Bin.thy
    "integ_of(bin_succ w) = $#1 + integ_of w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac (simpset() addsimps zadd_ac))) ]);

qed_goal "integ_of_pred" Bin.thy
    "integ_of(bin_pred w) = - ($#1) + integ_of w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac (simpset() addsimps zadd_ac))) ]);

Goal "integ_of(bin_minus w) = - (integ_of w)";
by (rtac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset()
		  delsimps [pred_Plus,pred_Minus,pred_Bcons]
		  addsimps [integ_of_succ,integ_of_pred,
			    zadd_assoc]) 1);
qed "integ_of_minus";

 
val bin_add_simps = [bin_add_Bcons_Bcons,
                     integ_of_succ, integ_of_pred];

Goal "! w. integ_of(bin_add v w) = integ_of v + integ_of w";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (rtac allI 1);
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps (bin_add_simps @ zadd_ac))));
qed_spec_mp "integ_of_add";

val bin_mult_simps = [zmult_zminus, integ_of_minus, integ_of_add,
                      integ_of_norm_Bcons];


Goal "integ_of(bin_mult v w) = integ_of v * integ_of w";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (asm_simp_tac
    (simpset() addsimps (bin_mult_simps @ [zadd_zmult_distrib] @ 
                                  zadd_ac)) 1);
qed "integ_of_mult";


(** Simplification rules with integer constants **)

Goal "#0 + z = z";
by (Simp_tac 1);
qed "zadd_0";

Goal "z + #0 = z";
by (Simp_tac 1);
qed "zadd_0_right";

Goal "z + (- z) = #0";
by (Simp_tac 1);
qed "zadd_zminus_inverse";

Goal "(- z) + z = #0";
by (Simp_tac 1);
qed "zadd_zminus_inverse2";

(*These rewrite to $# 0.  Henceforth we should rewrite to #0  *)
Delsimps [zadd_zminus_inverse_nat, zadd_zminus_inverse_nat2];

Addsimps [zadd_0, zadd_0_right, zadd_zminus_inverse, zadd_zminus_inverse2];

Goal "- (#0) = #0";
by (Simp_tac 1);
qed "zminus_0";

Addsimps [zminus_0];

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
by (simp_tac (simpset() addsimps [zless_add_nat1_eq]) 1);
qed "zless_add1_eq";

Goal "(w + #1 <= z) = (w<z)";
by (simp_tac (simpset() addsimps [add_nat1_zle_eq]) 1);
qed "add1_zle_eq";
Addsimps [add1_zle_eq];

Goal "znegative x = (x < #0)";
by (simp_tac (simpset() addsimps [znegative_eq_less_nat0]) 1); 
qed "znegative_eq_less_0"; 

Goal "(~znegative x) = ($# 0 <= x)";
by (simp_tac (simpset() addsimps [not_znegative_eq_ge_nat0]) 1); 
qed "not_znegative_eq_ge_0"; 



(** Simplification rules for comparison of binary numbers (Norbert Voelker) **)

(** Equals (=) **)

Goalw [iszero_def]
      "(integ_of x = integ_of y) \ 
\      = iszero(integ_of (bin_add x (bin_minus y)))"; 
by (simp_tac (simpset() addsimps
              (zcompare_rls @ [integ_of_add, integ_of_minus])) 1); 
qed "eq_integ_of_eq"; 

Goalw [iszero_def] "iszero (integ_of PlusSign)"; 
by (Simp_tac 1); 
qed "iszero_integ_of_Plus"; 

Goalw [iszero_def] "~ iszero(integ_of MinusSign)"; 
by (Simp_tac 1);
qed "nonzero_integ_of_Minus"; 

Goalw [iszero_def]
     "iszero (integ_of (Bcons w x)) = (~x & iszero (integ_of w))"; 
by (Simp_tac 1);
by (int_case_tac "integ_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps (zcompare_rls @ 
				   [zminus_zadd_distrib RS sym, 
				    add_znat])))); 
qed "iszero_integ_of_Bcons"; 


(** Less-than (<) **)

Goalw [zless_def,zdiff_def] 
    "integ_of x < integ_of y \
\    = znegative (integ_of (bin_add x (bin_minus y)))";
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
qed "less_integ_of_eq_zneg"; 

Goal "~ znegative (integ_of PlusSign)"; 
by (Simp_tac 1); 
qed "not_neg_integ_of_Plus"; 

Goal "znegative (integ_of MinusSign)"; 
by (Simp_tac 1);
qed "neg_integ_of_Minus"; 

Goal "znegative (integ_of (Bcons w x)) = znegative (integ_of w)"; 
by (Asm_simp_tac 1); 
by (int_case_tac "integ_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps ([add_znat, znegative_eq_less_nat0, 
				    symmetric zdiff_def] @ 
				   zcompare_rls)))); 
qed "neg_integ_of_Bcons"; 


(** Less-than-or-equals (<=) **)

Goal "(integ_of x <= integ_of y) = (~ integ_of y < integ_of x)";
by (simp_tac (simpset() addsimps [zle_def]) 1);
qed "le_integ_of_eq_not_less"; 


(*Hide the binary representation of integer constants*)
Delsimps [succ_Bcons, pred_Bcons, min_Bcons, add_Bcons, mult_Bcons, 
          integ_of_Plus, integ_of_Minus, integ_of_Bcons, 
          norm_Plus, norm_Minus, norm_Bcons];

(*Add simplification of arithmetic operations on integer constants*)
Addsimps [integ_of_add RS sym,
          integ_of_minus RS sym,
          integ_of_mult RS sym,
          bin_succ_Bcons1, bin_succ_Bcons0, 
          bin_pred_Bcons1, bin_pred_Bcons0, 
          bin_minus_Bcons1, bin_minus_Bcons0,  
          bin_add_Bcons_Plus, bin_add_Bcons_Minus,
          bin_add_Bcons_Bcons0, bin_add_Bcons_Bcons10, bin_add_Bcons_Bcons11,
          bin_mult_Bcons1, bin_mult_Bcons0, 
          norm_Bcons_Plus_0, norm_Bcons_Plus_1, 
          norm_Bcons_Minus_0, norm_Bcons_Minus_1, 
          norm_Bcons_Bcons];

(*... and simplification of relational operations*)
Addsimps [eq_integ_of_eq, iszero_integ_of_Plus, nonzero_integ_of_Minus,
	  iszero_integ_of_Bcons,
	  less_integ_of_eq_zneg,
	  not_neg_integ_of_Plus, neg_integ_of_Minus, neg_integ_of_Bcons,
	  le_integ_of_eq_not_less];

Goalw [zdiff_def]
     "integ_of v - integ_of w = integ_of(bin_add v (bin_minus w))";
by (Simp_tac 1);
qed "diff_integ_of_eq";

(*... and finally subtraction*)
Addsimps [diff_integ_of_eq];


(** Simplification of inequalities involving numerical constants **)

Goal "(w <= z + #1) = (w<=z | w = z + #1)";
by (simp_tac (simpset() addsimps [zle_eq_zless_or_eq, zless_add1_eq]) 1);
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
by (simp_tac (simpset() addsimps [zless_add1_eq, zle_eq_zless_or_eq]) 1);
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

(*LOOPS as a simprule!*)
Goal "w + #1 < z ==> w < z";
bd zless_zadd_imp_zless 1;
ba 2;
by (Simp_tac 1);
qed "zless_zadd1_imp_zless";


