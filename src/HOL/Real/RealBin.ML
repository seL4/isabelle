(*  Title:      HOL/RealBin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the reals (integer literals only)
*)

(** real_of_int (coercion from int to real) **)

Goal "real_of_int (number_of w) = number_of w";
by (simp_tac (simpset() addsimps [real_number_of_def]) 1);
qed "real_number_of";
Addsimps [real_number_of];

Goalw [real_number_of_def] "0r = #0";
by (simp_tac (simpset() addsimps [real_of_int_zero RS sym]) 1);
qed "zero_eq_numeral_0";

Goalw [real_number_of_def] "1r = #1";
by (simp_tac (simpset() addsimps [real_of_int_one RS sym]) 1);
qed "one_eq_numeral_1";

(** Addition **)

Goal "(number_of v :: real) + number_of v' = number_of (bin_add v v')";
by (simp_tac
    (simpset_of Int.thy addsimps [real_number_of_def, 
				  real_of_int_add, number_of_add]) 1);
qed "add_real_number_of";

Addsimps [add_real_number_of];


(** Subtraction **)

Goalw [real_number_of_def] "- (number_of w :: real) = number_of (bin_minus w)";
by (simp_tac
    (simpset_of Int.thy addsimps [number_of_minus, real_of_int_minus]) 1);
qed "minus_real_number_of";

Goalw [real_number_of_def]
   "(number_of v :: real) - number_of w = number_of (bin_add v (bin_minus w))";
by (simp_tac
    (simpset_of Int.thy addsimps [diff_number_of_eq, real_of_int_diff]) 1);
qed "diff_real_number_of";

Addsimps [minus_real_number_of, diff_real_number_of];


(** Multiplication **)

Goal "(number_of v :: real) * number_of v' = number_of (bin_mult v v')";
by (simp_tac
    (simpset_of Int.thy addsimps [real_number_of_def, 
				  real_of_int_mult, number_of_mult]) 1);
qed "mult_real_number_of";

Addsimps [mult_real_number_of];


(*** Comparisons ***)

(** Equals (=) **)

Goal "((number_of v :: real) = number_of v') = \
\     iszero (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (simpset_of Int.thy addsimps [real_number_of_def, 
				  real_of_int_eq_iff, eq_number_of_eq]) 1);
qed "eq_real_number_of";

Addsimps [eq_real_number_of];

(** Less-than (<) **)

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "((number_of v :: real) < number_of v') = \
\     neg (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (simpset_of Int.thy addsimps [real_number_of_def, real_of_int_less_iff, 
				  less_number_of_eq_neg]) 1);
qed "less_real_number_of";

Addsimps [less_real_number_of];


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::real)) = \
\     (~ number_of y < (number_of x::real))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_real_number_of_eq_not_less"; 

Addsimps [le_real_number_of_eq_not_less];


(** rabs (absolute value) **)

Goalw [rabs_def]
     "rabs (number_of v :: real) = \
\       (if neg (number_of v) then number_of (bin_minus v) \
\        else number_of v)";
by (simp_tac
    (simpset_of Int.thy addsimps
      bin_arith_simps@
      [minus_real_number_of, zero_eq_numeral_0, le_real_number_of_eq_not_less,
       less_real_number_of, real_of_int_le_iff]) 1);
qed "rabs_nat_number_of";

Addsimps [rabs_nat_number_of];


(*** New versions of existing theorems involving 0r, 1r ***)

Goal "- #1 = (#-1::real)";
by (Simp_tac 1);
qed "minus_numeral_one";


(*Maps 0r to #0 and 1r to #1 and -1r to #-1*)
val real_numeral_ss = 
    HOL_ss addsimps [zero_eq_numeral_0, one_eq_numeral_1, 
		     minus_numeral_one];

fun rename_numerals thy th = simplify real_numeral_ss (change_theory thy th);


fun inst x t = read_instantiate_sg (sign_of RealBin.thy) [(x,t)];


(*Now insert some identities previously stated for 0r and 1r*)

(** RealDef & Real **)

Addsimps (map (rename_numerals thy) 
	  [real_minus_zero, real_minus_zero_iff,
	   real_add_zero_left, real_add_zero_right, 
	   real_diff_0, real_diff_0_right,
	   real_mult_0_right, real_mult_0, real_mult_1_right, real_mult_1,
	   real_mult_minus_1_right, real_mult_minus_1, real_rinv_1,
	   real_minus_zero_less_iff]);

(** RealPow **)

Addsimps (map (rename_numerals thy) 
	  [realpow_zero, realpow_two_le, realpow_zero_le,
	   realpow_eq_one, rabs_minus_realpow_one, rabs_realpow_minus_one,
	   realpow_minus_one, realpow_minus_one2, realpow_minus_one_odd]);

(*Perhaps add some theorems that aren't in the default simpset, as
  done in Integ/NatBin.ML*)

