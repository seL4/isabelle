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

Goalw [real_number_of_def] "(0::real) = #0";
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

Goal "(#2::real) = #1 + #1";
by (Simp_tac 1);
val lemma = result();

(*For specialist use: NOT as default simprules*)
Goal "#2 * z = (z+z::real)";
by (simp_tac (simpset_of RealDef.thy
	      addsimps [lemma, real_add_mult_distrib,
			one_eq_numeral_1 RS sym]) 1);
qed "real_mult_2";

Goal "z * #2 = (z+z::real)";
by (stac real_mult_commute 1 THEN rtac real_mult_2 1);
qed "real_mult_2_right";


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

(*** New versions of existing theorems involving 0, 1r ***)

Goal "- #1 = (#-1::real)";
by (Simp_tac 1);
qed "minus_numeral_one";


(*Maps 0 to #0 and 1r to #1 and -1r to #-1*)
val real_numeral_ss = 
    HOL_ss addsimps [zero_eq_numeral_0, one_eq_numeral_1, 
		     minus_numeral_one];

fun rename_numerals thy th = simplify real_numeral_ss (change_theory thy th);


(*Now insert some identities previously stated for 0 and 1r*)

(** RealDef & Real **)

Addsimps (map (rename_numerals thy) 
	  [real_minus_zero, real_minus_zero_iff,
	   real_add_zero_left, real_add_zero_right, 
	   real_diff_0, real_diff_0_right,
	   real_mult_0_right, real_mult_0, real_mult_1_right, real_mult_1,
	   real_mult_minus_1_right, real_mult_minus_1, real_rinv_1,
	   real_minus_zero_less_iff]);

AddIffs (map (rename_numerals thy) [real_mult_is_0, real_0_is_mult]);

bind_thm ("real_0_less_times_iff", 
	  rename_numerals thy real_zero_less_times_iff);
bind_thm ("real_0_le_times_iff", 
	  rename_numerals thy real_zero_le_times_iff);
bind_thm ("real_times_less_0_iff", 
	  rename_numerals thy real_times_less_zero_iff);
bind_thm ("real_times_le_0_iff", 
	  rename_numerals thy real_times_le_zero_iff);


(*Perhaps add some theorems that aren't in the default simpset, as
  done in Integ/NatBin.ML*)


(*  Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Instantiate linear arithmetic decision procedure for the reals.
FIXME: multiplication with constants (eg #2 * x) does not work yet.
Solution: there should be a simproc for combining coefficients.
*)

let

(* reduce contradictory <= to False *)
val simps = [order_less_irrefl,zero_eq_numeral_0,one_eq_numeral_1,
  add_real_number_of,minus_real_number_of,diff_real_number_of,
  mult_real_number_of,eq_real_number_of,less_real_number_of,
  le_real_number_of_eq_not_less];

val simprocs = [Real_Cancel.sum_conv, Real_Cancel.rel_conv];

val add_mono_thms =
  map (fn s => prove_goal thy s
                 (fn prems => [cut_facts_tac prems 1,
                      asm_simp_tac (simpset() addsimps
     [real_add_le_mono,real_add_less_mono,
      real_add_less_le_mono,real_add_le_less_mono]) 1]))
    ["(i <= j) & (k <= l) ==> i + k <= j + (l::real)",
     "(i  = j) & (k <= l) ==> i + k <= j + (l::real)",
     "(i <= j) & (k  = l) ==> i + k <= j + (l::real)",
     "(i  = j) & (k  = l) ==> i + k  = j + (l::real)",
     "(i < j) & (k = l)   ==> i + k < j + (l::real)",
     "(i = j) & (k < l)   ==> i + k < j + (l::real)",
     "(i < j) & (k <= l)  ==> i + k < j + (l::real)",
     "(i <= j) & (k < l)  ==> i + k < j + (l::real)",
     "(i < j) & (k < l)   ==> i + k < j + (l::real)"];

in
LA_Data_Ref.add_mono_thms := !LA_Data_Ref.add_mono_thms @ add_mono_thms;
LA_Data_Ref.ss_ref := !LA_Data_Ref.ss_ref addsimps simps
                      addsimprocs simprocs;
LA_Data_Ref.discrete := !LA_Data_Ref.discrete @ [("RealDef.real",false)]
end;

let
val real_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of thy) (s, HOLogic.boolT))
      ["(m::real) < n","(m::real) <= n", "(m::real) = n"];

val fast_real_arith_simproc = mk_simproc
  "fast_real_arith" real_arith_simproc_pats Fast_Arith.lin_arith_prover;
in
Addsimprocs [fast_real_arith_simproc]
end;
 

Addsimps [zero_eq_numeral_0,one_eq_numeral_1];

(* added by jdf *)
fun full_rename_numerals thy th = 
    asm_full_simplify real_numeral_ss (change_theory thy th);


(** Simplification of arithmetic when nested to the right **)

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::real)";
by Auto_tac; 
qed "real_add_number_of_left";

Goal "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::real)";
by (simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
qed "real_mult_number_of_left";

Goalw [real_diff_def]
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::real)";
by (rtac real_add_number_of_left 1);
qed "real_add_number_of_diff1";

Goal "number_of v + (c - number_of w) = \
\    number_of (bin_add v (bin_minus w)) + (c::real)";
by (stac (diff_real_number_of RS sym) 1);
by Auto_tac;
qed "real_add_number_of_diff2";

Addsimps [real_add_number_of_left, real_mult_number_of_left,
	  real_add_number_of_diff1, real_add_number_of_diff2]; 

