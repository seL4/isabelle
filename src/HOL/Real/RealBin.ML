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

Goalw [rabs_def]
  "P(rabs x) = ((#0 <= x --> P x) & (x < #0 --> P(-x)))";
by(auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "rabs_split";

arith_tac_split_thms := !arith_tac_split_thms @ [rabs_split];

(** Tests **)
Goal "(x + y = x) = (y = (#0::real))";
by(arith_tac 1);

Goal "(x + y = y) = (x = (#0::real))";
by(arith_tac 1);

Goal "(x + y = (#0::real)) = (x = -y)";
by(arith_tac 1);

Goal "(x + y = (#0::real)) = (y = -x)";
by(arith_tac 1);

Goal "((x + y) < (x + z)) = (y < (z::real))";
by(arith_tac 1);

Goal "((x + z) < (y + z)) = (x < (y::real))";
by(arith_tac 1);

Goal "(~ x < y) = (y <= (x::real))";
by(arith_tac 1);

Goal "~(x < y & y < (x::real))";
by(arith_tac 1);

Goal "(x::real) < y ==> ~ y < x";
by(arith_tac 1);

Goal "((x::real) ~= y) = (x < y | y < x)";
by(arith_tac 1);

Goal "(~ x <= y) = (y < (x::real))";
by(arith_tac 1);

Goal "x <= y | y <= (x::real)";
by(arith_tac 1);

Goal "x <= y | y < (x::real)";
by(arith_tac 1);

Goal "x < y | y <= (x::real)";
by(arith_tac 1);

Goal "x <= (x::real)";
by(arith_tac 1);

Goal "((x::real) <= y) = (x < y | x = y)";
by(arith_tac 1);

Goal "((x::real) <= y & y <= x) = (x = y)";
by(arith_tac 1);

Goal "~(x < y & y <= (x::real))";
by(arith_tac 1);

Goal "~(x <= y & y < (x::real))";
by(arith_tac 1);

Goal "(-x < (#0::real)) = (#0 < x)";
by(arith_tac 1);

Goal "((#0::real) < -x) = (x < #0)";
by(arith_tac 1);

Goal "(-x <= (#0::real)) = (#0 <= x)";
by(arith_tac 1);

Goal "((#0::real) <= -x) = (x <= #0)";
by(arith_tac 1);

Goal "(x::real) = y | x < y | y < x";
by(arith_tac 1);

Goal "(x::real) = #0 | #0 < x | #0 < -x";
by(arith_tac 1);

Goal "(#0::real) <= x | #0 <= -x";
by(arith_tac 1);

Goal "((x::real) + y <= x + z) = (y <= z)";
by(arith_tac 1);

Goal "((x::real) + z <= y + z) = (x <= y)";
by(arith_tac 1);

Goal "(w::real) < x & y < z ==> w + y < x + z";
by(arith_tac 1);

Goal "(w::real) <= x & y <= z ==> w + y <= x + z";
by(arith_tac 1);

Goal "(#0::real) <= x & #0 <= y ==> #0 <= x + y";
by(arith_tac 1);

Goal "(#0::real) < x & #0 < y ==> #0 < x + y";
by(arith_tac 1);

Goal "(-x < y) = (#0 < x + (y::real))";
by(arith_tac 1);

Goal "(x < -y) = (x + y < (#0::real))";
by(arith_tac 1);

Goal "(y < x + -z) = (y + z < (x::real))";
by(arith_tac 1);

Goal "(x + -y < z) = (x < z + (y::real))";
by(arith_tac 1);

Goal "x <= y ==> x < y + (#1::real)";
by(arith_tac 1);

Goal "(x - y) + y = (x::real)";
by(arith_tac 1);

Goal "y + (x - y) = (x::real)";
by(arith_tac 1);

Goal "x - x = (#0::real)";
by(arith_tac 1);

Goal "(x - y = #0) = (x = (y::real))";
by(arith_tac 1);

Goal "((#0::real) <= x + x) = (#0 <= x)";
by(arith_tac 1);

Goal "(-x <= x) = ((#0::real) <= x)";
by(arith_tac 1);

Goal "(x <= -x) = (x <= (#0::real))";
by(arith_tac 1);

Goal "(-x = (#0::real)) = (x = #0)";
by(arith_tac 1);

Goal "-(x - y) = y - (x::real)";
by(arith_tac 1);

Goal "((#0::real) < x - y) = (y < x)";
by(arith_tac 1);

Goal "((#0::real) <= x - y) = (y <= x)";
by(arith_tac 1);

Goal "(x + y) - x = (y::real)";
by(arith_tac 1);

Goal "(-x = y) = (x = (-y::real))";
by(arith_tac 1);

Goal "x < (y::real) ==> ~(x = y)";
by(arith_tac 1);

Goal "(x <= x + y) = ((#0::real) <= y)";
by(arith_tac 1);

Goal "(y <= x + y) = ((#0::real) <= x)";
by(arith_tac 1);

Goal "(x < x + y) = ((#0::real) < y)";
by(arith_tac 1);

Goal "(y < x + y) = ((#0::real) < x)";
by(arith_tac 1);

Goal "(x - y) - x = (-y::real)";
by(arith_tac 1);

Goal "(x + y < z) = (x < z - (y::real))";
by(arith_tac 1);

Goal "(x - y < z) = (x < z + (y::real))";
by(arith_tac 1);

Goal "(x < y - z) = (x + z < (y::real))";
by(arith_tac 1);

Goal "(x <= y - z) = (x + z <= (y::real))";
by(arith_tac 1);

Goal "(x - y <= z) = (x <= z + (y::real))";
by(arith_tac 1);

Goal "(-x < -y) = (y < (x::real))";
by(arith_tac 1);

Goal "(-x <= -y) = (y <= (x::real))";
by(arith_tac 1);

Goal "(a + b) - (c + d) = (a - c) + (b - (d::real))";
by(arith_tac 1);

Goal "(#0::real) - x = -x";
by(arith_tac 1);

Goal "x - (#0::real) = x";
by(arith_tac 1);

Goal "w <= x & y < z ==> w + y < x + (z::real)";
by(arith_tac 1);

Goal "w < x & y <= z ==> w + y < x + (z::real)";
by(arith_tac 1);

Goal "(#0::real) <= x & #0 < y ==> #0 < x + (y::real)";
by(arith_tac 1);

Goal "(#0::real) < x & #0 <= y ==> #0 < x + y";
by(arith_tac 1);

Goal "-x - y = -(x + (y::real))";
by(arith_tac 1);

Goal "x - (-y) = x + (y::real)";
by(arith_tac 1);

Goal "-x - -y = y - (x::real)";
by(arith_tac 1);

Goal "(a - b) + (b - c) = a - (c::real)";
by(arith_tac 1);

Goal "(x = y - z) = (x + z = (y::real))";
by(arith_tac 1);

Goal "(x - y = z) = (x = z + (y::real))";
by(arith_tac 1);

Goal "x - (x - y) = (y::real)";
by(arith_tac 1);

Goal "x - (x + y) = -(y::real)";
by(arith_tac 1);

Goal "x = y ==> x <= (y::real)";
by(arith_tac 1);

Goal "(#0::real) < x ==> ~(x = #0)";
by(arith_tac 1);

Goal "(x + y) * (x - y) = (x * x) - (y * y)";

Goal "(-x = -y) = (x = (y::real))";
by(arith_tac 1);

Goal "(-x < -y) = (y < (x::real))";
by(arith_tac 1);

Goal "!!a::real. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);

Goal "!!a::real. [| a < b; c < d |] ==> a-d <= b+(-c)";
by (fast_arith_tac 1);

Goal "!!a::real. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b <= i+j; a<=b; i<=j |] \
\     ==> a+a <= j+j";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b < i+j; a<b; i<j |] \
\     ==> a+a < j+j";
by (fast_arith_tac 1);

Goal "!!a::real. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);

(* Too slow. Needs "combine_coefficients" simproc
Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
*)

