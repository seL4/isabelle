(*  Title:      HOL/Real/real_arith0.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type real.
*)

(*FIXME DELETE*)
val real_mult_left_mono =
    read_instantiate_sg(sign_of (the_context())) [("a","?a::real")] mult_left_mono;

val real_abs_def = thm "real_abs_def";

val real_le_def = thm "real_le_def";
val real_diff_def = thm "real_diff_def";
val real_divide_def = thm "real_divide_def";

val realrel_iff = thm"realrel_iff";
val realrel_refl = thm"realrel_refl";
val equiv_realrel = thm"equiv_realrel";
val equiv_realrel_iff = thm"equiv_realrel_iff";
val realrel_in_real = thm"realrel_in_real";
val inj_on_Abs_REAL = thm"inj_on_Abs_REAL";
val eq_realrelD = thm"eq_realrelD";
val inj_Rep_REAL = thm"inj_Rep_REAL";
val inj_real_of_preal = thm"inj_real_of_preal";
val eq_Abs_REAL = thm"eq_Abs_REAL";
val real_minus_congruent = thm"real_minus_congruent";
val real_minus = thm"real_minus";
val real_add = thm"real_add";
val real_add_commute = thm"real_add_commute";
val real_add_assoc = thm"real_add_assoc";
val real_add_zero_left = thm"real_add_zero_left";
val real_add_zero_right = thm"real_add_zero_right";

val real_mult = thm"real_mult";
val real_mult_commute = thm"real_mult_commute";
val real_mult_assoc = thm"real_mult_assoc";
val real_mult_1 = thm"real_mult_1";
val real_mult_1_right = thm"real_mult_1_right";
val preal_le_linear = thm"preal_le_linear";
val real_mult_inverse_left = thm"real_mult_inverse_left";
val real_not_refl2 = thm"real_not_refl2";
val real_of_preal_add = thm"real_of_preal_add";
val real_of_preal_mult = thm"real_of_preal_mult";
val real_of_preal_trichotomy = thm"real_of_preal_trichotomy";
val real_of_preal_minus_less_zero = thm"real_of_preal_minus_less_zero";
val real_of_preal_not_minus_gt_zero = thm"real_of_preal_not_minus_gt_zero";
val real_of_preal_zero_less = thm"real_of_preal_zero_less";
val real_le_imp_less_or_eq = thm"real_le_imp_less_or_eq";
val real_le_refl = thm"real_le_refl";
val real_le_linear = thm"real_le_linear";
val real_le_trans = thm"real_le_trans";
val real_le_anti_sym = thm"real_le_anti_sym";
val real_less_le = thm"real_less_le";
val real_less_sum_gt_zero = thm"real_less_sum_gt_zero";
val real_gt_zero_preal_Ex = thm "real_gt_zero_preal_Ex";
val real_gt_preal_preal_Ex = thm "real_gt_preal_preal_Ex";
val real_ge_preal_preal_Ex = thm "real_ge_preal_preal_Ex";
val real_less_all_preal = thm "real_less_all_preal";
val real_less_all_real2 = thm "real_less_all_real2";
val real_of_preal_le_iff = thm "real_of_preal_le_iff";
val real_mult_order = thm "real_mult_order";
val real_zero_less_one = thm "real_zero_less_one";
val real_add_less_le_mono = thm "real_add_less_le_mono";
val real_add_le_less_mono = thm "real_add_le_less_mono";
val real_add_order = thm "real_add_order";
val real_le_add_order = thm "real_le_add_order";
val real_le_square = thm "real_le_square";
val real_mult_less_mono2 = thm "real_mult_less_mono2";

val real_mult_less_iff1 = thm "real_mult_less_iff1";
val real_mult_le_cancel_iff1 = thm "real_mult_le_cancel_iff1";
val real_mult_le_cancel_iff2 = thm "real_mult_le_cancel_iff2";
val real_mult_less_mono = thm "real_mult_less_mono";
val real_mult_less_mono' = thm "real_mult_less_mono'";
val real_sum_squares_cancel = thm "real_sum_squares_cancel";
val real_sum_squares_cancel2 = thm "real_sum_squares_cancel2";

val real_mult_left_cancel = thm"real_mult_left_cancel";
val real_mult_right_cancel = thm"real_mult_right_cancel";
val real_inverse_unique = thm "real_inverse_unique";
val real_inverse_gt_one = thm "real_inverse_gt_one";

val real_of_int_zero = thm"real_of_int_zero";
val real_of_one = thm"real_of_one";
val real_of_int_add = thm"real_of_int_add";
val real_of_int_minus = thm"real_of_int_minus";
val real_of_int_diff = thm"real_of_int_diff";
val real_of_int_mult = thm"real_of_int_mult";
val real_of_int_real_of_nat = thm"real_of_int_real_of_nat";
val real_of_int_inject = thm"real_of_int_inject";
val real_of_int_less_iff = thm"real_of_int_less_iff";
val real_of_int_le_iff = thm"real_of_int_le_iff";
val real_of_nat_zero = thm "real_of_nat_zero";
val real_of_nat_one = thm "real_of_nat_one";
val real_of_nat_add = thm "real_of_nat_add";
val real_of_nat_Suc = thm "real_of_nat_Suc";
val real_of_nat_less_iff = thm "real_of_nat_less_iff";
val real_of_nat_le_iff = thm "real_of_nat_le_iff";
val real_of_nat_ge_zero = thm "real_of_nat_ge_zero";
val real_of_nat_Suc_gt_zero = thm "real_of_nat_Suc_gt_zero";
val real_of_nat_mult = thm "real_of_nat_mult";
val real_of_nat_inject = thm "real_of_nat_inject";
val real_of_nat_diff = thm "real_of_nat_diff";
val real_of_nat_zero_iff = thm "real_of_nat_zero_iff";
val real_of_nat_gt_zero_cancel_iff = thm "real_of_nat_gt_zero_cancel_iff";
val real_of_nat_le_zero_cancel_iff = thm "real_of_nat_le_zero_cancel_iff";
val not_real_of_nat_less_zero = thm "not_real_of_nat_less_zero";
val real_of_nat_ge_zero_cancel_iff = thm "real_of_nat_ge_zero_cancel_iff";


(****Instantiation of the generic linear arithmetic package****)

local

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val real_mult_mono_thms =
 [(rotate_prems 1 real_mult_less_mono2,
   cvar(real_mult_less_mono2, hd(prems_of real_mult_less_mono2))),
  (real_mult_left_mono,
   cvar(real_mult_left_mono, hd(tl(prems_of real_mult_left_mono))))]

val simps = [real_of_nat_zero, real_of_nat_Suc, real_of_nat_add, 
       real_of_nat_mult, real_of_int_zero, real_of_one, real_of_int_add RS sym,
       real_of_int_minus RS sym, real_of_int_diff RS sym,
       real_of_int_mult RS sym];

val int_inj_thms = [real_of_int_le_iff RS iffD2, real_of_int_less_iff RS iffD2,
                    real_of_int_inject RS iffD2];

val nat_inj_thms = [real_of_nat_le_iff RS iffD2, real_of_nat_less_iff RS iffD2,
                    real_of_nat_inject RS iffD2];

in

val fast_real_arith_simproc =
 Simplifier.simproc (Theory.sign_of (the_context ()))
  "fast_real_arith" ["(m::real) < n","(m::real) <= n", "(m::real) = n"]
  Fast_Arith.lin_arith_prover;

val real_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms @ real_mult_mono_thms,
    inj_thms = int_inj_thms @ nat_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the reals are dense!*)
    simpset = simpset addsimps simps}),
  arith_inj_const ("RealDef.real", HOLogic.natT --> HOLogic.realT),
  arith_inj_const ("RealDef.real", HOLogic.intT --> HOLogic.realT),
  arith_discrete ("RealDef.real",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_real_arith_simproc]];

(* some thms for injection nat => real:
real_of_nat_zero
real_of_nat_add
*)

end;


(* Some test data [omitting examples that assume the ordering to be discrete!]
Goal "!!a::real. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b <= i+j; a<=b; i<=j |] ==> a+a <= j+j";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> 6*a <= 5*l+i";
by (fast_arith_tac 1);
qed "";

Goal "a<=b ==> a < b+(1::real)";
by (fast_arith_tac 1);
qed "";

Goal "a<=b ==> a-(3::real) < b";
by (fast_arith_tac 1);
qed "";

Goal "a<=b ==> a-(1::real) < b";
by (fast_arith_tac 1);
qed "";

*)



