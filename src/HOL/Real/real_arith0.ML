(*  Title:      HOL/Real/real_arith0.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Instantiation of the generic linear arithmetic package for type real.
*)

val add_zero_left = thm"Ring_and_Field.add_0";
val add_zero_right = thm"Ring_and_Field.add_0_right";

val real_mult_left_mono =
    read_instantiate_sg(sign_of RealBin.thy) [("a","?a::real")] mult_left_mono;


local

(* reduce contradictory <= to False *)
val add_rules = 
    [order_less_irrefl, real_numeral_0_eq_0, real_numeral_1_eq_1,
     real_minus_1_eq_m1, 
     add_real_number_of, minus_real_number_of, diff_real_number_of,
     mult_real_number_of, eq_real_number_of, less_real_number_of,
     le_real_number_of_eq_not_less, real_diff_def,
     minus_add_distrib, minus_minus, mult_assoc, minus_zero,
     add_zero_left, add_zero_right, left_minus, right_minus,
     mult_left_zero, mult_right_zero, mult_1, mult_1_right,
     minus_mult_left RS sym, minus_mult_right RS sym];

val simprocs = [Real_Times_Assoc.conv, Real_Numeral_Simprocs.combine_numerals]@
               Real_Numeral_Simprocs.cancel_numerals @
               Real_Numeral_Simprocs.eval_numerals;

val mono_ss = simpset() addsimps
                [add_mono,add_strict_mono,
                 real_add_less_le_mono,real_add_le_less_mono];

val add_mono_thms_real =
  map (fn s => prove_goal (the_context ()) s
                 (fn prems => [cut_facts_tac prems 1, asm_simp_tac mono_ss 1]))
    ["(i <= j) & (k <= l) ==> i + k <= j + (l::real)",
     "(i  = j) & (k <= l) ==> i + k <= j + (l::real)",
     "(i <= j) & (k  = l) ==> i + k <= j + (l::real)",
     "(i  = j) & (k  = l) ==> i + k  = j + (l::real)",
     "(i < j) & (k = l)   ==> i + k < j + (l::real)",
     "(i = j) & (k < l)   ==> i + k < j + (l::real)",
     "(i < j) & (k <= l)  ==> i + k < j + (l::real)",
     "(i <= j) & (k < l)  ==> i + k < j + (l::real)",
     "(i < j) & (k < l)   ==> i + k < j + (l::real)"];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val real_mult_mono_thms =
 [(rotate_prems 1 real_mult_less_mono2,
   cvar(real_mult_less_mono2, hd(prems_of real_mult_less_mono2))),
  (real_mult_left_mono,
   cvar(real_mult_left_mono, hd(tl(prems_of real_mult_left_mono))))]

in

val fast_real_arith_simproc = Simplifier.simproc (Theory.sign_of (the_context ()))
  "fast_real_arith" ["(m::real) < n","(m::real) <= n", "(m::real) = n"]
  Fast_Arith.lin_arith_prover;

val real_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms @ add_mono_thms_real,
    mult_mono_thms = mult_mono_thms @ real_mult_mono_thms,
    inj_thms = inj_thms, (*FIXME: add real*)
    lessD = lessD,  (*We don't change LA_Data_Ref.lessD because the real ordering is dense!*)
    simpset = simpset addsimps add_rules
                      addsimprocs simprocs}),
  arith_discrete ("RealDef.real",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_real_arith_simproc]];

(* some thms for injection nat => real:
real_of_nat_zero
?zero_eq_numeral_0
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
