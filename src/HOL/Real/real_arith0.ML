(*  Title:      HOL/Real/real_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Instantiation of the generic linear arithmetic package for type real.
*)

local

(* reduce contradictory <= to False *)
val simps = [order_less_irrefl, zero_eq_numeral_0, one_eq_numeral_1,
             add_real_number_of, minus_real_number_of, diff_real_number_of,
             mult_real_number_of, eq_real_number_of, less_real_number_of,
             le_real_number_of_eq_not_less, real_diff_def,
             real_minus_add_distrib, real_minus_minus, real_mult_assoc];

val add_rules =
    map rename_numerals
        [real_add_zero_left, real_add_zero_right,
         real_add_minus, real_add_minus_left,
         real_mult_0, real_mult_0_right,
         real_mult_1, real_mult_1_right,
         real_mult_minus_1, real_mult_minus_1_right];

val simprocs = [Real_Times_Assoc.conv, Real_Numeral_Simprocs.combine_numerals]@
               Real_Numeral_Simprocs.cancel_numerals;

val mono_ss = simpset() addsimps
                [real_add_le_mono,real_add_less_mono,
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

val real_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of (the_context ())) (s, HOLogic.boolT))
      ["(m::real) < n","(m::real) <= n", "(m::real) = n"];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val real_mult_mono_thms =
 [(rotate_prems 1 real_mult_less_mono2,
   cvar(real_mult_less_mono2, hd(prems_of real_mult_less_mono2))),
  (real_mult_le_mono2,
   cvar(real_mult_le_mono2, hd(tl(prems_of real_mult_le_mono2))))]

in

val fast_real_arith_simproc = mk_simproc
  "fast_real_arith" real_arith_simproc_pats Fast_Arith.lin_arith_prover;

val real_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms @ add_mono_thms_real,
    mult_mono_thms = mult_mono_thms @ real_mult_mono_thms,
    inj_thms = inj_thms, (*FIXME: add real*)
    lessD = lessD,  (*We don't change LA_Data_Ref.lessD because the real ordering is dense!*)
    simpset = simpset addsimps (add_rules @ simps)
                      addsimprocs simprocs}),
  arith_discrete ("RealDef.real",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_real_arith_simproc]];

(* some thms for injection nat => real:
real_of_nat_zero
zero_eq_numeral_0
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
\     ==> # 6*a <= # 5*l+i";
by (fast_arith_tac 1);
qed "";
*)
