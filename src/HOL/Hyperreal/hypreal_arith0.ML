(*  Title:      HOL/Hyperreal/hypreal_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Instantiation of the generic linear arithmetic package for type hypreal.
*)

local

(* reduce contradictory <= to False *)
val simps = 
    [order_less_irrefl, zero_eq_numeral_0, one_eq_numeral_1,
     add_hypreal_number_of, minus_hypreal_number_of, diff_hypreal_number_of,
     mult_hypreal_number_of, eq_hypreal_number_of, less_hypreal_number_of,
     le_hypreal_number_of_eq_not_less, hypreal_diff_def,
     hypreal_minus_add_distrib, hypreal_minus_minus, hypreal_mult_assoc];

val add_rules =
    map rename_numerals
        [hypreal_add_zero_left, hypreal_add_zero_right,
         hypreal_add_minus, hypreal_add_minus_left,
         hypreal_mult_0, hypreal_mult_0_right,
         hypreal_mult_1, hypreal_mult_1_right,
         hypreal_mult_minus_1, hypreal_mult_minus_1_right];

val simprocs = [Hyperreal_Times_Assoc.conv, 
                Hyperreal_Numeral_Simprocs.combine_numerals]@
               Hyperreal_Numeral_Simprocs.cancel_numerals;

val mono_ss = simpset() addsimps
                [hypreal_add_le_mono,hypreal_add_less_mono,
                 hypreal_add_less_le_mono,hypreal_add_le_less_mono];

val add_mono_thms_hypreal =
  map (fn s => prove_goal (the_context ()) s
                 (fn prems => [cut_facts_tac prems 1, asm_simp_tac mono_ss 1]))
    ["(i <= j) & (k <= l) ==> i + k <= j + (l::hypreal)",
     "(i  = j) & (k <= l) ==> i + k <= j + (l::hypreal)",
     "(i <= j) & (k  = l) ==> i + k <= j + (l::hypreal)",
     "(i  = j) & (k  = l) ==> i + k  = j + (l::hypreal)",
     "(i < j) & (k = l)   ==> i + k < j + (l::hypreal)",
     "(i = j) & (k < l)   ==> i + k < j + (l::hypreal)",
     "(i < j) & (k <= l)  ==> i + k < j + (l::hypreal)",
     "(i <= j) & (k < l)  ==> i + k < j + (l::hypreal)",
     "(i < j) & (k < l)   ==> i + k < j + (l::hypreal)"];

val hypreal_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of (the_context ()))
       (s, HOLogic.boolT))
      ["(m::hypreal) < n", "(m::hypreal) <= n", "(m::hypreal) = n"];

fun cvar(th,_ $ (_ $ _ $ var)) = cterm_of (#sign(rep_thm th)) var;

val hypreal_mult_mono_thms =
 [(rotate_prems 1 hypreal_mult_less_mono2,
   cvar(hypreal_mult_less_mono2, hd(prems_of hypreal_mult_less_mono2))),
  (hypreal_mult_le_mono2,
   cvar(hypreal_mult_le_mono2, hd(tl(prems_of hypreal_mult_le_mono2))))]

in

val fast_hypreal_arith_simproc = mk_simproc
  "fast_hypreal_arith" hypreal_arith_simproc_pats Fast_Arith.lin_arith_prover;

val hypreal_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms @ add_mono_thms_hypreal,
    mult_mono_thms = mult_mono_thms @ hypreal_mult_mono_thms,
    inj_thms = inj_thms, (*FIXME: add hypreal*)
    lessD = lessD,  (*We don't change LA_Data_Ref.lessD because the hypreal ordering is dense!*)
    simpset = simpset addsimps (add_rules @ simps)
                      addsimprocs simprocs}),
  arith_discrete ("HyperDef.hypreal",false),
  Simplifier.change_simpset_of (op addsimprocs) [fast_hypreal_arith_simproc]];

end;


(* Some test data [omitting examples that assume the ordering to be discrete!]
Goal "!!a::hypreal. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);
qed "";

Goal "!!a::hypreal. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);
qed "";

Goal "!!a::hypreal. [| a+b <= i+j; a<=b; i<=j |] ==> a+a <= j+j";
by (fast_arith_tac 1);
qed "";

Goal "!!a::hypreal. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);
qed "";

Goal "!!a::hypreal. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::hypreal. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::hypreal. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);
qed "";

Goal "!!a::hypreal. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
qed "";

Goal "!!a::hypreal. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> 6*a <= 5*l+i";
by (fast_arith_tac 1);
qed "";
*)
