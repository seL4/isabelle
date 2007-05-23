(*  Title:      HOL/Real/real_arith.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen
    Copyright   1999 TU Muenchen

Simprocs for common factor cancellation & Rational coefficient handling

Instantiation of the generic linear arithmetic package for type real.
*)

local

val simps = [@{thm real_of_nat_zero}, @{thm real_of_nat_Suc}, @{thm real_of_nat_add},
             @{thm real_of_nat_mult}, @{thm real_of_int_zero}, @{thm real_of_one},
             @{thm real_of_int_add}, @{thm real_of_int_minus}, @{thm real_of_int_diff},
             @{thm real_of_int_mult}, @{thm real_of_int_of_nat_eq},
             @{thm real_of_nat_number_of}, @{thm real_number_of}]

val nat_inj_thms = [@{thm real_of_nat_le_iff} RS iffD2,
                    @{thm real_of_nat_inject} RS iffD2]
(* not needed because x < (y::nat) can be rewritten as Suc x <= y:
                    real_of_nat_less_iff RS iffD2 *)

val int_inj_thms = [@{thm real_of_int_le_iff} RS iffD2,
                    @{thm real_of_int_inject} RS iffD2]
(* not needed because x < (y::int) can be rewritten as x + 1 <= y:
                    real_of_int_less_iff RS iffD2 *)

in

val fast_real_arith_simproc =
 Simplifier.simproc (the_context ())
  "fast_real_arith" ["(m::real) < n","(m::real) <= n", "(m::real) = n"]
  Fast_Arith.lin_arith_prover;

val real_arith_setup =
  Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms,
    inj_thms = int_inj_thms @ nat_inj_thms @ inj_thms,
    lessD = lessD,  (*Can't change LA_Data_Ref.lessD: the reals are dense!*)
    neqE = neqE,
    simpset = simpset addsimps simps}) #>
  arith_inj_const ("RealDef.real", HOLogic.natT --> HOLogic.realT) #>
  arith_inj_const ("RealDef.real", HOLogic.intT --> HOLogic.realT)

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



