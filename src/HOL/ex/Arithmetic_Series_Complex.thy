(*  Title:      HOL/ex/Arithmetic_Series_Complex.thy
    Author:     Benjamin Porter, 2006
*)


header {* Arithmetic Series for Reals *}

theory Arithmetic_Series_Complex
imports "../RealDef"
begin

lemma arith_series_real:
  "(2::real) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
  of_nat n * (a + (a + of_nat(n - 1)*d))"
  by (fact arith_series_general) (* FIXME: duplicate *)

end
