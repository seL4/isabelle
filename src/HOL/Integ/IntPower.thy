(*  Title:	IntPower.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

Integer powers 
*)

theory IntPower = IntDiv:

instance int :: power ..

primrec
  power_0:   "p ^ 0 = 1"
  power_Suc: "p ^ (Suc n) = (p::int) * (p ^ n)"


lemma zpower_zmod: "((x::int) mod m)^y mod m = x^y mod m"
apply (induct_tac "y", auto)
apply (rule zmod_zmult1_eq [THEN trans])
apply (simp (no_asm_simp))
apply (rule zmod_zmult_distrib [symmetric])
done

lemma zpower_1 [simp]: "1^y = (1::int)"
by (induct_tac "y", auto)

lemma zpower_zmult_distrib: "(x*z)^y = ((x^y)*(z^y)::int)"
by (induct_tac "y", auto)

lemma zpower_zadd_distrib: "x^(y+z) = ((x^y)*(x^z)::int)"
by (induct_tac "y", auto)

lemma zpower_zpower: "(x^y)^z = (x^(y*z)::int)"
apply (induct_tac "y", auto)
apply (subst zpower_zmult_distrib)
apply (subst zpower_zadd_distrib)
apply (simp (no_asm_simp))
done


(*** Logical equivalences for inequalities ***)

lemma zpower_eq_0_iff [simp]: "(x^n = 0) = (x = (0::int) & 0<n)"
by (induct_tac "n", auto)

lemma zero_less_zpower_abs_iff [simp]:
     "(0 < (abs x)^n) = (x \<noteq> (0::int) | n=0)"
apply (induct_tac "n")
apply (auto simp add: int_0_less_mult_iff)
done

lemma zero_le_zpower_abs [simp]: "(0::int) <= (abs x)^n"
apply (induct_tac "n")
apply (auto simp add: int_0_le_mult_iff)
done

ML
{*
val zpower_zmod = thm "zpower_zmod";
val zpower_1 = thm "zpower_1";
val zpower_zmult_distrib = thm "zpower_zmult_distrib";
val zpower_zadd_distrib = thm "zpower_zadd_distrib";
val zpower_zpower = thm "zpower_zpower";
val zpower_eq_0_iff = thm "zpower_eq_0_iff";
val zero_less_zpower_abs_iff = thm "zero_less_zpower_abs_iff";
val zero_le_zpower_abs = thm "zero_le_zpower_abs";
*}

end

