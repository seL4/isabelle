(*  Title:       RealInt.thy
    ID:         $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   1999 University of Edinburgh
*)

header{*Embedding the Integers into the Reals*}

theory RealInt = RealOrd:

defs (overloaded)
  real_of_int_def:
   "real z == Abs_REAL(UN (i,j): Rep_Integ z. realrel ``
		       {(preal_of_prat(prat_of_pnat(pnat_of_nat i)),
			 preal_of_prat(prat_of_pnat(pnat_of_nat j)))})"


lemma real_of_int_congruent: 
  "congruent intrel (%p. (%(i,j). realrel ``  
   {(preal_of_prat (prat_of_pnat (pnat_of_nat i)),  
     preal_of_prat (prat_of_pnat (pnat_of_nat j)))}) p)"
apply (unfold congruent_def)
apply (auto simp add: pnat_of_nat_add prat_of_pnat_add [symmetric] preal_of_prat_add [symmetric])
done

lemma real_of_int: 
   "real (Abs_Integ (intrel `` {(i, j)})) =  
      Abs_REAL(realrel ``  
        {(preal_of_prat (prat_of_pnat (pnat_of_nat i)),  
          preal_of_prat (prat_of_pnat (pnat_of_nat j)))})"
apply (unfold real_of_int_def)
apply (rule_tac f = Abs_REAL in arg_cong)
apply (simp add: realrel_in_real [THEN Abs_REAL_inverse] 
             UN_equiv_class [OF equiv_intrel real_of_int_congruent])
done

lemma inj_real_of_int: "inj(real :: int => real)"
apply (rule inj_onI)
apply (rule_tac z = x in eq_Abs_Integ)
apply (rule_tac z = y in eq_Abs_Integ)
apply (auto dest!: inj_preal_of_prat [THEN injD] inj_prat_of_pnat [THEN injD]
                   inj_pnat_of_nat [THEN injD]
      simp add: real_of_int preal_of_prat_add [symmetric] prat_of_pnat_add [symmetric] pnat_of_nat_add)
done

lemma real_of_int_zero: "real (int 0) = 0"
apply (unfold int_def real_zero_def)
apply (simp add: real_of_int preal_add_commute)
done

lemma real_of_one: "real (1::int) = (1::real)"
apply (subst int_1 [symmetric])
apply (auto simp add: int_def real_one_def real_of_int preal_of_prat_add [symmetric] pnat_two_eq prat_of_pnat_add [symmetric] pnat_one_iff [symmetric])
done

lemma real_of_int_add: "real (x::int) + real y = real (x + y)"
apply (rule_tac z = x in eq_Abs_Integ)
apply (rule_tac z = y in eq_Abs_Integ)
apply (auto simp add: real_of_int preal_of_prat_add [symmetric]
            prat_of_pnat_add [symmetric] zadd real_add pnat_of_nat_add pnat_add_ac)
done
declare real_of_int_add [symmetric, simp]

lemma real_of_int_minus: "-real (x::int) = real (-x)"
apply (rule_tac z = x in eq_Abs_Integ)
apply (auto simp add: real_of_int real_minus zminus)
done
declare real_of_int_minus [symmetric, simp]

lemma real_of_int_diff: 
  "real (x::int) - real y = real (x - y)"
apply (unfold zdiff_def real_diff_def)
apply (simp only: real_of_int_add real_of_int_minus)
done
declare real_of_int_diff [symmetric, simp]

lemma real_of_int_mult: "real (x::int) * real y = real (x * y)"
apply (rule_tac z = x in eq_Abs_Integ)
apply (rule_tac z = y in eq_Abs_Integ)
apply (auto simp add: real_of_int real_mult zmult
         preal_of_prat_mult [symmetric] pnat_of_nat_mult 
        prat_of_pnat_mult [symmetric] preal_of_prat_add [symmetric]
        prat_of_pnat_add [symmetric] pnat_of_nat_add mult_ac add_ac pnat_add_ac)
done
declare real_of_int_mult [symmetric, simp]

lemma real_of_int_Suc: "real (int (Suc n)) = real (int n) + (1::real)"
by (simp add: real_of_one [symmetric] zadd_int zadd_ac)

declare real_of_one [simp]

(* relating two of the embeddings *)
lemma real_of_int_real_of_nat: "real (int n) = real n"
apply (induct_tac "n")
apply (simp_all only: real_of_int_zero real_of_nat_zero real_of_int_Suc real_of_nat_Suc)
done

lemma real_of_nat_real_of_int: "~neg z ==> real (nat z) = real z"
by (simp add: not_neg_eq_ge_0 real_of_int_real_of_nat [symmetric])

lemma real_of_int_zero_cancel [simp]: "(real x = 0) = (x = int 0)"
by (auto intro: inj_real_of_int [THEN injD] 
         simp only: real_of_int_zero)

lemma real_of_int_less_cancel: "real (x::int) < real y ==> x < y"
apply (rule ccontr, drule linorder_not_less [THEN iffD1])
apply (auto simp add: zle_iff_zadd real_of_int_add [symmetric] real_of_int_real_of_nat linorder_not_le [symmetric])
done

lemma real_of_int_inject [iff]: "(real (x::int) = real y) = (x = y)"
by (blast dest!: inj_real_of_int [THEN injD])

lemma real_of_int_less_mono: "x < y ==> (real (x::int) < real y)"
apply (simp add: linorder_not_le [symmetric])
apply (auto dest!: real_of_int_less_cancel simp add: order_le_less)
done

lemma real_of_int_less_iff [iff]: "(real (x::int) < real y) = (x < y)"
by (blast dest: real_of_int_less_cancel intro: real_of_int_less_mono)

lemma real_of_int_le_iff [simp]: "(real (x::int) \<le> real y) = (x \<le> y)"
by (simp add: linorder_not_less [symmetric])

ML
{*
val real_of_int_congruent = thm"real_of_int_congruent";
val real_of_int = thm"real_of_int";
val inj_real_of_int = thm"inj_real_of_int";
val real_of_int_zero = thm"real_of_int_zero";
val real_of_one = thm"real_of_one";
val real_of_int_add = thm"real_of_int_add";
val real_of_int_minus = thm"real_of_int_minus";
val real_of_int_diff = thm"real_of_int_diff";
val real_of_int_mult = thm"real_of_int_mult";
val real_of_int_Suc = thm"real_of_int_Suc";
val real_of_int_real_of_nat = thm"real_of_int_real_of_nat";
val real_of_nat_real_of_int = thm"real_of_nat_real_of_int";
val real_of_int_zero_cancel = thm"real_of_int_zero_cancel";
val real_of_int_less_cancel = thm"real_of_int_less_cancel";
val real_of_int_inject = thm"real_of_int_inject";
val real_of_int_less_mono = thm"real_of_int_less_mono";
val real_of_int_less_iff = thm"real_of_int_less_iff";
val real_of_int_le_iff = thm"real_of_int_le_iff";
*}


end
