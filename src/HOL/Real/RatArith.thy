(*  Title:      HOL/RatArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2004  University of Cambridge

Binary arithmetic and simplification for the rats

This case is reduced to that for the integers
*)

theory RatArith = Rational
files ("rat_arith.ML"):

instance rat :: number ..

defs (overloaded)
  rat_number_of_def:
    "(number_of v :: rat) == of_int (number_of v)"
     (*::bin=>rat         ::bin=>int*)


lemma rat_numeral_0_eq_0: "Numeral0 = (0::rat)"
by (simp add: rat_number_of_def zero_rat [symmetric])

lemma rat_numeral_1_eq_1: "Numeral1 = (1::rat)"
by (simp add: rat_number_of_def one_rat [symmetric])


subsection{*Arithmetic Operations On Numerals*}

lemma add_rat_number_of [simp]:
     "(number_of v :: rat) + number_of v' = number_of (bin_add v v')" 
by (simp only: rat_number_of_def of_int_add number_of_add)

lemma minus_rat_number_of [simp]:
     "- (number_of w :: rat) = number_of (bin_minus w)"
by (simp only: rat_number_of_def of_int_minus number_of_minus)

lemma diff_rat_number_of [simp]: 
   "(number_of v :: rat) - number_of w = number_of (bin_add v (bin_minus w))"
by (simp only: add_rat_number_of minus_rat_number_of diff_minus)

lemma mult_rat_number_of [simp]:
     "(number_of v :: rat) * number_of v' = number_of (bin_mult v v')"
by (simp only: rat_number_of_def of_int_mult number_of_mult)

text{*Lemmas for specialist use, NOT as default simprules*}
lemma rat_mult_2: "2 * z = (z+z::rat)"
proof -
  have eq: "(2::rat) = 1 + 1"
    by (simp del: rat_number_of_def add: rat_numeral_1_eq_1 [symmetric])
  thus ?thesis by (simp add: eq left_distrib)
qed

lemma rat_mult_2_right: "z * 2 = (z+z::rat)"
by (subst mult_commute, rule rat_mult_2)


subsection{*Comparisons On Numerals*}

lemma eq_rat_number_of [simp]:
     "((number_of v :: rat) = number_of v') =  
      iszero (number_of (bin_add v (bin_minus v')) :: int)"
by (simp add: rat_number_of_def)

text{*@{term neg} is used in rewrite rules for binary comparisons*}
lemma less_rat_number_of [simp]:
     "((number_of v :: rat) < number_of v') =  
      neg (number_of (bin_add v (bin_minus v')) :: int)"
by (simp add: rat_number_of_def)


text{*New versions of existing theorems involving 0, 1*}

lemma rat_minus_1_eq_m1 [simp]: "- 1 = (-1::rat)"
by (simp del: rat_number_of_def add: rat_numeral_1_eq_1 [symmetric])

lemma rat_mult_minus1 [simp]: "-1 * z = -(z::rat)"
proof -
  have  "-1 * z = (- 1) * z" by (simp add: rat_minus_1_eq_m1)
  also have "... = - (1 * z)" by (simp only: minus_mult_left) 
  also have "... = -z" by simp
  finally show ?thesis .
qed

lemma rat_mult_minus1_right [simp]: "z * -1 = -(z::rat)"
by (subst mult_commute, rule rat_mult_minus1)


subsection{*Simplification of Arithmetic when Nested to the Right*}

lemma rat_add_number_of_left [simp]:
     "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::rat)"
by (simp add: add_assoc [symmetric])

lemma rat_mult_number_of_left [simp]:
     "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::rat)"
apply (simp add: mult_assoc [symmetric])
done

lemma rat_add_number_of_diff1 [simp]: 
     "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::rat)"
apply (unfold diff_rat_def)
apply (rule rat_add_number_of_left)
done

lemma rat_add_number_of_diff2 [simp]:
     "number_of v + (c - number_of w) =  
      number_of (bin_add v (bin_minus w)) + (c::rat)"
apply (subst diff_rat_number_of [symmetric])
apply (simp only: diff_rat_def add_ac)
done


declare rat_numeral_0_eq_0 [simp] rat_numeral_1_eq_1 [simp]

lemmas rat_add_0_left = add_0 [where ?'a = rat]
lemmas rat_add_0_right = add_0_right [where ?'a = rat]
lemmas rat_mult_1_left = mult_1 [where ?'a = rat]
lemmas rat_mult_1_right = mult_1_right [where ?'a = rat]


declare diff_rat_def [symmetric]


use "rat_arith.ML"

setup rat_arith_setup


subsubsection{*Division By @{term "-1"}*}

lemma rat_divide_minus1 [simp]: "x/-1 = -(x::rat)" 
by simp

lemma rat_minus1_divide [simp]: "-1/(x::rat) = - (1/x)"
by (simp add: divide_rat_def inverse_minus_eq)

subsection{*Absolute Value Function for the Rats*}

lemma abs_nat_number_of [simp]: 
     "abs (number_of v :: rat) =  
        (if neg (number_of v :: int)  then number_of (bin_minus v)  
         else number_of v)"
by (simp add: abs_if) 

lemma abs_minus_one [simp]: "abs (-1) = (1::rat)"
by (simp add: abs_if)

declare rat_number_of_def [simp]


ML
{*
val rat_divide_minus1 = thm "rat_divide_minus1";
val rat_minus1_divide = thm "rat_minus1_divide";
val abs_nat_number_of = thm "abs_nat_number_of";
val abs_minus_one = thm "abs_minus_one";
*}

end
