(*  Title:      HOL/HyperArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header{*Binary arithmetic and Simplification for the Hyperreals*}

theory HyperArith = HyperDef
files ("hypreal_arith.ML"):

subsection{*Binary Arithmetic for the Hyperreals*}

instance hypreal :: number ..

defs (overloaded)
  hypreal_number_of_def:
    "number_of v == hypreal_of_real (number_of v)"
     (*::bin=>hypreal               ::bin=>real*)
     --{*This case is reduced to that for the reals.*}



subsubsection{*Embedding the Reals into the Hyperreals*}

lemma hypreal_number_of [simp]: "hypreal_of_real (number_of w) = number_of w"
by (simp add: hypreal_number_of_def)

lemma hypreal_numeral_0_eq_0: "Numeral0 = (0::hypreal)"
by (simp add: hypreal_number_of_def)

lemma hypreal_numeral_1_eq_1: "Numeral1 = (1::hypreal)"
by (simp add: hypreal_number_of_def)

subsubsection{*Addition*}

lemma add_hypreal_number_of [simp]:
     "(number_of v :: hypreal) + number_of v' = number_of (bin_add v v')"
by (simp only: hypreal_number_of_def hypreal_of_real_add [symmetric]
               add_real_number_of)


subsubsection{*Subtraction*}

lemma minus_hypreal_number_of [simp]:
     "- (number_of w :: hypreal) = number_of (bin_minus w)"
by (simp only: hypreal_number_of_def minus_real_number_of
               hypreal_of_real_minus [symmetric])

lemma diff_hypreal_number_of [simp]:
     "(number_of v :: hypreal) - number_of w =
      number_of (bin_add v (bin_minus w))"
by (unfold hypreal_number_of_def hypreal_diff_def, simp)


subsubsection{*Multiplication*}

lemma mult_hypreal_number_of [simp]:
     "(number_of v :: hypreal) * number_of v' = number_of (bin_mult v v')"
by (simp only: hypreal_number_of_def hypreal_of_real_mult [symmetric] mult_real_number_of)

text{*Lemmas for specialist use, NOT as default simprules*}
lemma hypreal_mult_2: "2 * z = (z+z::hypreal)"
proof -
  have eq: "(2::hypreal) = 1 + 1"
    by (simp add: hypreal_numeral_1_eq_1 [symmetric])
  thus ?thesis by (simp add: eq left_distrib)
qed

lemma hypreal_mult_2_right: "z * 2 = (z+z::hypreal)"
by (subst hypreal_mult_commute, rule hypreal_mult_2)


subsubsection{*Comparisons*}

(** Equals (=) **)

lemma eq_hypreal_number_of [simp]:
     "((number_of v :: hypreal) = number_of v') =
      iszero (number_of (bin_add v (bin_minus v')) :: int)"
apply (simp only: hypreal_number_of_def hypreal_of_real_eq_iff eq_real_number_of)
done


(** Less-than (<) **)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma less_hypreal_number_of [simp]:
     "((number_of v :: hypreal) < number_of v') =
      neg (number_of (bin_add v (bin_minus v')) :: int)"
by (simp only: hypreal_number_of_def hypreal_of_real_less_iff less_real_number_of)



text{*New versions of existing theorems involving 0, 1*}

lemma hypreal_minus_1_eq_m1 [simp]: "- 1 = (-1::hypreal)"
by (simp add: hypreal_numeral_1_eq_1 [symmetric])

lemma hypreal_mult_minus1 [simp]: "-1 * z = -(z::hypreal)"
proof -
  have  "-1 * z = (- 1) * z" by (simp add: hypreal_minus_1_eq_m1)
  also have "... = - (1 * z)" by (simp only: minus_mult_left)
  also have "... = -z" by simp
  finally show ?thesis .
qed

lemma hypreal_mult_minus1_right [simp]: "(z::hypreal) * -1 = -z"
by (subst hypreal_mult_commute, rule hypreal_mult_minus1)


subsection{*Simplification of Arithmetic when Nested to the Right*}

lemma hypreal_add_number_of_left [simp]:
     "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::hypreal)"
by (simp add: add_assoc [symmetric])

lemma hypreal_mult_number_of_left [simp]:
     "number_of v *(number_of w * z) = (number_of(bin_mult v w) * z::hypreal)"
by (simp add: hypreal_mult_assoc [symmetric])

lemma hypreal_add_number_of_diff1:
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::hypreal)"
by (simp add: hypreal_diff_def hypreal_add_number_of_left)

lemma hypreal_add_number_of_diff2 [simp]:
     "number_of v + (c - number_of w) =
      number_of (bin_add v (bin_minus w)) + (c::hypreal)"
apply (subst diff_hypreal_number_of [symmetric])
apply (simp only: hypreal_diff_def add_ac)
done


declare hypreal_numeral_0_eq_0 [simp] hypreal_numeral_1_eq_1 [simp]



use "hypreal_arith.ML"

setup hypreal_arith_setup

lemma hypreal_le_add_order: "[| 0 \<le> x; 0 \<le> y |] ==> (0::hypreal) \<le> x + y"
by arith


subsubsection{*Division By @{term 1} and @{term "-1"}*}

lemma hypreal_divide_minus1 [simp]: "x/-1 = -(x::hypreal)"
by simp

lemma hypreal_minus1_divide [simp]: "-1/(x::hypreal) = - (1/x)"
by (simp add: hypreal_divide_def hypreal_minus_inverse)


subsection{*The Function @{term hypreal_of_real}*}

lemma number_of_less_hypreal_of_real_iff [simp]:
     "(number_of w < hypreal_of_real z) = (number_of w < z)"
apply (subst hypreal_of_real_less_iff [symmetric])
apply (simp (no_asm))
done

lemma number_of_le_hypreal_of_real_iff [simp]:
     "(number_of w <= hypreal_of_real z) = (number_of w <= z)"
apply (subst hypreal_of_real_le_iff [symmetric])
apply (simp (no_asm))
done

lemma hypreal_of_real_eq_number_of_iff [simp]:
     "(hypreal_of_real z = number_of w) = (z = number_of w)"
apply (subst hypreal_of_real_eq_iff [symmetric])
apply (simp (no_asm))
done

lemma hypreal_of_real_less_number_of_iff [simp]:
     "(hypreal_of_real z < number_of w) = (z < number_of w)"
apply (subst hypreal_of_real_less_iff [symmetric])
apply (simp (no_asm))
done

lemma hypreal_of_real_le_number_of_iff [simp]:
     "(hypreal_of_real z <= number_of w) = (z <= number_of w)"
apply (subst hypreal_of_real_le_iff [symmetric])
apply (simp (no_asm))
done

subsection{*Absolute Value Function for the Hyperreals*}

lemma hrabs_number_of [simp]:
     "abs (number_of v :: hypreal) =
        (if neg (number_of v :: int) then number_of (bin_minus v)
         else number_of v)"
by (simp add: hrabs_def)


declare abs_mult [simp]

lemma hrabs_add_less: "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)"
apply (unfold hrabs_def)
apply (simp split add: split_if_asm)
done

lemma hrabs_less_gt_zero: "abs x < r ==> (0::hypreal) < r"
by (blast intro!: order_le_less_trans abs_ge_zero)

lemma hrabs_disj: "abs x = (x::hypreal) | abs x = -x"
by (simp add: hrabs_def)

(* Needed in Geom.ML *)
lemma hrabs_add_lemma_disj: "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y"
by (simp add: hrabs_def split add: split_if_asm)


(*----------------------------------------------------------
    Relating hrabs to abs through embedding of IR into IR*
 ----------------------------------------------------------*)
lemma hypreal_of_real_hrabs:
    "abs (hypreal_of_real r) = hypreal_of_real (abs r)"
apply (unfold hypreal_of_real_def)
apply (auto simp add: hypreal_hrabs)
done


subsection{*Embedding the Naturals into the Hyperreals*}

constdefs

  hypreal_of_nat   :: "nat => hypreal"
   "hypreal_of_nat m  == of_nat m"

lemma SNat_eq: "Nats = {n. \<exists>N. n = hypreal_of_nat N}"
by (force simp add: hypreal_of_nat_def Nats_def) 


lemma hypreal_of_nat_add [simp]:
     "hypreal_of_nat (m + n) = hypreal_of_nat m + hypreal_of_nat n"
by (simp add: hypreal_of_nat_def)

lemma hypreal_of_nat_mult: "hypreal_of_nat (m * n) = hypreal_of_nat m * hypreal_of_nat n"
by (simp add: hypreal_of_nat_def)
declare hypreal_of_nat_mult [simp]

lemma hypreal_of_nat_less_iff:
      "(n < m) = (hypreal_of_nat n < hypreal_of_nat m)"
apply (simp add: hypreal_of_nat_def)
done
declare hypreal_of_nat_less_iff [symmetric, simp]

(*------------------------------------------------------------*)
(* naturals embedded in hyperreals                            *)
(* is a hyperreal c.f. NS extension                           *)
(*------------------------------------------------------------*)

lemma hypreal_of_nat_eq:
     "hypreal_of_nat (n::nat) = hypreal_of_real (real n)"
apply (induct n) 
apply (simp_all add: hypreal_of_nat_def real_of_nat_def)
done

lemma hypreal_of_nat:
     "hypreal_of_nat m = Abs_hypreal(hyprel``{%n. real m})"
apply (induct m) 
apply (simp_all add: hypreal_of_nat_def real_of_nat_def hypreal_zero_def 
                     hypreal_one_def hypreal_add)
done

lemma hypreal_of_nat_Suc:
     "hypreal_of_nat (Suc n) = hypreal_of_nat n + (1::hypreal)"
by (simp add: hypreal_of_nat_def)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma hypreal_of_nat_number_of [simp]:
     "hypreal_of_nat (number_of v :: nat) =
         (if neg (number_of v :: int) then 0
          else (number_of v :: hypreal))"
by (simp add: hypreal_of_nat_eq)

lemma hypreal_of_nat_zero [simp]: "hypreal_of_nat 0 = 0"
by (simp add: hypreal_of_nat_def) 

lemma hypreal_of_nat_one [simp]: "hypreal_of_nat 1 = 1"
by (simp add: hypreal_of_nat_def) 

lemma hypreal_of_nat_le_iff [simp]:
     "(hypreal_of_nat n \<le> hypreal_of_nat m) = (n \<le> m)"
by (simp add: hypreal_of_nat_def) 

lemma hypreal_of_nat_ge_zero [simp]: "0 \<le> hypreal_of_nat n"
by (simp add: hypreal_of_nat_def) 


(*
FIXME: we should declare this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric hypreal_diff_def]
*)

ML
{*
val hypreal_le_add_order = thm"hypreal_le_add_order";

val hypreal_of_nat_def = thm"hypreal_of_nat_def";

val hrabs_number_of = thm "hrabs_number_of";
val hrabs_add_less = thm "hrabs_add_less";
val hrabs_less_gt_zero = thm "hrabs_less_gt_zero";
val hrabs_disj = thm "hrabs_disj";
val hrabs_add_lemma_disj = thm "hrabs_add_lemma_disj";
val hypreal_of_real_hrabs = thm "hypreal_of_real_hrabs";
val hypreal_of_nat_add = thm "hypreal_of_nat_add";
val hypreal_of_nat_mult = thm "hypreal_of_nat_mult";
val hypreal_of_nat_less_iff = thm "hypreal_of_nat_less_iff";
val hypreal_of_nat_Suc = thm "hypreal_of_nat_Suc";
val hypreal_of_nat_number_of = thm "hypreal_of_nat_number_of";
val hypreal_of_nat_zero = thm "hypreal_of_nat_zero";
val hypreal_of_nat_one = thm "hypreal_of_nat_one";
val hypreal_of_nat_le_iff = thm"hypreal_of_nat_le_iff";
val hypreal_of_nat_ge_zero = thm"hypreal_of_nat_ge_zero";
val hypreal_of_nat = thm"hypreal_of_nat";
*}

end
