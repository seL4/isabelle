(*  Title       : HRealAbs.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the hyperreals
*) 

theory HRealAbs = HyperArith:

constdefs

  hypreal_of_nat :: "nat => hypreal"
  "hypreal_of_nat (n::nat) == hypreal_of_real (real n)"


lemma hrabs_number_of [simp]:
     "abs (number_of v :: hypreal) =
        (if neg (number_of v) then number_of (bin_minus v)
         else number_of v)"
by (simp add: hrabs_def)


(*------------------------------------------------------------
   Properties of the absolute value function over the reals
   (adapted version of previously proved theorems about abs)
 ------------------------------------------------------------*)

lemma hrabs_eqI1: "(0::hypreal)<=x ==> abs x = x"
by (simp add: hrabs_def)

lemma hrabs_eqI2: "(0::hypreal)<x ==> abs x = x"
by (simp add: order_less_imp_le hrabs_eqI1)

lemma hrabs_minus_eqI2: "x<(0::hypreal) ==> abs x = -x"
by (simp add: linorder_not_less [symmetric] hrabs_def)

lemma hrabs_minus_eqI1: "x<=(0::hypreal) ==> abs x = -x"
by (auto dest: order_antisym simp add: hrabs_def)

declare abs_mult [simp]

lemma hrabs_add_less: "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)"
apply (unfold hrabs_def)
apply (simp split add: split_if_asm)
done

lemma hrabs_less_gt_zero: "abs x < r ==> (0::hypreal) < r"
by (blast intro!: order_le_less_trans abs_ge_zero)

lemma hrabs_disj: "abs x = (x::hypreal) | abs x = -x"
by (simp add: hrabs_def)

lemma hrabs_eq_disj: "abs x = (y::hypreal) ==> x = y | -x = y"
by (simp add: hrabs_def split add: split_if_asm)

(* Needed in Geom.ML *)
lemma hrabs_add_lemma_disj: "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y"
by (simp add: hrabs_def split add: split_if_asm)

(* Needed in Geom.ML?? *)
lemma hrabs_add_lemma_disj2: "(x::hypreal) + - y + (z + - y) = abs (x + - z) ==> y = z | x = y"
by (simp add: hrabs_def split add: split_if_asm)


(*----------------------------------------------------------
    Relating hrabs to abs through embedding of IR into IR*
 ----------------------------------------------------------*)
lemma hypreal_of_real_hrabs:
    "abs (hypreal_of_real r) = hypreal_of_real (abs r)"
apply (unfold hypreal_of_real_def)
apply (auto simp add: hypreal_hrabs)
done


(*----------------------------------------------------------------------------
             Embedding of the naturals in the hyperreals
 ----------------------------------------------------------------------------*)

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

lemma hypreal_of_nat_iff:
     "hypreal_of_nat  m = Abs_hypreal(hyprel``{%n. real m})"
by (simp add: hypreal_of_nat_def hypreal_of_real_def real_of_nat_def)

lemma inj_hypreal_of_nat: "inj hypreal_of_nat"
by (simp add: inj_on_def hypreal_of_nat_def)

lemma hypreal_of_nat_Suc:
     "hypreal_of_nat (Suc n) = hypreal_of_nat n + (1::hypreal)"
by (simp add: hypreal_of_nat_def real_of_nat_Suc)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma hypreal_of_nat_number_of [simp]:
     "hypreal_of_nat (number_of v :: nat) =
         (if neg (number_of v) then 0
          else (number_of v :: hypreal))"
by (simp add: hypreal_of_nat_def)

lemma hypreal_of_nat_zero [simp]: "hypreal_of_nat 0 = 0"
by (simp del: numeral_0_eq_0 add: numeral_0_eq_0 [symmetric])

lemma hypreal_of_nat_one [simp]: "hypreal_of_nat 1 = 1"
by (simp add: hypreal_of_nat_Suc)


ML
{*
val hypreal_of_nat_def = thm"hypreal_of_nat_def";

val hrabs_number_of = thm "hrabs_number_of";
val hrabs_eqI1 = thm "hrabs_eqI1";
val hrabs_eqI2 = thm "hrabs_eqI2";
val hrabs_minus_eqI2 = thm "hrabs_minus_eqI2";
val hrabs_minus_eqI1 = thm "hrabs_minus_eqI1";
val hrabs_add_less = thm "hrabs_add_less";
val hrabs_less_gt_zero = thm "hrabs_less_gt_zero";
val hrabs_disj = thm "hrabs_disj";
val hrabs_eq_disj = thm "hrabs_eq_disj";
val hrabs_add_lemma_disj = thm "hrabs_add_lemma_disj";
val hrabs_add_lemma_disj2 = thm "hrabs_add_lemma_disj2";
val hypreal_of_real_hrabs = thm "hypreal_of_real_hrabs";
val hypreal_of_nat_add = thm "hypreal_of_nat_add";
val hypreal_of_nat_mult = thm "hypreal_of_nat_mult";
val hypreal_of_nat_less_iff = thm "hypreal_of_nat_less_iff";
val hypreal_of_nat_iff = thm "hypreal_of_nat_iff";
val inj_hypreal_of_nat = thm "inj_hypreal_of_nat";
val hypreal_of_nat_Suc = thm "hypreal_of_nat_Suc";
val hypreal_of_nat_number_of = thm "hypreal_of_nat_number_of";
val hypreal_of_nat_zero = thm "hypreal_of_nat_zero";
val hypreal_of_nat_one = thm "hypreal_of_nat_one";
*}

end
