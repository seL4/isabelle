(*  Title:      HOL/HyperArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header{*Binary arithmetic and Simplification for the Hyperreals*}

theory HyperArith = HyperDef
files ("hypreal_arith.ML"):


subsection{*Numerals and Arithmetic*}

instance hypreal :: number ..

primrec (*the type constraint is essential!*)
  number_of_Pls: "number_of bin.Pls = 0"
  number_of_Min: "number_of bin.Min = - (1::hypreal)"
  number_of_BIT: "number_of(w BIT x) = (if x then 1 else 0) +
	                               (number_of w) + (number_of w)"

declare number_of_Pls [simp del]
        number_of_Min [simp del]
        number_of_BIT [simp del]

instance hypreal :: number_ring
proof
  show "Numeral0 = (0::hypreal)" by (rule number_of_Pls)
  show "-1 = - (1::hypreal)" by (rule number_of_Min)
  fix w :: bin and x :: bool
  show "(number_of (w BIT x) :: hypreal) =
        (if x then 1 else 0) + number_of w + number_of w"
    by (rule number_of_BIT)
qed


text{*Collapse applications of @{term hypreal_of_real} to @{term number_of}*}
lemma hypreal_number_of [simp]: "hypreal_of_real (number_of w) = number_of w"
apply (induct w) 
apply (simp_all only: number_of hypreal_of_real_add hypreal_of_real_minus, simp_all) 
done


use "hypreal_arith.ML"

setup hypreal_arith_setup

lemma hypreal_le_add_order: "[| 0 \<le> x; 0 \<le> y |] ==> (0::hypreal) \<le> x + y"
by arith


subsection{*The Function @{term hypreal_of_real}*}

lemma number_of_less_hypreal_of_real_iff [simp]:
     "(number_of w < hypreal_of_real z) = (number_of w < z)"
apply (subst hypreal_of_real_less_iff [symmetric])
apply (simp (no_asm))
done

lemma number_of_le_hypreal_of_real_iff [simp]:
     "(number_of w \<le> hypreal_of_real z) = (number_of w \<le> z)"
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
     "(hypreal_of_real z \<le> number_of w) = (z \<le> number_of w)"
apply (subst hypreal_of_real_le_iff [symmetric])
apply (simp (no_asm))
done

subsection{*Absolute Value Function for the Hyperreals*}

declare abs_mult [simp]

lemma hrabs_add_less: "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)"
apply (unfold hrabs_def)
apply (simp split add: split_if_asm)
done

text{*used once in NSA*}
lemma hrabs_less_gt_zero: "abs x < r ==> (0::hypreal) < r"
by (blast intro!: order_le_less_trans abs_ge_zero)

lemma hrabs_disj: "abs x = (x::hypreal) | abs x = -x"
by (simp add: hrabs_def)

(* Needed in Geom.ML *)
lemma hrabs_add_lemma_disj: "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y"
by (simp add: hrabs_def split add: split_if_asm)

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

val hrabs_add_less = thm "hrabs_add_less";
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
