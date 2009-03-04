(*  Title:      HOL/NatBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary arithmetic for the natural numbers *}

theory NatBin
imports IntDiv
begin

text {*
  Arithmetic for naturals is reduced to that for the non-negative integers.
*}

instantiation nat :: number
begin

definition
  nat_number_of_def [code inline, code del]: "number_of v = nat (number_of v)"

instance ..

end

lemma [code post]:
  "nat (number_of v) = number_of v"
  unfolding nat_number_of_def ..

abbreviation (xsymbols)
  power2 :: "'a::power => 'a"  ("(_\<twosuperior>)" [1000] 999) where
  "x\<twosuperior> == x^2"

notation (latex output)
  power2  ("(_\<twosuperior>)" [1000] 999)

notation (HTML output)
  power2  ("(_\<twosuperior>)" [1000] 999)


subsection {* Predicate for negative binary numbers *}

definition
  neg  :: "int \<Rightarrow> bool"
where
  "neg Z \<longleftrightarrow> Z < 0"

lemma not_neg_int [simp]: "~ neg (of_nat n)"
by (simp add: neg_def)

lemma neg_zminus_int [simp]: "neg (- (of_nat (Suc n)))"
by (simp add: neg_def neg_less_0_iff_less del: of_nat_Suc)

lemmas neg_eq_less_0 = neg_def

lemma not_neg_eq_ge_0: "(~neg x) = (0 \<le> x)"
by (simp add: neg_def linorder_not_less)

text{*To simplify inequalities when Numeral1 can get simplified to 1*}

lemma not_neg_0: "~ neg 0"
by (simp add: One_int_def neg_def)

lemma not_neg_1: "~ neg 1"
by (simp add: neg_def linorder_not_less zero_le_one)

lemma neg_nat: "neg z ==> nat z = 0"
by (simp add: neg_def order_less_imp_le) 

lemma not_neg_nat: "~ neg z ==> of_nat (nat z) = z"
by (simp add: linorder_not_less neg_def)

text {*
  If @{term Numeral0} is rewritten to 0 then this rule can't be applied:
  @{term Numeral0} IS @{term "number_of Pls"}
*}

lemma not_neg_number_of_Pls: "~ neg (number_of Int.Pls)"
  by (simp add: neg_def)

lemma neg_number_of_Min: "neg (number_of Int.Min)"
  by (simp add: neg_def)

lemma neg_number_of_Bit0:
  "neg (number_of (Int.Bit0 w)) = neg (number_of w)"
  by (simp add: neg_def)

lemma neg_number_of_Bit1:
  "neg (number_of (Int.Bit1 w)) = neg (number_of w)"
  by (simp add: neg_def)

lemmas neg_simps [simp] =
  not_neg_0 not_neg_1
  not_neg_number_of_Pls neg_number_of_Min
  neg_number_of_Bit0 neg_number_of_Bit1


subsection{*Function @{term nat}: Coercion from Type @{typ int} to @{typ nat}*}

declare nat_0 [simp] nat_1 [simp]

lemma nat_number_of [simp]: "nat (number_of w) = number_of w"
by (simp add: nat_number_of_def)

lemma nat_numeral_0_eq_0 [simp]: "Numeral0 = (0::nat)"
by (simp add: nat_number_of_def)

lemma nat_numeral_1_eq_1 [simp]: "Numeral1 = (1::nat)"
by (simp add: nat_1 nat_number_of_def)

lemma numeral_1_eq_Suc_0: "Numeral1 = Suc 0"
by (simp add: nat_numeral_1_eq_1)

lemma numeral_2_eq_2: "2 = Suc (Suc 0)"
apply (unfold nat_number_of_def)
apply (rule nat_2)
done


subsection{*Function @{term int}: Coercion from Type @{typ nat} to @{typ int}*}

lemma int_nat_number_of [simp]:
     "int (number_of v) =  
         (if neg (number_of v :: int) then 0  
          else (number_of v :: int))"
  unfolding nat_number_of_def number_of_is_id neg_def
  by simp


subsubsection{*Successor *}

lemma Suc_nat_eq_nat_zadd1: "(0::int) <= z ==> Suc (nat z) = nat (1 + z)"
apply (rule sym)
apply (simp add: nat_eq_iff int_Suc)
done

lemma Suc_nat_number_of_add:
     "Suc (number_of v + n) =  
        (if neg (number_of v :: int) then 1+n else number_of (Int.succ v) + n)"
  unfolding nat_number_of_def number_of_is_id neg_def numeral_simps
  by (simp add: Suc_nat_eq_nat_zadd1 add_ac)

lemma Suc_nat_number_of [simp]:
     "Suc (number_of v) =  
        (if neg (number_of v :: int) then 1 else number_of (Int.succ v))"
apply (cut_tac n = 0 in Suc_nat_number_of_add)
apply (simp cong del: if_weak_cong)
done


subsubsection{*Addition *}

lemma add_nat_number_of [simp]:
     "(number_of v :: nat) + number_of v' =  
         (if v < Int.Pls then number_of v'  
          else if v' < Int.Pls then number_of v  
          else number_of (v + v'))"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by (simp add: nat_add_distrib)

lemma nat_number_of_add_1 [simp]:
  "number_of v + (1::nat) =
    (if v < Int.Pls then 1 else number_of (Int.succ v))"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by (simp add: nat_add_distrib)

lemma nat_1_add_number_of [simp]:
  "(1::nat) + number_of v =
    (if v < Int.Pls then 1 else number_of (Int.succ v))"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by (simp add: nat_add_distrib)

lemma nat_1_add_1 [simp]: "1 + 1 = (2::nat)"
  by (rule int_int_eq [THEN iffD1]) simp


subsubsection{*Subtraction *}

lemma diff_nat_eq_if:
     "nat z - nat z' =  
        (if neg z' then nat z   
         else let d = z-z' in     
              if neg d then 0 else nat d)"
by (simp add: Let_def nat_diff_distrib [symmetric] neg_eq_less_0 not_neg_eq_ge_0)


lemma diff_nat_number_of [simp]: 
     "(number_of v :: nat) - number_of v' =  
        (if v' < Int.Pls then number_of v  
         else let d = number_of (v + uminus v') in     
              if neg d then 0 else nat d)"
  unfolding nat_number_of_def number_of_is_id numeral_simps neg_def
  by auto

lemma nat_number_of_diff_1 [simp]:
  "number_of v - (1::nat) =
    (if v \<le> Int.Pls then 0 else number_of (Int.pred v))"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by auto


subsubsection{*Multiplication *}

lemma mult_nat_number_of [simp]:
     "(number_of v :: nat) * number_of v' =  
       (if v < Int.Pls then 0 else number_of (v * v'))"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by (simp add: nat_mult_distrib)


subsubsection{*Quotient *}

lemma div_nat_number_of [simp]:
     "(number_of v :: nat)  div  number_of v' =  
          (if neg (number_of v :: int) then 0  
           else nat (number_of v div number_of v'))"
  unfolding nat_number_of_def number_of_is_id neg_def
  by (simp add: nat_div_distrib)

lemma one_div_nat_number_of [simp]:
     "Suc 0 div number_of v' = nat (1 div number_of v')" 
by (simp del: nat_numeral_1_eq_1 add: numeral_1_eq_Suc_0 [symmetric]) 


subsubsection{*Remainder *}

lemma mod_nat_number_of [simp]:
     "(number_of v :: nat)  mod  number_of v' =  
        (if neg (number_of v :: int) then 0  
         else if neg (number_of v' :: int) then number_of v  
         else nat (number_of v mod number_of v'))"
  unfolding nat_number_of_def number_of_is_id neg_def
  by (simp add: nat_mod_distrib)

lemma one_mod_nat_number_of [simp]:
     "Suc 0 mod number_of v' =  
        (if neg (number_of v' :: int) then Suc 0
         else nat (1 mod number_of v'))"
by (simp del: nat_numeral_1_eq_1 add: numeral_1_eq_Suc_0 [symmetric]) 


subsubsection{* Divisibility *}

lemmas dvd_eq_mod_eq_0_number_of =
  dvd_eq_mod_eq_0 [of "number_of x" "number_of y", standard]

declare dvd_eq_mod_eq_0_number_of [simp]

ML
{*
val nat_number_of_def = thm"nat_number_of_def";

val nat_number_of = thm"nat_number_of";
val nat_numeral_0_eq_0 = thm"nat_numeral_0_eq_0";
val nat_numeral_1_eq_1 = thm"nat_numeral_1_eq_1";
val numeral_1_eq_Suc_0 = thm"numeral_1_eq_Suc_0";
val numeral_2_eq_2 = thm"numeral_2_eq_2";
val nat_div_distrib = thm"nat_div_distrib";
val nat_mod_distrib = thm"nat_mod_distrib";
val int_nat_number_of = thm"int_nat_number_of";
val Suc_nat_eq_nat_zadd1 = thm"Suc_nat_eq_nat_zadd1";
val Suc_nat_number_of_add = thm"Suc_nat_number_of_add";
val Suc_nat_number_of = thm"Suc_nat_number_of";
val add_nat_number_of = thm"add_nat_number_of";
val diff_nat_eq_if = thm"diff_nat_eq_if";
val diff_nat_number_of = thm"diff_nat_number_of";
val mult_nat_number_of = thm"mult_nat_number_of";
val div_nat_number_of = thm"div_nat_number_of";
val mod_nat_number_of = thm"mod_nat_number_of";
*}


subsection{*Comparisons*}

subsubsection{*Equals (=) *}

lemma eq_nat_nat_iff:
     "[| (0::int) <= z;  0 <= z' |] ==> (nat z = nat z') = (z=z')"
by (auto elim!: nonneg_eq_int)

lemma eq_nat_number_of [simp]:
     "((number_of v :: nat) = number_of v') =  
      (if neg (number_of v :: int) then (number_of v' :: int) \<le> 0
       else if neg (number_of v' :: int) then (number_of v :: int) = 0
       else v = v')"
  unfolding nat_number_of_def number_of_is_id neg_def
  by auto


subsubsection{*Less-than (<) *}

lemma less_nat_number_of [simp]:
  "(number_of v :: nat) < number_of v' \<longleftrightarrow>
    (if v < v' then Int.Pls < v' else False)"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by auto


subsubsection{*Less-than-or-equal *}

lemma le_nat_number_of [simp]:
  "(number_of v :: nat) \<le> number_of v' \<longleftrightarrow>
    (if v \<le> v' then True else v \<le> Int.Pls)"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by auto

(*Maps #n to n for n = 0, 1, 2*)
lemmas numerals = nat_numeral_0_eq_0 nat_numeral_1_eq_1 numeral_2_eq_2


subsection{*Powers with Numeric Exponents*}

text{*We cannot refer to the number @{term 2} in @{text Ring_and_Field.thy}.
We cannot prove general results about the numeral @{term "-1"}, so we have to
use @{term "- 1"} instead.*}

lemma power2_eq_square: "(a::'a::recpower)\<twosuperior> = a * a"
  by (simp add: numeral_2_eq_2 Power.power_Suc)

lemma zero_power2 [simp]: "(0::'a::{semiring_1,recpower})\<twosuperior> = 0"
  by (simp add: power2_eq_square)

lemma one_power2 [simp]: "(1::'a::{semiring_1,recpower})\<twosuperior> = 1"
  by (simp add: power2_eq_square)

lemma power3_eq_cube: "(x::'a::recpower) ^ 3 = x * x * x"
  apply (subgoal_tac "3 = Suc (Suc (Suc 0))")
  apply (erule ssubst)
  apply (simp add: power_Suc mult_ac)
  apply (unfold nat_number_of_def)
  apply (subst nat_eq_iff)
  apply simp
done

text{*Squares of literal numerals will be evaluated.*}
lemmas power2_eq_square_number_of =
    power2_eq_square [of "number_of w", standard]
declare power2_eq_square_number_of [simp]


lemma zero_le_power2[simp]: "0 \<le> (a\<twosuperior>::'a::{ordered_idom,recpower})"
  by (simp add: power2_eq_square)

lemma zero_less_power2[simp]:
     "(0 < a\<twosuperior>) = (a \<noteq> (0::'a::{ordered_idom,recpower}))"
  by (force simp add: power2_eq_square zero_less_mult_iff linorder_neq_iff)

lemma power2_less_0[simp]:
  fixes a :: "'a::{ordered_idom,recpower}"
  shows "~ (a\<twosuperior> < 0)"
by (force simp add: power2_eq_square mult_less_0_iff) 

lemma zero_eq_power2[simp]:
     "(a\<twosuperior> = 0) = (a = (0::'a::{ordered_idom,recpower}))"
  by (force simp add: power2_eq_square mult_eq_0_iff)

lemma abs_power2[simp]:
     "abs(a\<twosuperior>) = (a\<twosuperior>::'a::{ordered_idom,recpower})"
  by (simp add: power2_eq_square abs_mult abs_mult_self)

lemma power2_abs[simp]:
     "(abs a)\<twosuperior> = (a\<twosuperior>::'a::{ordered_idom,recpower})"
  by (simp add: power2_eq_square abs_mult_self)

lemma power2_minus[simp]:
     "(- a)\<twosuperior> = (a\<twosuperior>::'a::{comm_ring_1,recpower})"
  by (simp add: power2_eq_square)

lemma power2_le_imp_le:
  fixes x y :: "'a::{ordered_semidom,recpower}"
  shows "\<lbrakk>x\<twosuperior> \<le> y\<twosuperior>; 0 \<le> y\<rbrakk> \<Longrightarrow> x \<le> y"
unfolding numeral_2_eq_2 by (rule power_le_imp_le_base)

lemma power2_less_imp_less:
  fixes x y :: "'a::{ordered_semidom,recpower}"
  shows "\<lbrakk>x\<twosuperior> < y\<twosuperior>; 0 \<le> y\<rbrakk> \<Longrightarrow> x < y"
by (rule power_less_imp_less_base)

lemma power2_eq_imp_eq:
  fixes x y :: "'a::{ordered_semidom,recpower}"
  shows "\<lbrakk>x\<twosuperior> = y\<twosuperior>; 0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> x = y"
unfolding numeral_2_eq_2 by (erule (2) power_eq_imp_eq_base, simp)

lemma power_minus1_even[simp]: "(- 1) ^ (2*n) = (1::'a::{comm_ring_1,recpower})"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) then show ?case by (simp add: power_Suc power_add)
qed

lemma power_minus1_odd: "(- 1) ^ Suc(2*n) = -(1::'a::{comm_ring_1,recpower})"
  by (simp add: power_Suc) 

lemma power_even_eq: "(a::'a::recpower) ^ (2*n) = (a^n)^2"
by (subst mult_commute) (simp add: power_mult)

lemma power_odd_eq: "(a::int) ^ Suc(2*n) = a * (a^n)^2"
by (simp add: power_even_eq) 

lemma power_minus_even [simp]:
     "(-a) ^ (2*n) = (a::'a::{comm_ring_1,recpower}) ^ (2*n)"
by (simp add: power_minus1_even power_minus [of a]) 

lemma zero_le_even_power'[simp]:
     "0 \<le> (a::'a::{ordered_idom,recpower}) ^ (2*n)"
proof (induct "n")
  case 0
    show ?case by (simp add: zero_le_one)
next
  case (Suc n)
    have "a ^ (2 * Suc n) = (a*a) * a ^ (2*n)" 
      by (simp add: mult_ac power_add power2_eq_square)
    thus ?case
      by (simp add: prems zero_le_mult_iff)
qed

lemma odd_power_less_zero:
     "(a::'a::{ordered_idom,recpower}) < 0 ==> a ^ Suc(2*n) < 0"
proof (induct "n")
  case 0
  then show ?case by (simp add: Power.power_Suc)
next
  case (Suc n)
  have "a ^ Suc (2 * Suc n) = (a*a) * a ^ Suc(2*n)" 
    by (simp add: mult_ac power_add power2_eq_square Power.power_Suc)
  thus ?case
    by (simp add: prems mult_less_0_iff mult_neg_neg)
qed

lemma odd_0_le_power_imp_0_le:
     "0 \<le> a  ^ Suc(2*n) ==> 0 \<le> (a::'a::{ordered_idom,recpower})"
apply (insert odd_power_less_zero [of a n]) 
apply (force simp add: linorder_not_less [symmetric]) 
done

text{*Simprules for comparisons where common factors can be cancelled.*}
lemmas zero_compare_simps =
    add_strict_increasing add_strict_increasing2 add_increasing
    zero_le_mult_iff zero_le_divide_iff 
    zero_less_mult_iff zero_less_divide_iff 
    mult_le_0_iff divide_le_0_iff 
    mult_less_0_iff divide_less_0_iff 
    zero_le_power2 power2_less_0

subsubsection{*Nat *}

lemma Suc_pred': "0 < n ==> n = Suc(n - 1)"
by (simp add: numerals)

(*Expresses a natural number constant as the Suc of another one.
  NOT suitable for rewriting because n recurs in the condition.*)
lemmas expand_Suc = Suc_pred' [of "number_of v", standard]

subsubsection{*Arith *}

lemma Suc_eq_add_numeral_1: "Suc n = n + 1"
by (simp add: numerals)

lemma Suc_eq_add_numeral_1_left: "Suc n = 1 + n"
by (simp add: numerals)

(* These two can be useful when m = number_of... *)

lemma add_eq_if: "(m::nat) + n = (if m=0 then n else Suc ((m - 1) + n))"
  unfolding One_nat_def by (cases m) simp_all

lemma mult_eq_if: "(m::nat) * n = (if m=0 then 0 else n + ((m - 1) * n))"
  unfolding One_nat_def by (cases m) simp_all

lemma power_eq_if: "(p ^ m :: nat) = (if m=0 then 1 else p * (p ^ (m - 1)))"
  unfolding One_nat_def by (cases m) simp_all


subsection{*Comparisons involving (0::nat) *}

text{*Simplification already does @{term "n<0"}, @{term "n\<le>0"} and @{term "0\<le>n"}.*}

lemma eq_number_of_0 [simp]:
  "number_of v = (0::nat) \<longleftrightarrow> v \<le> Int.Pls"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by auto

lemma eq_0_number_of [simp]:
  "(0::nat) = number_of v \<longleftrightarrow> v \<le> Int.Pls"
by (rule trans [OF eq_sym_conv eq_number_of_0])

lemma less_0_number_of [simp]:
   "(0::nat) < number_of v \<longleftrightarrow> Int.Pls < v"
  unfolding nat_number_of_def number_of_is_id numeral_simps
  by simp

lemma neg_imp_number_of_eq_0: "neg (number_of v :: int) ==> number_of v = (0::nat)"
by (simp del: nat_numeral_0_eq_0 add: nat_numeral_0_eq_0 [symmetric])



subsection{*Comparisons involving  @{term Suc} *}

lemma eq_number_of_Suc [simp]:
     "(number_of v = Suc n) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then False else nat pv = n)"
apply (simp only: simp_thms Let_def neg_eq_less_0 linorder_not_less 
                  number_of_pred nat_number_of_def 
            split add: split_if)
apply (rule_tac x = "number_of v" in spec)
apply (auto simp add: nat_eq_iff)
done

lemma Suc_eq_number_of [simp]:
     "(Suc n = number_of v) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then False else nat pv = n)"
by (rule trans [OF eq_sym_conv eq_number_of_Suc])

lemma less_number_of_Suc [simp]:
     "(number_of v < Suc n) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then True else nat pv < n)"
apply (simp only: simp_thms Let_def neg_eq_less_0 linorder_not_less 
                  number_of_pred nat_number_of_def  
            split add: split_if)
apply (rule_tac x = "number_of v" in spec)
apply (auto simp add: nat_less_iff)
done

lemma less_Suc_number_of [simp]:
     "(Suc n < number_of v) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then False else n < nat pv)"
apply (simp only: simp_thms Let_def neg_eq_less_0 linorder_not_less 
                  number_of_pred nat_number_of_def
            split add: split_if)
apply (rule_tac x = "number_of v" in spec)
apply (auto simp add: zless_nat_eq_int_zless)
done

lemma le_number_of_Suc [simp]:
     "(number_of v <= Suc n) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then True else nat pv <= n)"
by (simp add: Let_def less_Suc_number_of linorder_not_less [symmetric])

lemma le_Suc_number_of [simp]:
     "(Suc n <= number_of v) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then False else n <= nat pv)"
by (simp add: Let_def less_number_of_Suc linorder_not_less [symmetric])


lemma eq_number_of_Pls_Min: "(Numeral0 ::int) ~= number_of Int.Min"
by auto



subsection{*Max and Min Combined with @{term Suc} *}

lemma max_number_of_Suc [simp]:
     "max (Suc n) (number_of v) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then Suc n else Suc(max n (nat pv)))"
apply (simp only: Let_def neg_eq_less_0 number_of_pred nat_number_of_def 
            split add: split_if nat.split)
apply (rule_tac x = "number_of v" in spec) 
apply auto
done
 
lemma max_Suc_number_of [simp]:
     "max (number_of v) (Suc n) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then Suc n else Suc(max (nat pv) n))"
apply (simp only: Let_def neg_eq_less_0 number_of_pred nat_number_of_def 
            split add: split_if nat.split)
apply (rule_tac x = "number_of v" in spec) 
apply auto
done
 
lemma min_number_of_Suc [simp]:
     "min (Suc n) (number_of v) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then 0 else Suc(min n (nat pv)))"
apply (simp only: Let_def neg_eq_less_0 number_of_pred nat_number_of_def 
            split add: split_if nat.split)
apply (rule_tac x = "number_of v" in spec) 
apply auto
done
 
lemma min_Suc_number_of [simp]:
     "min (number_of v) (Suc n) =  
        (let pv = number_of (Int.pred v) in  
         if neg pv then 0 else Suc(min (nat pv) n))"
apply (simp only: Let_def neg_eq_less_0 number_of_pred nat_number_of_def 
            split add: split_if nat.split)
apply (rule_tac x = "number_of v" in spec) 
apply auto
done
 
subsection{*Literal arithmetic involving powers*}

lemma nat_power_eq: "(0::int) <= z ==> nat (z^n) = nat z ^ n"
apply (induct "n")
apply (simp_all (no_asm_simp) add: nat_mult_distrib)
done

lemma power_nat_number_of:
     "(number_of v :: nat) ^ n =  
       (if neg (number_of v :: int) then 0^n else nat ((number_of v :: int) ^ n))"
by (simp only: simp_thms neg_nat not_neg_eq_ge_0 nat_number_of_def nat_power_eq
         split add: split_if cong: imp_cong)


lemmas power_nat_number_of_number_of = power_nat_number_of [of _ "number_of w", standard]
declare power_nat_number_of_number_of [simp]



text{*For arbitrary rings*}

lemma power_number_of_even:
  fixes z :: "'a::{number_ring,recpower}"
  shows "z ^ number_of (Int.Bit0 w) = (let w = z ^ (number_of w) in w * w)"
unfolding Let_def nat_number_of_def number_of_Bit0
apply (rule_tac x = "number_of w" in spec, clarify)
apply (case_tac " (0::int) <= x")
apply (auto simp add: nat_mult_distrib power_even_eq power2_eq_square)
done

lemma power_number_of_odd:
  fixes z :: "'a::{number_ring,recpower}"
  shows "z ^ number_of (Int.Bit1 w) = (if (0::int) <= number_of w
     then (let w = z ^ (number_of w) in z * w * w) else 1)"
unfolding Let_def nat_number_of_def number_of_Bit1
apply (rule_tac x = "number_of w" in spec, auto)
apply (simp only: nat_add_distrib nat_mult_distrib)
apply simp
apply (auto simp add: nat_add_distrib nat_mult_distrib power_even_eq power2_eq_square neg_nat power_Suc)
done

lemmas zpower_number_of_even = power_number_of_even [where 'a=int]
lemmas zpower_number_of_odd = power_number_of_odd [where 'a=int]

lemmas power_number_of_even_number_of [simp] =
    power_number_of_even [of "number_of v", standard]

lemmas power_number_of_odd_number_of [simp] =
    power_number_of_odd [of "number_of v", standard]



ML
{*
val numeral_ss = @{simpset} addsimps @{thms numerals};

val nat_bin_arith_setup =
 LinArith.map_data
   (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
     {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms,
      inj_thms = inj_thms,
      lessD = lessD, neqE = neqE,
      simpset = simpset addsimps @{thms neg_simps} @
        [@{thm Suc_nat_number_of}, @{thm int_nat_number_of}]})
*}

declaration {* K nat_bin_arith_setup *}

(* Enable arith to deal with div/mod k where k is a numeral: *)
declare split_div[of _ _ "number_of k", standard, arith_split]
declare split_mod[of _ _ "number_of k", standard, arith_split]

lemma nat_number_of_Pls: "Numeral0 = (0::nat)"
  by (simp add: number_of_Pls nat_number_of_def)

lemma nat_number_of_Min: "number_of Int.Min = (0::nat)"
  apply (simp only: number_of_Min nat_number_of_def nat_zminus_int)
  done

lemma nat_number_of_Bit0:
    "number_of (Int.Bit0 w) = (let n::nat = number_of w in n + n)"
  unfolding nat_number_of_def number_of_is_id numeral_simps Let_def
  by auto

lemma nat_number_of_Bit1:
  "number_of (Int.Bit1 w) =
    (if neg (number_of w :: int) then 0
     else let n = number_of w in Suc (n + n))"
  unfolding nat_number_of_def number_of_is_id numeral_simps neg_def Let_def
  by auto

lemmas nat_number =
  nat_number_of_Pls nat_number_of_Min
  nat_number_of_Bit0 nat_number_of_Bit1

lemma Let_Suc [simp]: "Let (Suc n) f == f (Suc n)"
  by (simp add: Let_def)

lemma power_m1_even: "(-1) ^ (2*n) = (1::'a::{number_ring,recpower})"
by (simp add: power_mult power_Suc); 

lemma power_m1_odd: "(-1) ^ Suc(2*n) = (-1::'a::{number_ring,recpower})"
by (simp add: power_mult power_Suc); 


subsection{*Literal arithmetic and @{term of_nat}*}

lemma of_nat_double:
     "0 \<le> x ==> of_nat (nat (2 * x)) = of_nat (nat x) + of_nat (nat x)"
by (simp only: mult_2 nat_add_distrib of_nat_add) 

lemma nat_numeral_m1_eq_0: "-1 = (0::nat)"
by (simp only: nat_number_of_def)

lemma of_nat_number_of_lemma:
     "of_nat (number_of v :: nat) =  
         (if 0 \<le> (number_of v :: int) 
          then (number_of v :: 'a :: number_ring)
          else 0)"
by (simp add: int_number_of_def nat_number_of_def number_of_eq of_nat_nat);

lemma of_nat_number_of_eq [simp]:
     "of_nat (number_of v :: nat) =  
         (if neg (number_of v :: int) then 0  
          else (number_of v :: 'a :: number_ring))"
by (simp only: of_nat_number_of_lemma neg_def, simp) 


subsection {*Lemmas for the Combination and Cancellation Simprocs*}

lemma nat_number_of_add_left:
     "number_of v + (number_of v' + (k::nat)) =  
         (if neg (number_of v :: int) then number_of v' + k  
          else if neg (number_of v' :: int) then number_of v + k  
          else number_of (v + v') + k)"
  unfolding nat_number_of_def number_of_is_id neg_def
  by auto

lemma nat_number_of_mult_left:
     "number_of v * (number_of v' * (k::nat)) =  
         (if v < Int.Pls then 0
          else number_of (v * v') * k)"
by simp


subsubsection{*For @{text combine_numerals}*}

lemma left_add_mult_distrib: "i*u + (j*u + k) = (i+j)*u + (k::nat)"
by (simp add: add_mult_distrib)


subsubsection{*For @{text cancel_numerals}*}

lemma nat_diff_add_eq1:
     "j <= (i::nat) ==> ((i*u + m) - (j*u + n)) = (((i-j)*u + m) - n)"
by (simp split add: nat_diff_split add: add_mult_distrib)

lemma nat_diff_add_eq2:
     "i <= (j::nat) ==> ((i*u + m) - (j*u + n)) = (m - ((j-i)*u + n))"
by (simp split add: nat_diff_split add: add_mult_distrib)

lemma nat_eq_add_iff1:
     "j <= (i::nat) ==> (i*u + m = j*u + n) = ((i-j)*u + m = n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_eq_add_iff2:
     "i <= (j::nat) ==> (i*u + m = j*u + n) = (m = (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff1:
     "j <= (i::nat) ==> (i*u + m < j*u + n) = ((i-j)*u + m < n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff2:
     "i <= (j::nat) ==> (i*u + m < j*u + n) = (m < (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff1:
     "j <= (i::nat) ==> (i*u + m <= j*u + n) = ((i-j)*u + m <= n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff2:
     "i <= (j::nat) ==> (i*u + m <= j*u + n) = (m <= (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)


subsubsection{*For @{text cancel_numeral_factors} *}

lemma nat_mult_le_cancel1: "(0::nat) < k ==> (k*m <= k*n) = (m<=n)"
by auto

lemma nat_mult_less_cancel1: "(0::nat) < k ==> (k*m < k*n) = (m<n)"
by auto

lemma nat_mult_eq_cancel1: "(0::nat) < k ==> (k*m = k*n) = (m=n)"
by auto

lemma nat_mult_div_cancel1: "(0::nat) < k ==> (k*m) div (k*n) = (m div n)"
by auto

lemma nat_mult_dvd_cancel_disj[simp]:
  "(k*m) dvd (k*n) = (k=0 | m dvd (n::nat))"
by(auto simp: dvd_eq_mod_eq_0 mod_mult_distrib2[symmetric])

lemma nat_mult_dvd_cancel1: "0 < k \<Longrightarrow> (k*m) dvd (k*n::nat) = (m dvd n)"
by(auto)


subsubsection{*For @{text cancel_factor} *}

lemma nat_mult_le_cancel_disj: "(k*m <= k*n) = ((0::nat) < k --> m<=n)"
by auto

lemma nat_mult_less_cancel_disj: "(k*m < k*n) = ((0::nat) < k & m<n)"
by auto

lemma nat_mult_eq_cancel_disj: "(k*m = k*n) = (k = (0::nat) | m=n)"
by auto

lemma nat_mult_div_cancel_disj[simp]:
     "(k*m) div (k*n) = (if k = (0::nat) then 0 else m div n)"
by (simp add: nat_mult_div_cancel1)

end
