(*  Title:      HOL/NatBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary arithmetic for the natural numbers *}

theory NatBin = IntDiv:

text {*
  Arithmetic for naturals is reduced to that for the non-negative integers.
*}

instance nat :: number ..

defs (overloaded)
  nat_number_of_def:
     "(number_of::bin => nat) v == nat ((number_of :: bin => int) v)"


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


text{*Distributive laws for type @{text nat}.  The others are in theory
   @{text IntArith}, but these require div and mod to be defined for type
   "int".  They also need some of the lemmas proved above.*}

lemma nat_div_distrib: "(0::int) <= z ==> nat (z div z') = nat z div nat z'"
apply (case_tac "0 <= z'")
apply (auto simp add: div_nonneg_neg_le0 DIVISION_BY_ZERO_DIV)
apply (case_tac "z' = 0", simp add: DIVISION_BY_ZERO)
apply (auto elim!: nonneg_eq_int)
apply (rename_tac m m')
apply (subgoal_tac "0 <= int m div int m'")
 prefer 2 apply (simp add: nat_numeral_0_eq_0 pos_imp_zdiv_nonneg_iff) 
apply (rule inj_int [THEN injD], simp)
apply (rule_tac r = "int (m mod m') " in quorem_div)
 prefer 2 apply force
apply (simp add: nat_less_iff [symmetric] quorem_def nat_numeral_0_eq_0 zadd_int 
                 zmult_int)
done

(*Fails if z'<0: the LHS collapses to (nat z) but the RHS doesn't*)
lemma nat_mod_distrib:
     "[| (0::int) <= z;  0 <= z' |] ==> nat (z mod z') = nat z mod nat z'"
apply (case_tac "z' = 0", simp add: DIVISION_BY_ZERO)
apply (auto elim!: nonneg_eq_int)
apply (rename_tac m m')
apply (subgoal_tac "0 <= int m mod int m'")
 prefer 2 apply (simp add: nat_less_iff nat_numeral_0_eq_0 pos_mod_sign) 
apply (rule inj_int [THEN injD], simp)
apply (rule_tac q = "int (m div m') " in quorem_mod)
 prefer 2 apply force
apply (simp add: nat_less_iff [symmetric] quorem_def nat_numeral_0_eq_0 zadd_int zmult_int)
done


subsection{*Function @{term int}: Coercion from Type @{typ nat} to @{typ int}*}

(*"neg" is used in rewrite rules for binary comparisons*)
lemma int_nat_number_of [simp]:
     "int (number_of v :: nat) =  
         (if neg (number_of v :: int) then 0  
          else (number_of v :: int))"
by (simp del: nat_number_of
	 add: neg_nat nat_number_of_def not_neg_nat add_assoc)


subsubsection{*Successor *}

lemma Suc_nat_eq_nat_zadd1: "(0::int) <= z ==> Suc (nat z) = nat (1 + z)"
apply (rule sym)
apply (simp add: nat_eq_iff int_Suc)
done

lemma Suc_nat_number_of_add:
     "Suc (number_of v + n) =  
        (if neg (number_of v :: int) then 1+n else number_of (bin_succ v) + n)" 
by (simp del: nat_number_of 
         add: nat_number_of_def neg_nat
              Suc_nat_eq_nat_zadd1 number_of_succ) 

lemma Suc_nat_number_of [simp]:
     "Suc (number_of v) =  
        (if neg (number_of v :: int) then 1 else number_of (bin_succ v))"
apply (cut_tac n = 0 in Suc_nat_number_of_add)
apply (simp cong del: if_weak_cong)
done


subsubsection{*Addition *}

(*"neg" is used in rewrite rules for binary comparisons*)
lemma add_nat_number_of [simp]:
     "(number_of v :: nat) + number_of v' =  
         (if neg (number_of v :: int) then number_of v'  
          else if neg (number_of v' :: int) then number_of v  
          else number_of (bin_add v v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_add_distrib [symmetric]) 


subsubsection{*Subtraction *}

lemma diff_nat_eq_if:
     "nat z - nat z' =  
        (if neg z' then nat z   
         else let d = z-z' in     
              if neg d then 0 else nat d)"
apply (simp add: Let_def nat_diff_distrib [symmetric] neg_eq_less_0 not_neg_eq_ge_0)
apply (simp add: diff_is_0_eq nat_le_eq_zle)
done

lemma diff_nat_number_of [simp]: 
     "(number_of v :: nat) - number_of v' =  
        (if neg (number_of v' :: int) then number_of v  
         else let d = number_of (bin_add v (bin_minus v')) in     
              if neg d then 0 else nat d)"
by (simp del: nat_number_of add: diff_nat_eq_if nat_number_of_def) 



subsubsection{*Multiplication *}

lemma mult_nat_number_of [simp]:
     "(number_of v :: nat) * number_of v' =  
       (if neg (number_of v :: int) then 0 else number_of (bin_mult v v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_mult_distrib [symmetric]) 



subsubsection{*Quotient *}

lemma div_nat_number_of [simp]:
     "(number_of v :: nat)  div  number_of v' =  
          (if neg (number_of v :: int) then 0  
           else nat (number_of v div number_of v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_div_distrib [symmetric]) 

lemma one_div_nat_number_of [simp]:
     "(Suc 0)  div  number_of v' = (nat (1 div number_of v'))" 
by (simp del: nat_numeral_1_eq_1 add: numeral_1_eq_Suc_0 [symmetric]) 


subsubsection{*Remainder *}

lemma mod_nat_number_of [simp]:
     "(number_of v :: nat)  mod  number_of v' =  
        (if neg (number_of v :: int) then 0  
         else if neg (number_of v' :: int) then number_of v  
         else nat (number_of v mod number_of v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_mod_distrib [symmetric]) 

lemma one_mod_nat_number_of [simp]:
     "(Suc 0)  mod  number_of v' =  
        (if neg (number_of v' :: int) then Suc 0
         else nat (1 mod number_of v'))"
by (simp del: nat_numeral_1_eq_1 add: numeral_1_eq_Suc_0 [symmetric]) 



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

(*"neg" is used in rewrite rules for binary comparisons*)
lemma eq_nat_number_of [simp]:
     "((number_of v :: nat) = number_of v') =  
      (if neg (number_of v :: int) then (iszero (number_of v' :: int) | neg (number_of v' :: int))  
       else if neg (number_of v' :: int) then iszero (number_of v :: int)  
       else iszero (number_of (bin_add v (bin_minus v')) :: int))"
apply (simp only: simp_thms neg_nat not_neg_eq_ge_0 nat_number_of_def
                  eq_nat_nat_iff eq_number_of_eq nat_0 iszero_def
            split add: split_if cong add: imp_cong)
apply (simp only: nat_eq_iff nat_eq_iff2)
apply (simp add: not_neg_eq_ge_0 [symmetric])
done


subsubsection{*Less-than (<) *}

(*"neg" is used in rewrite rules for binary comparisons*)
lemma less_nat_number_of [simp]:
     "((number_of v :: nat) < number_of v') =  
         (if neg (number_of v :: int) then neg (number_of (bin_minus v') :: int)  
          else neg (number_of (bin_add v (bin_minus v')) :: int))"
by (simp only: simp_thms neg_nat not_neg_eq_ge_0 nat_number_of_def
                nat_less_eq_zless less_number_of_eq_neg zless_nat_eq_int_zless
         cong add: imp_cong, simp) 




(*Maps #n to n for n = 0, 1, 2*)
lemmas numerals = nat_numeral_0_eq_0 nat_numeral_1_eq_1 numeral_2_eq_2


subsection{*General Theorems About Powers Involving Binary Numerals*}

text{*We cannot refer to the number @{term 2} in @{text Ring_and_Field.thy}.
We cannot prove general results about the numeral @{term "-1"}, so we have to
use @{term "- 1"} instead.*}

lemma power2_eq_square: "(a::'a::{semiring,ringpower})\<twosuperior> = a * a"
  by (simp add: numeral_2_eq_2 Power.power_Suc)

lemma [simp]: "(0::'a::{semiring,ringpower})\<twosuperior> = 0"
  by (simp add: power2_eq_square)

lemma [simp]: "(1::'a::{semiring,ringpower})\<twosuperior> = 1"
  by (simp add: power2_eq_square)

text{*Squares of literal numerals will be evaluated.*}
declare power2_eq_square [of "number_of w", standard, simp]

lemma zero_le_power2 [simp]: "0 \<le> (a\<twosuperior>::'a::{ordered_ring,ringpower})"
  by (simp add: power2_eq_square zero_le_square)

lemma zero_less_power2 [simp]:
     "(0 < a\<twosuperior>) = (a \<noteq> (0::'a::{ordered_ring,ringpower}))"
  by (force simp add: power2_eq_square zero_less_mult_iff linorder_neq_iff)

lemma zero_eq_power2 [simp]:
     "(a\<twosuperior> = 0) = (a = (0::'a::{ordered_ring,ringpower}))"
  by (force simp add: power2_eq_square mult_eq_0_iff)

lemma abs_power2 [simp]:
     "abs(a\<twosuperior>) = (a\<twosuperior>::'a::{ordered_ring,ringpower})"
  by (simp add: power2_eq_square abs_mult abs_mult_self)

lemma power2_abs [simp]:
     "(abs a)\<twosuperior> = (a\<twosuperior>::'a::{ordered_ring,ringpower})"
  by (simp add: power2_eq_square abs_mult_self)

lemma power2_minus [simp]:
     "(- a)\<twosuperior> = (a\<twosuperior>::'a::{ring,ringpower})"
  by (simp add: power2_eq_square)

lemma power_minus1_even: "(- 1) ^ (2*n) = (1::'a::{ring,ringpower})"
apply (induct_tac "n")
apply (auto simp add: power_Suc power_add)
done

lemma power_even_eq: "(a::'a::ringpower) ^ (2*n) = (a^n)^2"
by (simp add: power_mult power_mult_distrib power2_eq_square)

lemma power_odd_eq: "(a::int) ^ Suc(2*n) = a * (a^n)^2"
by (simp add: power_even_eq) 

lemma power_minus_even [simp]:
     "(-a) ^ (2*n) = (a::'a::{ring,ringpower}) ^ (2*n)"
by (simp add: power_minus1_even power_minus [of a]) 

lemma zero_le_even_power:
     "0 \<le> (a::'a::{ordered_ring,ringpower}) ^ (2*n)"
proof (induct "n")
  case 0
    show ?case by (simp add: zero_le_one)
next
  case (Suc n)
    have "a ^ (2 * Suc n) = (a*a) * a ^ (2*n)" 
      by (simp add: mult_ac power_add power2_eq_square)
    thus ?case
      by (simp add: prems zero_le_square zero_le_mult_iff)
qed

lemma odd_power_less_zero:
     "(a::'a::{ordered_ring,ringpower}) < 0 ==> a ^ Suc(2*n) < 0"
proof (induct "n")
  case 0
    show ?case by (simp add: Power.power_Suc)
next
  case (Suc n)
    have "a ^ Suc (2 * Suc n) = (a*a) * a ^ Suc(2*n)" 
      by (simp add: mult_ac power_add power2_eq_square Power.power_Suc)
    thus ?case
      by (simp add: prems mult_less_0_iff mult_neg)
qed

lemma odd_0_le_power_imp_0_le:
     "0 \<le> a  ^ Suc(2*n) ==> 0 \<le> (a::'a::{ordered_ring,ringpower})"
apply (insert odd_power_less_zero [of a n]) 
apply (force simp add: linorder_not_less [symmetric]) 
done


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
apply (case_tac "m")
apply (simp_all add: numerals)
done

lemma mult_eq_if: "(m::nat) * n = (if m=0 then 0 else n + ((m - 1) * n))"
apply (case_tac "m")
apply (simp_all add: numerals)
done

lemma power_eq_if: "(p ^ m :: nat) = (if m=0 then 1 else p * (p ^ (m - 1)))"
apply (case_tac "m")
apply (simp_all add: numerals)
done

lemma diff_less': "[| 0<n; 0<m |] ==> m - n < (m::nat)"
by (simp add: diff_less numerals)

declare diff_less' [of "number_of v", standard, simp]


subsection{*Comparisons involving (0::nat) *}

text{*Simplification already does @{term "n<0"}, @{term "n\<le>0"} and @{term "0\<le>n"}.*}

lemma eq_number_of_0 [simp]:
     "(number_of v = (0::nat)) =  
      (if neg (number_of v :: int) then True else iszero (number_of v :: int))"
by (simp del: nat_numeral_0_eq_0 add: nat_numeral_0_eq_0 [symmetric] iszero_0)

lemma eq_0_number_of [simp]:
     "((0::nat) = number_of v) =  
      (if neg (number_of v :: int) then True else iszero (number_of v :: int))"
by (rule trans [OF eq_sym_conv eq_number_of_0])

lemma less_0_number_of [simp]:
     "((0::nat) < number_of v) = neg (number_of (bin_minus v) :: int)"
by (simp del: nat_numeral_0_eq_0 add: nat_numeral_0_eq_0 [symmetric])


lemma neg_imp_number_of_eq_0: "neg (number_of v :: int) ==> number_of v = (0::nat)"
by (simp del: nat_numeral_0_eq_0 add: nat_numeral_0_eq_0 [symmetric] iszero_0)



subsection{*Comparisons involving Suc *}

lemma eq_number_of_Suc [simp]:
     "(number_of v = Suc n) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then False else nat pv = n)"
apply (simp only: simp_thms Let_def neg_eq_less_0 linorder_not_less 
                  number_of_pred nat_number_of_def 
            split add: split_if)
apply (rule_tac x = "number_of v" in spec)
apply (auto simp add: nat_eq_iff)
done

lemma Suc_eq_number_of [simp]:
     "(Suc n = number_of v) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then False else nat pv = n)"
by (rule trans [OF eq_sym_conv eq_number_of_Suc])

lemma less_number_of_Suc [simp]:
     "(number_of v < Suc n) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then True else nat pv < n)"
apply (simp only: simp_thms Let_def neg_eq_less_0 linorder_not_less 
                  number_of_pred nat_number_of_def  
            split add: split_if)
apply (rule_tac x = "number_of v" in spec)
apply (auto simp add: nat_less_iff)
done

lemma less_Suc_number_of [simp]:
     "(Suc n < number_of v) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then False else n < nat pv)"
apply (simp only: simp_thms Let_def neg_eq_less_0 linorder_not_less 
                  number_of_pred nat_number_of_def
            split add: split_if)
apply (rule_tac x = "number_of v" in spec)
apply (auto simp add: zless_nat_eq_int_zless)
done

lemma le_number_of_Suc [simp]:
     "(number_of v <= Suc n) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then True else nat pv <= n)"
by (simp add: Let_def less_Suc_number_of linorder_not_less [symmetric])

lemma le_Suc_number_of [simp]:
     "(Suc n <= number_of v) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then False else n <= nat pv)"
by (simp add: Let_def less_number_of_Suc linorder_not_less [symmetric])


(* Push int(.) inwards: *)
declare zadd_int [symmetric, simp]

lemma lemma1: "(m+m = n+n) = (m = (n::int))"
by auto

lemma lemma2: "m+m ~= (1::int) + (n + n)"
apply auto
apply (drule_tac f = "%x. x mod 2" in arg_cong)
apply (simp add: zmod_zadd1_eq)
done

lemma eq_number_of_BIT_BIT:
     "((number_of (v BIT x) ::int) = number_of (w BIT y)) =  
      (x=y & (((number_of v) ::int) = number_of w))"
by (simp only: simp_thms number_of_BIT lemma1 lemma2 eq_commute
               Ring_and_Field.add_left_cancel add_assoc Ring_and_Field.add_0
            split add: split_if cong: imp_cong) 


lemma eq_number_of_BIT_Pls:
     "((number_of (v BIT x) ::int) = number_of bin.Pls) =  
      (x=False & (((number_of v) ::int) = number_of bin.Pls))"
apply (simp only: simp_thms  add: number_of_BIT number_of_Pls eq_commute
            split add: split_if cong: imp_cong)
apply (rule_tac x = "number_of v" in spec, safe)
apply (simp_all (no_asm_use))
apply (drule_tac f = "%x. x mod 2" in arg_cong)
apply (simp add: zmod_zadd1_eq)
done

lemma eq_number_of_BIT_Min:
     "((number_of (v BIT x) ::int) = number_of bin.Min) =  
      (x=True & (((number_of v) ::int) = number_of bin.Min))"
apply (simp only: simp_thms  add: number_of_BIT number_of_Min eq_commute
            split add: split_if cong: imp_cong)
apply (rule_tac x = "number_of v" in spec, auto)
apply (drule_tac f = "%x. x mod 2" in arg_cong, auto)
done

lemma eq_number_of_Pls_Min: "(number_of bin.Pls ::int) ~= number_of bin.Min"
by auto



subsection{*Literal arithmetic involving powers*}

lemma nat_power_eq: "(0::int) <= z ==> nat (z^n) = nat z ^ n"
apply (induct_tac "n")
apply (simp_all (no_asm_simp) add: nat_mult_distrib)
done

lemma power_nat_number_of:
     "(number_of v :: nat) ^ n =  
       (if neg (number_of v :: int) then 0^n else nat ((number_of v :: int) ^ n))"
by (simp only: simp_thms neg_nat not_neg_eq_ge_0 nat_number_of_def nat_power_eq
         split add: split_if cong: imp_cong)


declare power_nat_number_of [of _ "number_of w", standard, simp]


text{*For the integers*}

lemma zpower_number_of_even:
     "(z::int) ^ number_of (w BIT False) =  
      (let w = z ^ (number_of w) in  w*w)"
apply (simp del: nat_number_of  add: nat_number_of_def number_of_BIT Let_def)
apply (simp only: number_of_add) 
apply (rule_tac x = "number_of w" in spec, clarify)
apply (case_tac " (0::int) <= x")
apply (auto simp add: nat_mult_distrib power_even_eq power2_eq_square)
done

lemma zpower_number_of_odd:
     "(z::int) ^ number_of (w BIT True) =  
          (if (0::int) <= number_of w                    
           then (let w = z ^ (number_of w) in  z*w*w)    
           else 1)"
apply (simp del: nat_number_of  add: nat_number_of_def number_of_BIT Let_def)
apply (simp only: number_of_add nat_numeral_1_eq_1 not_neg_eq_ge_0 neg_eq_less_0) 
apply (rule_tac x = "number_of w" in spec, clarify)
apply (auto simp add: nat_add_distrib nat_mult_distrib power_even_eq power2_eq_square neg_nat)
done

declare zpower_number_of_even [of "number_of v", standard, simp]
declare zpower_number_of_odd  [of "number_of v", standard, simp]



ML
{*
val numerals = thms"numerals";
val numeral_ss = simpset() addsimps numerals;

val nat_bin_arith_setup =
 [Fast_Arith.map_data 
   (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
     {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms,
      inj_thms = inj_thms,
      lessD = lessD,
      simpset = simpset addsimps [Suc_nat_number_of, int_nat_number_of,
                                  not_neg_number_of_Pls,
                                  neg_number_of_Min,neg_number_of_BIT]})]
*}

setup nat_bin_arith_setup

(* Enable arith to deal with div/mod k where k is a numeral: *)
declare split_div[of _ _ "number_of k", standard, arith_split]
declare split_mod[of _ _ "number_of k", standard, arith_split]

lemma nat_number_of_Pls: "number_of bin.Pls = (0::nat)"
  by (simp add: number_of_Pls nat_number_of_def)

lemma nat_number_of_Min: "number_of bin.Min = (0::nat)"
  apply (simp only: number_of_Min nat_number_of_def nat_zminus_int)
  apply (simp add: neg_nat)
  done

lemma nat_number_of_BIT_True:
  "number_of (w BIT True) =
    (if neg (number_of w :: int) then 0
     else let n = number_of w in Suc (n + n))"
  apply (simp only: nat_number_of_def Let_def split: split_if)
  apply (intro conjI impI)
   apply (simp add: neg_nat neg_number_of_BIT)
  apply (rule int_int_eq [THEN iffD1])
  apply (simp only: not_neg_nat neg_number_of_BIT int_Suc zadd_int [symmetric] simp_thms)
  apply (simp only: number_of_BIT if_True zadd_assoc)
  done

lemma nat_number_of_BIT_False:
    "number_of (w BIT False) = (let n::nat = number_of w in n + n)"
  apply (simp only: nat_number_of_def Let_def)
  apply (cases "neg (number_of w :: int)")
   apply (simp add: neg_nat neg_number_of_BIT)
  apply (rule int_int_eq [THEN iffD1])
  apply (simp only: not_neg_nat neg_number_of_BIT int_Suc zadd_int [symmetric] simp_thms)
  apply (simp only: number_of_BIT if_False zadd_0 zadd_assoc)
  done

lemmas nat_number =
  nat_number_of_Pls nat_number_of_Min
  nat_number_of_BIT_True nat_number_of_BIT_False

lemma Let_Suc [simp]: "Let (Suc n) f == f (Suc n)"
  by (simp add: Let_def)

lemma power_m1_even: "(-1) ^ (2*n) = (1::'a::{number_ring,ringpower})"
by (simp add: power_mult); 

lemma power_m1_odd: "(-1) ^ Suc(2*n) = (-1::'a::{number_ring,ringpower})"
by (simp add: power_mult power_Suc); 


subsection{*Literal arithmetic and @{term of_nat}*}

lemma of_nat_double:
     "0 \<le> x ==> of_nat (nat (2 * x)) = of_nat (nat x) + of_nat (nat x)"
by (simp only: mult_2 nat_add_distrib of_nat_add) 

lemma nat_numeral_m1_eq_0: "-1 = (0::nat)"
by (simp only:  nat_number_of_def, simp)

lemma int_double_iff: "(0::int) \<le> 2*x + 1 = (0 \<le> x)"
by arith

lemma of_nat_number_of_lemma:
     "of_nat (number_of v :: nat) =  
         (if 0 \<le> (number_of v :: int) 
          then (number_of v :: 'a :: number_ring)
          else 0)"
apply (induct v, simp, simp add: nat_numeral_m1_eq_0)
apply (simp only: number_of nat_number_of_def)
txt{*Generalize in order to eliminate the function @{term number_of} and
its annoying simprules*}
apply (erule rev_mp)
apply (rule_tac x="number_of bin :: int" in spec) 
apply (rule_tac x="number_of bin :: 'a" in spec) 
apply (simp add: nat_add_distrib of_nat_double int_double_iff)
done

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
          else number_of (bin_add v v') + k)"
by simp

lemma nat_number_of_mult_left:
     "number_of v * (number_of v' * (k::nat)) =  
         (if neg (number_of v :: int) then 0
          else number_of (bin_mult v v') * k)"
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


subsubsection{*For @{text cancel_factor} *}

lemma nat_mult_le_cancel_disj: "(k*m <= k*n) = ((0::nat) < k --> m<=n)"
by auto

lemma nat_mult_less_cancel_disj: "(k*m < k*n) = ((0::nat) < k & m<n)"
by auto

lemma nat_mult_eq_cancel_disj: "(k*m = k*n) = (k = (0::nat) | m=n)"
by auto

lemma nat_mult_div_cancel_disj:
     "(k*m) div (k*n) = (if k = (0::nat) then 0 else m div n)"
by (simp add: nat_mult_div_cancel1)


ML
{*
val eq_nat_nat_iff = thm"eq_nat_nat_iff";
val eq_nat_number_of = thm"eq_nat_number_of";
val less_nat_number_of = thm"less_nat_number_of";
val power2_eq_square = thm "power2_eq_square";
val zero_le_power2 = thm "zero_le_power2";
val zero_less_power2 = thm "zero_less_power2";
val zero_eq_power2 = thm "zero_eq_power2";
val abs_power2 = thm "abs_power2";
val power2_abs = thm "power2_abs";
val power2_minus = thm "power2_minus";
val power_minus1_even = thm "power_minus1_even";
val power_minus_even = thm "power_minus_even";
val zero_le_even_power = thm "zero_le_even_power";
val odd_power_less_zero = thm "odd_power_less_zero";
val odd_0_le_power_imp_0_le = thm "odd_0_le_power_imp_0_le";

val Suc_pred' = thm"Suc_pred'";
val expand_Suc = thm"expand_Suc";
val Suc_eq_add_numeral_1 = thm"Suc_eq_add_numeral_1";
val Suc_eq_add_numeral_1_left = thm"Suc_eq_add_numeral_1_left";
val add_eq_if = thm"add_eq_if";
val mult_eq_if = thm"mult_eq_if";
val power_eq_if = thm"power_eq_if";
val diff_less' = thm"diff_less'";
val eq_number_of_0 = thm"eq_number_of_0";
val eq_0_number_of = thm"eq_0_number_of";
val less_0_number_of = thm"less_0_number_of";
val neg_imp_number_of_eq_0 = thm"neg_imp_number_of_eq_0";
val eq_number_of_Suc = thm"eq_number_of_Suc";
val Suc_eq_number_of = thm"Suc_eq_number_of";
val less_number_of_Suc = thm"less_number_of_Suc";
val less_Suc_number_of = thm"less_Suc_number_of";
val le_number_of_Suc = thm"le_number_of_Suc";
val le_Suc_number_of = thm"le_Suc_number_of";
val eq_number_of_BIT_BIT = thm"eq_number_of_BIT_BIT";
val eq_number_of_BIT_Pls = thm"eq_number_of_BIT_Pls";
val eq_number_of_BIT_Min = thm"eq_number_of_BIT_Min";
val eq_number_of_Pls_Min = thm"eq_number_of_Pls_Min";
val of_nat_number_of_eq = thm"of_nat_number_of_eq";
val nat_power_eq = thm"nat_power_eq";
val power_nat_number_of = thm"power_nat_number_of";
val zpower_number_of_even = thm"zpower_number_of_even";
val zpower_number_of_odd = thm"zpower_number_of_odd";
val nat_number_of_Pls = thm"nat_number_of_Pls";
val nat_number_of_Min = thm"nat_number_of_Min";
val nat_number_of_BIT_True = thm"nat_number_of_BIT_True";
val nat_number_of_BIT_False = thm"nat_number_of_BIT_False";
val Let_Suc = thm"Let_Suc";

val nat_number = thms"nat_number";

val nat_number_of_add_left = thm"nat_number_of_add_left";
val nat_number_of_mult_left = thm"nat_number_of_mult_left";
val left_add_mult_distrib = thm"left_add_mult_distrib";
val nat_diff_add_eq1 = thm"nat_diff_add_eq1";
val nat_diff_add_eq2 = thm"nat_diff_add_eq2";
val nat_eq_add_iff1 = thm"nat_eq_add_iff1";
val nat_eq_add_iff2 = thm"nat_eq_add_iff2";
val nat_less_add_iff1 = thm"nat_less_add_iff1";
val nat_less_add_iff2 = thm"nat_less_add_iff2";
val nat_le_add_iff1 = thm"nat_le_add_iff1";
val nat_le_add_iff2 = thm"nat_le_add_iff2";
val nat_mult_le_cancel1 = thm"nat_mult_le_cancel1";
val nat_mult_less_cancel1 = thm"nat_mult_less_cancel1";
val nat_mult_eq_cancel1 = thm"nat_mult_eq_cancel1";
val nat_mult_div_cancel1 = thm"nat_mult_div_cancel1";
val nat_mult_le_cancel_disj = thm"nat_mult_le_cancel_disj";
val nat_mult_less_cancel_disj = thm"nat_mult_less_cancel_disj";
val nat_mult_eq_cancel_disj = thm"nat_mult_eq_cancel_disj";
val nat_mult_div_cancel_disj = thm"nat_mult_div_cancel_disj";

val power_minus_even = thm"power_minus_even";
val zero_le_even_power = thm"zero_le_even_power";
*}


subsection {* Configuration of the code generator *}

ML {*
infix 7 `*;
infix 6 `+;

val op `* = op * : int * int -> int;
val op `+ = op + : int * int -> int;
val `~ = ~ : int -> int;
*}

types_code
  "int" ("int")

constdefs
  int_aux :: "int \<Rightarrow> nat \<Rightarrow> int"
  "int_aux i n == (i + int n)"
  nat_aux :: "nat \<Rightarrow> int \<Rightarrow> nat"
  "nat_aux n i == (n + nat i)"

lemma [code]:
  "int_aux i 0 = i"
  "int_aux i (Suc n) = int_aux (i + 1) n" -- {* tail recursive *}
  "int n = int_aux 0 n"
  by (simp add: int_aux_def)+

lemma [code]: "nat_aux n i = (if i <= 0 then n else nat_aux (Suc n) (i - 1))"
  by (simp add: nat_aux_def Suc_nat_eq_nat_zadd1) -- {* tail recursive *}
lemma [code]: "nat i = nat_aux 0 i"
  by (simp add: nat_aux_def)

consts_code
  "0" :: "int"                  ("0")
  "1" :: "int"                  ("1")
  "uminus" :: "int => int"      ("`~")
  "op +" :: "int => int => int" ("(_ `+/ _)")
  "op *" :: "int => int => int" ("(_ `*/ _)")
  "op <" :: "int => int => bool" ("(_ </ _)")
  "op <=" :: "int => int => bool" ("(_ <=/ _)")
  "neg"                         ("(_ < 0)")

ML {*
fun number_of_codegen thy gr s b (Const ("Numeral.number_of",
      Type ("fun", [_, Type ("IntDef.int", [])])) $ bin) =
        (Some (gr, Pretty.str (string_of_int (HOLogic.dest_binum bin)))
        handle TERM _ => None)
  | number_of_codegen thy gr s b (Const ("Numeral.number_of",
      Type ("fun", [_, Type ("nat", [])])) $ bin) =
        Some (Codegen.invoke_codegen thy s b (gr,
          Const ("IntDef.nat", HOLogic.intT --> HOLogic.natT) $
            (Const ("Numeral.number_of", HOLogic.binT --> HOLogic.intT) $ bin)))
  | number_of_codegen _ _ _ _ _ = None;
*}

setup {* [Codegen.add_codegen "number_of_codegen" number_of_codegen] *}

end
