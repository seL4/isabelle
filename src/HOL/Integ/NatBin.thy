(*  Title:      HOL/NatBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary arithmetic for the natural numbers *}

theory NatBin = IntPower:

text {*
  Arithmetic for naturals is reduced to that for the non-negative integers.
*}

instance nat :: number ..

defs (overloaded)
  nat_number_of_def:
     "(number_of::bin => nat) v == nat ((number_of :: bin => int) v)"


(** nat (coercion from int to nat) **)

declare nat_0 [simp] nat_1 [simp]

lemma nat_number_of [simp]: "nat (number_of w) = number_of w"
by (simp add: nat_number_of_def)

lemma numeral_0_eq_0: "Numeral0 = (0::nat)"
by (simp add: nat_number_of_def)

lemma numeral_1_eq_1: "Numeral1 = (1::nat)"
by (simp add: nat_1 nat_number_of_def)

lemma numeral_1_eq_Suc_0: "Numeral1 = Suc 0"
by (simp add: numeral_1_eq_1)

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
 prefer 2 apply (simp add: numeral_0_eq_0 pos_imp_zdiv_nonneg_iff) 
apply (rule inj_int [THEN injD], simp)
apply (rule_tac r = "int (m mod m') " in quorem_div)
 prefer 2 apply force
apply (simp add: nat_less_iff [symmetric] quorem_def numeral_0_eq_0 zadd_int 
                 zmult_int)
done

(*Fails if z'<0: the LHS collapses to (nat z) but the RHS doesn't*)
lemma nat_mod_distrib:
     "[| (0::int) <= z;  0 <= z' |] ==> nat (z mod z') = nat z mod nat z'"
apply (case_tac "z' = 0", simp add: DIVISION_BY_ZERO)
apply (auto elim!: nonneg_eq_int)
apply (rename_tac m m')
apply (subgoal_tac "0 <= int m mod int m'")
 prefer 2 apply (simp add: nat_less_iff numeral_0_eq_0 pos_mod_sign) 
apply (rule inj_int [THEN injD], simp)
apply (rule_tac q = "int (m div m') " in quorem_mod)
 prefer 2 apply force
apply (simp add: nat_less_iff [symmetric] quorem_def numeral_0_eq_0 zadd_int zmult_int)
done


(** int (coercion from nat to int) **)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma int_nat_number_of:
     "int (number_of v :: nat) =  
         (if neg (number_of v) then 0  
          else (number_of v :: int))"
by (simp del: nat_number_of
	 add: neg_nat nat_number_of_def not_neg_nat add_assoc)
declare int_nat_number_of [simp]


(** Successor **)

lemma Suc_nat_eq_nat_zadd1: "(0::int) <= z ==> Suc (nat z) = nat (1 + z)"
apply (rule sym)
apply (simp add: nat_eq_iff int_Suc)
done

lemma Suc_nat_number_of_add:
     "Suc (number_of v + n) =  
        (if neg (number_of v) then 1+n else number_of (bin_succ v) + n)" 
by (simp del: nat_number_of 
         add: nat_number_of_def neg_nat
              Suc_nat_eq_nat_zadd1 number_of_succ) 

lemma Suc_nat_number_of:
     "Suc (number_of v) =  
        (if neg (number_of v) then 1 else number_of (bin_succ v))"
apply (cut_tac n = 0 in Suc_nat_number_of_add)
apply (simp cong del: if_weak_cong)
done
declare Suc_nat_number_of [simp]


(** Addition **)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma add_nat_number_of:
     "(number_of v :: nat) + number_of v' =  
         (if neg (number_of v) then number_of v'  
          else if neg (number_of v') then number_of v  
          else number_of (bin_add v v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_add_distrib [symmetric]) 

declare add_nat_number_of [simp]


(** Subtraction **)

lemma diff_nat_eq_if:
     "nat z - nat z' =  
        (if neg z' then nat z   
         else let d = z-z' in     
              if neg d then 0 else nat d)"
apply (simp add: Let_def nat_diff_distrib [symmetric] neg_eq_less_0 not_neg_eq_ge_0)
apply (simp add: diff_is_0_eq nat_le_eq_zle)
done

lemma diff_nat_number_of: 
     "(number_of v :: nat) - number_of v' =  
        (if neg (number_of v') then number_of v  
         else let d = number_of (bin_add v (bin_minus v')) in     
              if neg d then 0 else nat d)"
by (simp del: nat_number_of add: diff_nat_eq_if nat_number_of_def) 

declare diff_nat_number_of [simp]


(** Multiplication **)

lemma mult_nat_number_of:
     "(number_of v :: nat) * number_of v' =  
       (if neg (number_of v) then 0 else number_of (bin_mult v v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_mult_distrib [symmetric]) 

declare mult_nat_number_of [simp]


(** Quotient **)

lemma div_nat_number_of:
     "(number_of v :: nat)  div  number_of v' =  
          (if neg (number_of v) then 0  
           else nat (number_of v div number_of v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_div_distrib [symmetric]) 

declare div_nat_number_of [simp]


(** Remainder **)

lemma mod_nat_number_of:
     "(number_of v :: nat)  mod  number_of v' =  
        (if neg (number_of v) then 0  
         else if neg (number_of v') then number_of v  
         else nat (number_of v mod number_of v'))"
by (force dest!: neg_nat
          simp del: nat_number_of
          simp add: nat_number_of_def nat_mod_distrib [symmetric]) 

declare mod_nat_number_of [simp]

ML
{*
val nat_number_of_def = thm"nat_number_of_def";

val nat_number_of = thm"nat_number_of";
val numeral_0_eq_0 = thm"numeral_0_eq_0";
val numeral_1_eq_1 = thm"numeral_1_eq_1";
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


ML
{*
structure NatAbstractNumeralsData =
  struct
  val dest_eq		= HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral	= Bin_Simprocs.is_numeral
  val numeral_0_eq_0    = numeral_0_eq_0
  val numeral_1_eq_1    = numeral_1_eq_Suc_0
  val prove_conv        = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps	= ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq  = Bin_Simprocs.simplify_meta_eq 
  end;

structure NatAbstractNumerals = AbstractNumeralsFun (NatAbstractNumeralsData);

val nat_eval_numerals = 
  map Bin_Simprocs.prep_simproc
   [("nat_div_eval_numerals", ["(Suc 0) div m"], NatAbstractNumerals.proc div_nat_number_of),
    ("nat_mod_eval_numerals", ["(Suc 0) mod m"], NatAbstractNumerals.proc mod_nat_number_of)];

Addsimprocs nat_eval_numerals;
*}

(*** Comparisons ***)

(** Equals (=) **)

lemma eq_nat_nat_iff:
     "[| (0::int) <= z;  0 <= z' |] ==> (nat z = nat z') = (z=z')"
by (auto elim!: nonneg_eq_int)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma eq_nat_number_of:
     "((number_of v :: nat) = number_of v') =  
      (if neg (number_of v) then (iszero (number_of v') | neg (number_of v'))  
       else if neg (number_of v') then iszero (number_of v)  
       else iszero (number_of (bin_add v (bin_minus v'))))"
apply (simp only: simp_thms neg_nat not_neg_eq_ge_0 nat_number_of_def
                  eq_nat_nat_iff eq_number_of_eq nat_0 iszero_def
            split add: split_if cong add: imp_cong)
apply (simp only: nat_eq_iff nat_eq_iff2)
apply (simp add: not_neg_eq_ge_0 [symmetric])
done

declare eq_nat_number_of [simp]

(** Less-than (<) **)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma less_nat_number_of:
     "((number_of v :: nat) < number_of v') =  
         (if neg (number_of v) then neg (number_of (bin_minus v'))  
          else neg (number_of (bin_add v (bin_minus v'))))"
apply (simp only: simp_thms neg_nat not_neg_eq_ge_0 nat_number_of_def
                nat_less_eq_zless less_number_of_eq_neg zless_nat_eq_int_zless
            cong add: imp_cong, simp) 
done

declare less_nat_number_of [simp]


(** Less-than-or-equals (<=) **)

lemma le_nat_number_of_eq_not_less:
     "(number_of x <= (number_of y::nat)) =  
      (~ number_of y < (number_of x::nat))"
apply (rule linorder_not_less [symmetric])
done

declare le_nat_number_of_eq_not_less [simp]


(*Maps #n to n for n = 0, 1, 2*)
lemmas numerals = numeral_0_eq_0 numeral_1_eq_1 numeral_2_eq_2


(** Nat **)

lemma Suc_pred': "0 < n ==> n = Suc(n - 1)"
by (simp add: numerals)

(*Expresses a natural number constant as the Suc of another one.
  NOT suitable for rewriting because n recurs in the condition.*)
lemmas expand_Suc = Suc_pred' [of "number_of v", standard]

(** Arith **)

lemma Suc_eq_add_numeral_1: "Suc n = n + 1"
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

(** Power **)

lemma power_two: "(p::nat) ^ 2 = p*p"
by (simp add: numerals)


(*** Comparisons involving (0::nat) ***)

lemma eq_number_of_0:
     "(number_of v = (0::nat)) =  
      (if neg (number_of v) then True else iszero (number_of v))"
apply (simp add: numeral_0_eq_0 [symmetric] iszero_0)
done

lemma eq_0_number_of:
     "((0::nat) = number_of v) =  
      (if neg (number_of v) then True else iszero (number_of v))"
apply (rule trans [OF eq_sym_conv eq_number_of_0])
done

lemma less_0_number_of:
     "((0::nat) < number_of v) = neg (number_of (bin_minus v))"
by (simp add: numeral_0_eq_0 [symmetric])

(*Simplification already handles n<0, n<=0 and 0<=n.*)
declare eq_number_of_0 [simp] eq_0_number_of [simp] less_0_number_of [simp]

lemma neg_imp_number_of_eq_0: "neg (number_of v) ==> number_of v = (0::nat)"
by (simp add: numeral_0_eq_0 [symmetric] iszero_0)



(*** Comparisons involving Suc ***)

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
apply (rule trans [OF eq_sym_conv eq_number_of_Suc])
done

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
apply (simp add: Let_def less_Suc_number_of linorder_not_less [symmetric])
done

lemma le_Suc_number_of [simp]:
     "(Suc n <= number_of v) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then False else n <= nat pv)"
apply (simp add: Let_def less_number_of_Suc linorder_not_less [symmetric])
done


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
               Ring_and_Field.add_left_cancel add_assoc left_zero
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



(*** Literal arithmetic involving powers, type nat ***)

lemma nat_power_eq: "(0::int) <= z ==> nat (z^n) = nat z ^ n"
apply (induct_tac "n")
apply (simp_all (no_asm_simp) add: nat_mult_distrib)
done

lemma power_nat_number_of:
     "(number_of v :: nat) ^ n =  
       (if neg (number_of v) then 0^n else nat ((number_of v :: int) ^ n))"
by (simp only: simp_thms neg_nat not_neg_eq_ge_0 nat_number_of_def nat_power_eq
         split add: split_if cong: imp_cong)


declare power_nat_number_of [of _ "number_of w", standard, simp]



(*** Literal arithmetic involving powers, type int ***)

lemma zpower_even: "(z::int) ^ (2*a) = (z^a)^2"
by (simp add: zpower_zpower mult_commute)

lemma zpower_two: "(p::int) ^ 2 = p*p"
by (simp add: numerals)

lemma zpower_odd: "(z::int) ^ (2*a + 1) = z * (z^a)^2"
by (simp add: zpower_even zpower_zadd_distrib)

lemma zpower_number_of_even:
     "(z::int) ^ number_of (w BIT False) =  
      (let w = z ^ (number_of w) in  w*w)"
apply (simp del: nat_number_of  add: nat_number_of_def number_of_BIT Let_def)
apply (simp only: number_of_add) 
apply (rule_tac x = "number_of w" in spec, clarify)
apply (case_tac " (0::int) <= x")
apply (auto simp add: nat_mult_distrib zpower_even zpower_two)
done

lemma zpower_number_of_odd:
     "(z::int) ^ number_of (w BIT True) =  
          (if (0::int) <= number_of w                    
           then (let w = z ^ (number_of w) in  z*w*w)    
           else 1)"
apply (simp del: nat_number_of  add: nat_number_of_def number_of_BIT Let_def)
apply (simp only: number_of_add int_numeral_1_eq_1 not_neg_eq_ge_0 neg_eq_less_0) 
apply (rule_tac x = "number_of w" in spec, clarify)
apply (auto simp add: nat_add_distrib nat_mult_distrib zpower_even zpower_two neg_nat)
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
    (if neg (number_of w) then 0
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
  apply (cases "neg (number_of w)")
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


subsection {*More ML Bindings*}

ML
{*
val eq_nat_nat_iff = thm"eq_nat_nat_iff";
val eq_nat_number_of = thm"eq_nat_number_of";
val less_nat_number_of = thm"less_nat_number_of";
val le_nat_number_of_eq_not_less = thm"le_nat_number_of_eq_not_less";
val Suc_pred' = thm"Suc_pred'";
val expand_Suc = thm"expand_Suc";
val Suc_eq_add_numeral_1 = thm"Suc_eq_add_numeral_1";
val add_eq_if = thm"add_eq_if";
val mult_eq_if = thm"mult_eq_if";
val power_eq_if = thm"power_eq_if";
val diff_less' = thm"diff_less'";
val power_two = thm"power_two";
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
val nat_power_eq = thm"nat_power_eq";
val power_nat_number_of = thm"power_nat_number_of";
val zpower_even = thm"zpower_even";
val zpower_two = thm"zpower_two";
val zpower_odd = thm"zpower_odd";
val zpower_number_of_even = thm"zpower_number_of_even";
val zpower_number_of_odd = thm"zpower_number_of_odd";
val nat_number_of_Pls = thm"nat_number_of_Pls";
val nat_number_of_Min = thm"nat_number_of_Min";
val nat_number_of_BIT_True = thm"nat_number_of_BIT_True";
val nat_number_of_BIT_False = thm"nat_number_of_BIT_False";
val Let_Suc = thm"Let_Suc";

val nat_number = thms"nat_number";
*}

subsection {*Lemmas for the Combination and Cancellation Simprocs*}

lemma nat_number_of_add_left:
     "number_of v + (number_of v' + (k::nat)) =  
         (if neg (number_of v) then number_of v' + k  
          else if neg (number_of v') then number_of v + k  
          else number_of (bin_add v v') + k)"
apply simp
done


(** For combine_numerals **)

lemma left_add_mult_distrib: "i*u + (j*u + k) = (i+j)*u + (k::nat)"
by (simp add: add_mult_distrib)


(** For cancel_numerals **)

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


(** For cancel_numeral_factors **)

lemma nat_mult_le_cancel1: "(0::nat) < k ==> (k*m <= k*n) = (m<=n)"
by auto

lemma nat_mult_less_cancel1: "(0::nat) < k ==> (k*m < k*n) = (m<n)"
by auto

lemma nat_mult_eq_cancel1: "(0::nat) < k ==> (k*m = k*n) = (m=n)"
by auto

lemma nat_mult_div_cancel1: "(0::nat) < k ==> (k*m) div (k*n) = (m div n)"
by auto


(** For cancel_factor **)

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
val nat_number_of_add_left = thm"nat_number_of_add_left";
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
  "neg"                         ("(_ < 0)")

end
