(*  Title:      HOL/NatBin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the natural numbers
*)

(** nat (coercion from int to nat) **)

Goal "nat (number_of w) = number_of w";
by (simp_tac (simpset() addsimps [nat_number_of_def]) 1);
qed "nat_number_of";
Addsimps [nat_number_of];

(*These rewrites should one day be re-oriented...*)

Goal "#0 = 0";
by (simp_tac (simpset_of Int.thy addsimps [nat_0, nat_number_of_def]) 1);
qed "numeral_0_eq_0";

Goal "#1 = 1";
by (simp_tac (simpset_of Int.thy addsimps [nat_1, nat_number_of_def]) 1);
qed "numeral_1_eq_1";

Goal "#2 = 2";
by (simp_tac (simpset_of Int.thy addsimps [nat_2, nat_number_of_def]) 1);
qed "numeral_2_eq_2";


(** int (coercion from nat to int) **)

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "int (number_of v :: nat) = \
\        (if neg (number_of v) then #0 \
\         else (number_of v :: int))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, nat_number_of_def, 
				  not_neg_nat, int_0]) 1);
qed "int_nat_number_of";
Addsimps [int_nat_number_of];


(** Successor **)

Goal "(#0::int) <= z ==> Suc (nat z) = nat (#1 + z)";
br sym 1;
by (asm_simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "Suc_nat_eq_nat_zadd1";

Goal "Suc (number_of v) = \
\       (if neg (number_of v) then #1 else number_of (bin_succ v))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, nat_1, not_neg_eq_ge_0, 
				  nat_number_of_def, int_Suc, 
				  Suc_nat_eq_nat_zadd1, number_of_succ]) 1);
qed "Suc_nat_number_of";

Goal "Suc #0 = #1";
by (simp_tac (simpset() addsimps [Suc_nat_number_of]) 1);
qed "Suc_numeral_0_eq_1";

Goal "Suc #1 = #2";
by (simp_tac (simpset() addsimps [Suc_nat_number_of]) 1);
qed "Suc_numeral_1_eq_2";

(** Addition **)

Goal "[| (#0::int) <= z;  #0 <= z' |] ==> nat z + nat z' = nat (z+z')";
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zadd_int RS sym]) 1);
qed "add_nat_eq_nat_zadd";

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "(number_of v :: nat) + number_of v' = \
\        (if neg (number_of v) then number_of v' \
\         else if neg (number_of v') then number_of v \
\         else number_of (bin_add v v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  add_nat_eq_nat_zadd, number_of_add]) 1);
qed "add_nat_number_of";

Addsimps [add_nat_number_of];


(** Subtraction **)

Goal "[| (#0::int) <= z';  z' <= z |] ==> nat z - nat z' = nat (z-z')";
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zdiff_int RS sym, nat_le_eq_zle]) 1);
qed "diff_nat_eq_nat_zdiff";


Goal "nat z - nat z' = \
\       (if neg z' then nat z  \
\        else let d = z-z' in    \
\             if neg d then 0 else nat d)";
by (simp_tac (simpset() addsimps [Let_def, diff_nat_eq_nat_zdiff,
				  neg_eq_less_0, not_neg_eq_ge_0]) 1);
by (simp_tac (simpset() addsimps zcompare_rls@
		                 [diff_is_0_eq, nat_le_eq_zle]) 1);
qed "diff_nat_eq_if";

Goalw [nat_number_of_def]
     "(number_of v :: nat) - number_of v' = \
\       (if neg (number_of v') then number_of v \
\        else let d = number_of (bin_add v (bin_minus v')) in    \
\             if neg d then #0 else nat d)";
by (simp_tac
    (simpset_of Int.thy delcongs [if_weak_cong]
			addsimps [not_neg_eq_ge_0, nat_0,
				  diff_nat_eq_if, diff_number_of_eq]) 1);
qed "diff_nat_number_of";

Addsimps [diff_nat_number_of];


(** Multiplication **)

Goal "(#0::int) <= z ==> nat z * nat z' = nat (z*z')";
by (case_tac "#0 <= z'" 1);
by (subgoal_tac "z'*z <= #0" 2);
by (rtac (neg_imp_zmult_nonpos_iff RS iffD2) 3);
by Auto_tac;
by (subgoal_tac "#0 <= z*z'" 1);
by (force_tac (claset() addDs [zmult_zle_mono1], simpset()) 2);
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zmult_int RS sym]) 1);
qed "mult_nat_eq_nat_zmult";

Goal "(number_of v :: nat) * number_of v' = \
\      (if neg (number_of v) then #0 else number_of (bin_mult v v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  mult_nat_eq_nat_zmult, number_of_mult, 
				  nat_0]) 1);
qed "mult_nat_number_of";

Addsimps [mult_nat_number_of];


(** Quotient **)

Goal "(#0::int) <= z ==> nat z div nat z' = nat (z div z')";
by (case_tac "#0 <= z'" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [div_nonneg_neg, DIVISION_BY_ZERO_DIV]));
by (zdiv_undefined_case_tac "z' = #0" 1);
 by (simp_tac (simpset() addsimps [numeral_0_eq_0, DIVISION_BY_ZERO_DIV]) 1);
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
by (rename_tac "m m'" 1);
by (subgoal_tac "#0 <= int m div int m'" 1);
 by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, numeral_0_eq_0, 
				       pos_imp_zdiv_nonneg_iff]) 2);
by (rtac (inj_int RS injD) 1);
by (Asm_simp_tac 1);
by (rtac sym 1);
by (res_inst_tac [("r", "int (m mod m')")] quorem_div 1);
 by (Force_tac 2);
by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, quorem_def, 
				      numeral_0_eq_0, zadd_int, zmult_int, 
				      mod_less_divisor]) 1);
by (rtac (mod_div_equality RS sym RS trans) 1);
by (asm_simp_tac (simpset() addsimps add_ac@mult_ac) 1);
qed "div_nat_eq_nat_zdiv";

Goal "(number_of v :: nat)  div  number_of v' = \
\         (if neg (number_of v) then #0 \
\          else nat (number_of v div number_of v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [not_neg_eq_ge_0, nat_number_of_def, neg_nat, 
				  div_nat_eq_nat_zdiv, nat_0]) 1);
qed "div_nat_number_of";

Addsimps [div_nat_number_of];


(** Remainder **)

(*Fails if z'<0: the LHS collapses to (nat z) but the RHS doesn't*)
Goal "[| (#0::int) <= z;  #0 <= z' |] ==> nat z mod nat z' = nat (z mod z')";
by (zdiv_undefined_case_tac "z' = #0" 1);
 by (simp_tac (simpset() addsimps [numeral_0_eq_0, DIVISION_BY_ZERO_MOD]) 1);
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
by (rename_tac "m m'" 1);
by (subgoal_tac "#0 <= int m mod int m'" 1);
 by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, numeral_0_eq_0, 
				       pos_mod_sign]) 2);
by (rtac (inj_int RS injD) 1);
by (Asm_simp_tac 1);
by (rtac sym 1);
by (res_inst_tac [("q", "int (m div m')")] quorem_mod 1);
 by (Force_tac 2);
by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, quorem_def, 
				      numeral_0_eq_0, zadd_int, zmult_int, 
				      mod_less_divisor]) 1);
by (rtac (mod_div_equality RS sym RS trans) 1);
by (asm_simp_tac (simpset() addsimps add_ac@mult_ac) 1);
qed "mod_nat_eq_nat_zmod";

Goal "(number_of v :: nat)  mod  number_of v' = \
\       (if neg (number_of v) then #0 \
\        else if neg (number_of v') then number_of v \
\        else nat (number_of v mod number_of v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [not_neg_eq_ge_0, nat_number_of_def, 
				  neg_nat, nat_0, DIVISION_BY_ZERO_MOD,
				  mod_nat_eq_nat_zmod]) 1);
qed "mod_nat_number_of";

Addsimps [mod_nat_number_of];


(*** Comparisons ***)

(** Equals (=) **)

Goal "[| (#0::int) <= z;  #0 <= z' |] ==> (nat z = nat z') = (z=z')";
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
qed "eq_nat_nat_iff";

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "((number_of v :: nat) = number_of v') = \
\        (if neg (number_of v) then ((#0::nat) = number_of v') \
\         else if neg (number_of v') then iszero (number_of v) \
\         else iszero (number_of (bin_add v (bin_minus v'))))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  eq_nat_nat_iff, eq_number_of_eq, nat_0]) 1);
by (simp_tac (simpset_of Int.thy addsimps [nat_eq_iff, iszero_def]) 1);
qed "eq_nat_number_of";

Addsimps [eq_nat_number_of];

(** Less-than (<) **)

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "((number_of v :: nat) < number_of v') = \
\        (if neg (number_of v) then neg (number_of (bin_minus v')) \
\         else neg (number_of (bin_add v (bin_minus v'))))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  nat_less_eq_zless, less_number_of_eq_neg,
				  nat_0]) 1);
by (simp_tac (simpset_of Int.thy addsimps [neg_eq_less_int0, zminus_zless, 
				    number_of_minus, zless_zero_nat]) 1);
qed "less_nat_number_of";

Addsimps [less_nat_number_of];


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::nat)) = \
\     (~ number_of y < (number_of x::nat))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_nat_number_of_eq_not_less"; 

Addsimps [le_nat_number_of_eq_not_less];


(*** New versions of existing theorems involving 0, 1, 2 ***)

fun change_theory thy th = 
    [th, read_instantiate_sg (sign_of thy) [("t","dummyVar")] refl] 
    MRS (conjI RS conjunct1) |> standard;

(*Maps n to #n for n = 0, 1, 2*)
val numeral_sym_ss = 
    HOL_ss addsimps [numeral_0_eq_0 RS sym, 
		     numeral_1_eq_1 RS sym, 
		     numeral_2_eq_2 RS sym,
		     Suc_numeral_1_eq_2, Suc_numeral_0_eq_1];

fun rename_numerals thy th = simplify numeral_sym_ss (change_theory thy th);

(*Maps #n to n for n = 0, 1, 2*)
val numeral_ss = 
    simpset() addsimps [numeral_0_eq_0, numeral_1_eq_1, numeral_2_eq_2];

(** Nat **)

Goal "#0 < n ==> n = Suc(n - #1)";
by (asm_full_simp_tac numeral_ss 1);
qed "Suc_pred'";


fun inst x t = read_instantiate_sg (sign_of NatBin.thy) [(x,t)];

(*Expresses a natural number constant as the Suc of another one.
  NOT suitable for rewriting because n recurs in the condition.*)
bind_thm ("expand_Suc", inst "n" "number_of ?v" Suc_pred');

(** Arith **)

Addsimps (map (rename_numerals thy) 
	  [diff_0_eq_0, add_0, add_0_right, add_pred, 
	   diff_is_0_eq RS iffD2, zero_less_diff,
	   mult_0, mult_0_right, mult_1, mult_1_right, 
	   mult_is_0, zero_less_mult_iff,
	   mult_eq_1_iff]);

AddIffs (map (rename_numerals thy) [add_is_0, zero_is_add, add_gr_0]);

(* These two can be useful when m = number_of... *)

Goal "(m::nat) + n = (if m=#0 then n else Suc ((m - #1) + n))";
by (exhaust_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "add_eq_if";

Goal "(m::nat) * n = (if m=#0 then #0 else n + ((m - #1) * n))";
by (exhaust_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "mult_eq_if";

(*various theorems that aren't in the default simpset*)
val add_is_one' = rename_numerals thy add_is_1;
val one_is_add' = rename_numerals thy one_is_add;
val zero_induct' = rename_numerals thy zero_induct;
val diff_self_eq_0' = rename_numerals thy diff_self_eq_0;
val mult_eq_self_implies_10' = rename_numerals thy mult_eq_self_implies_10;
val le_pred_eq' = rename_numerals thy le_pred_eq;
val less_pred_eq' = rename_numerals thy less_pred_eq;

(** Divides **)

Addsimps (map (rename_numerals thy) 
	  [mod_1, mod_0, div_1, div_0, mod2_gr_0, mod2_add_self_eq_0,
	   mod2_add_self]);

AddIffs (map (rename_numerals thy) 
	  [dvd_1_left, dvd_0_right]);

(*useful?*)
val mod_self' = rename_numerals thy mod_self;
val div_self' = rename_numerals thy div_self;
val div_less' = rename_numerals thy div_less;
val mod_mult_self_is_zero' = rename_numerals thy mod_mult_self_is_0;

(** Power **)

Goal "(p::nat) ^ #0 = #1";
by (simp_tac numeral_ss 1);
qed "power_zero";
Addsimps [power_zero];

val binomial_zero = rename_numerals thy binomial_0;
val binomial_Suc' = rename_numerals thy binomial_Suc;
val binomial_n_n' = rename_numerals thy binomial_n_n;

(*binomial_0_Suc doesn't work well on numerals*)
Addsimps (map (rename_numerals thy) 
	  [binomial_n_0, binomial_zero, binomial_1]);

