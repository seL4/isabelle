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
by (rtac sym 1);
by (asm_simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "Suc_nat_eq_nat_zadd1";

Goal "Suc (number_of v) = \
\       (if neg (number_of v) then #1 else number_of (bin_succ v))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, nat_1, not_neg_eq_ge_0, 
				  nat_number_of_def, int_Suc, 
				  Suc_nat_eq_nat_zadd1, number_of_succ]) 1);
qed "Suc_nat_number_of";
Addsimps [Suc_nat_number_of];

Goal "Suc (number_of v + n) = \
\       (if neg (number_of v) then #1+n else number_of (bin_succ v) + n)";
by (Simp_tac 1);
qed "Suc_nat_number_of_add";

Goal "Suc #0 = #1";
by (Simp_tac 1);
qed "Suc_numeral_0_eq_1";

Goal "Suc #1 = #2";
by (Simp_tac 1);
qed "Suc_numeral_1_eq_2";

(** Addition **)

Goal "[| (#0::int) <= z;  #0 <= z' |] ==> nat (z+z') = nat z + nat z'";
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zadd_int RS sym]) 1);
qed "nat_add_distrib";

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "(number_of v :: nat) + number_of v' = \
\        (if neg (number_of v) then number_of v' \
\         else if neg (number_of v') then number_of v \
\         else number_of (bin_add v v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  nat_add_distrib RS sym, number_of_add]) 1);
qed "add_nat_number_of";

Addsimps [add_nat_number_of];


(** Subtraction **)

Goal "[| (#0::int) <= z';  z' <= z |] ==> nat (z-z') = nat z - nat z'";
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zdiff_int RS sym, nat_le_eq_zle]) 1);
qed "nat_diff_distrib";


Goal "nat z - nat z' = \
\       (if neg z' then nat z  \
\        else let d = z-z' in    \
\             if neg d then 0 else nat d)";
by (simp_tac (simpset() addsimps [Let_def, nat_diff_distrib RS sym,
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

Goal "(#0::int) <= z ==> nat (z*z') = nat z * nat z'";
by (case_tac "#0 <= z'" 1);
by (subgoal_tac "z'*z <= #0" 2);
by (rtac (neg_imp_zmult_nonpos_iff RS iffD2) 3);
by (auto_tac (claset(),
	      simpset() addsimps [zmult_commute]));
by (subgoal_tac "#0 <= z*z'" 1);
by (force_tac (claset() addDs [zmult_zle_mono1], simpset()) 2);
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zmult_int RS sym]) 1);
qed "nat_mult_distrib";

Goal "(number_of v :: nat) * number_of v' = \
\      (if neg (number_of v) then #0 else number_of (bin_mult v v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  nat_mult_distrib RS sym, number_of_mult, 
				  nat_0]) 1);
qed "mult_nat_number_of";

Addsimps [mult_nat_number_of];


(** Quotient **)

Goal "(#0::int) <= z ==> nat (z div z') = nat z div nat z'";
by (case_tac "#0 <= z'" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [div_nonneg_neg_le0, DIVISION_BY_ZERO_DIV]));
by (zdiv_undefined_case_tac "z' = #0" 1);
 by (simp_tac (simpset() addsimps [numeral_0_eq_0, DIVISION_BY_ZERO_DIV]) 1);
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
by (rename_tac "m m'" 1);
by (subgoal_tac "#0 <= int m div int m'" 1);
 by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, numeral_0_eq_0, 
				       pos_imp_zdiv_nonneg_iff]) 2);
by (rtac (inj_int RS injD) 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("r", "int (m mod m')")] quorem_div 1);
 by (Force_tac 2);
by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, quorem_def, 
				      numeral_0_eq_0, zadd_int, zmult_int]) 1);
by (rtac (mod_div_equality RS sym RS trans) 1);
by (asm_simp_tac (simpset() addsimps add_ac@mult_ac) 1);
qed "nat_div_distrib";

Goal "(number_of v :: nat)  div  number_of v' = \
\         (if neg (number_of v) then #0 \
\          else nat (number_of v div number_of v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [not_neg_eq_ge_0, nat_number_of_def, neg_nat, 
				  nat_div_distrib RS sym, nat_0]) 1);
qed "div_nat_number_of";

Addsimps [div_nat_number_of];


(** Remainder **)

(*Fails if z'<0: the LHS collapses to (nat z) but the RHS doesn't*)
Goal "[| (#0::int) <= z;  #0 <= z' |] ==> nat (z mod z') = nat z mod nat z'";
by (zdiv_undefined_case_tac "z' = #0" 1);
 by (simp_tac (simpset() addsimps [numeral_0_eq_0, DIVISION_BY_ZERO_MOD]) 1);
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
by (rename_tac "m m'" 1);
by (subgoal_tac "#0 <= int m mod int m'" 1);
 by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, numeral_0_eq_0, 
				       pos_mod_sign]) 2);
by (rtac (inj_int RS injD) 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("q", "int (m div m')")] quorem_mod 1);
 by (Force_tac 2);
by (asm_simp_tac (simpset() addsimps [nat_less_iff RS sym, quorem_def, 
				      numeral_0_eq_0, zadd_int, zmult_int]) 1);
by (rtac (mod_div_equality RS sym RS trans) 1);
by (asm_simp_tac (simpset() addsimps add_ac@mult_ac) 1);
qed "nat_mod_distrib";

Goal "(number_of v :: nat)  mod  number_of v' = \
\       (if neg (number_of v) then #0 \
\        else if neg (number_of v') then number_of v \
\        else nat (number_of v mod number_of v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [not_neg_eq_ge_0, nat_number_of_def, 
				  neg_nat, nat_0, DIVISION_BY_ZERO_MOD,
				  nat_mod_distrib RS sym]) 1);
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
				number_of_minus, zless_nat_eq_int_zless]) 1);
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

(*Expresses a natural number constant as the Suc of another one.
  NOT suitable for rewriting because n recurs in the condition.*)
bind_thm ("expand_Suc", inst "n" "number_of ?v" Suc_pred');

(** NatDef & Nat **)

Addsimps (map (rename_numerals thy) 
	  [min_0L, min_0R, max_0L, max_0R]);

AddIffs (map (rename_numerals thy) 
	 [Suc_not_Zero, Zero_not_Suc, zero_less_Suc, not_less0, less_one, 
	  le0, le_0_eq, 
	  neq0_conv, zero_neq_conv, not_gr0]);

(** Arith **)

Addsimps (map (rename_numerals thy) 
	  [diff_0, diff_0_eq_0, add_0, add_0_right, add_pred, 
	   diff_is_0_eq, zero_is_diff_eq, zero_less_diff,
	   mult_0, mult_0_right, mult_1, mult_1_right, 
	   mult_is_0, zero_is_mult, zero_less_mult_iff,
	   mult_eq_1_iff]);

AddIffs (map (rename_numerals thy) [add_is_0, zero_is_add, add_gr_0]);

Goal "Suc n = n + #1";
by (asm_simp_tac numeral_ss 1);
qed "Suc_eq_add_numeral_1";

(* These two can be useful when m = number_of... *)

Goal "(m::nat) + n = (if m=#0 then n else Suc ((m - #1) + n))";
by (case_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "add_eq_if";

Goal "(m::nat) * n = (if m=#0 then #0 else n + ((m - #1) * n))";
by (case_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "mult_eq_if";

Goal "(p ^ m :: nat) = (if m=#0 then #1 else p * (p ^ (m - #1)))";
by (case_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "power_eq_if";

Goal "[| #0<n; #0<m |] ==> m - n < (m::nat)";
by (asm_full_simp_tac (numeral_ss addsimps [diff_less]) 1);
qed "diff_less'";

Addsimps [inst "n" "number_of ?v" diff_less'];

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


(*** Comparisons involving 0 ***)

Goal "(number_of v = 0) = \
\     (if neg (number_of v) then True else iszero (number_of v))";
by (simp_tac (simpset() addsimps [numeral_0_eq_0 RS sym]) 1);
qed "eq_number_of_0";

Goal "(0 = number_of v) = \
\     (if neg (number_of v) then True else iszero (number_of v))";
by (rtac ([eq_sym_conv, eq_number_of_0] MRS trans) 1);
qed "eq_0_number_of";

Goal "(0 < number_of v) = neg (number_of (bin_minus v))";
by (simp_tac (simpset() addsimps [numeral_0_eq_0 RS sym]) 1);
qed "less_0_number_of";

(*Simplification already handles n<0, n<=0 and 0<=n.*)
Addsimps [eq_number_of_0, eq_0_number_of, less_0_number_of];


(*** Comparisons involving Suc ***)

Goal "(number_of v = Suc n) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then False else nat pv = n)";
by (simp_tac
    (simpset_of Int.thy addsimps
      [Let_def, neg_eq_less_0, linorder_not_less, number_of_pred,
       nat_number_of_def, zadd_0]@zadd_ac@zcompare_rls) 1);
by (res_inst_tac [("x", "number_of v")] spec 1);
by (auto_tac (claset(),
	      simpset() addsimps [nat_eq_iff]@zcompare_rls));
qed "eq_number_of_Suc";

Goal "(Suc n = number_of v) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then False else nat pv = n)";
by (rtac ([eq_sym_conv, eq_number_of_Suc] MRS trans) 1);
qed "Suc_eq_number_of";

Goal "(number_of v < Suc n) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then True else nat pv < n)";
by (simp_tac
    (simpset_of Int.thy addsimps
      [Let_def, neg_eq_less_0, linorder_not_less, number_of_pred,
       nat_number_of_def, zadd_0]@zadd_ac@zcompare_rls) 1);
by (res_inst_tac [("x", "number_of v")] spec 1);
by (auto_tac (claset(),
	      simpset() addsimps [nat_less_iff]@zcompare_rls));
qed "less_number_of_Suc";

Goal "(Suc n < number_of v) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then False else n < nat pv)";
by (simp_tac
    (simpset_of Int.thy addsimps
      [Let_def, neg_eq_less_0, linorder_not_less, number_of_pred,
       nat_number_of_def, zadd_0]@zadd_ac@zcompare_rls) 1);
by (res_inst_tac [("x", "number_of v")] spec 1);
by (auto_tac (claset(),
	      simpset() addsimps [zless_nat_eq_int_zless]@zcompare_rls));
qed "less_Suc_number_of";

Goal "(number_of v <= Suc n) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then True else nat pv <= n)";
by (simp_tac
    (simpset_of Int.thy addsimps
      [Let_def, less_Suc_number_of, linorder_not_less RS sym]) 1);
qed "le_number_of_Suc";

Goal "(Suc n <= number_of v) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then False else n <= nat pv)";
by (simp_tac
    (simpset_of Int.thy addsimps
      [Let_def, less_number_of_Suc, linorder_not_less RS sym]) 1);
qed "le_Suc_number_of";

Addsimps [eq_number_of_Suc, Suc_eq_number_of, 
	  less_number_of_Suc, less_Suc_number_of, 
	  le_number_of_Suc, le_Suc_number_of];

(* Push int(.) inwards: *)
Addsimps [int_Suc,zadd_int RS sym];


(*** Simprocs for nat numerals ***)

(*Lemma used for cancel_numerals to prove #n <= i + ... + #m + ... j *)
Goal "!!k::nat. k<=i | k <= j ==> k <= i+j";
by Auto_tac;
qed "disj_imp_le_add";


structure Nat_Numeral_Simprocs =
struct

(*Utilities for simproc inverse_fold*)

fun mk_numeral n = HOLogic.number_of_const $ NumeralSyntax.mk_bin n;

(*Decodes a numeral to a NATURAL NUMBER*)
fun dest_numeral (Const("Numeral.number_of", _) $ w) = 
        BasisLibrary.Int.max (0, NumeralSyntax.dest_bin w)
  | dest_numeral t = raise TERM("dest_numeral", [t]);

fun find_first_numeral past (t::terms) =
    (dest_numeral t, t, rev past @ terms)
    handle _ => find_first_numeral (t::past) terms;

val zero = mk_numeral 0;
val one = mk_numeral 1;
val mk_plus = HOLogic.mk_binop "op +";

fun mk_sum [] = HOLogic.zero
  | mk_sum [t] = t
  | mk_sum (t :: ts) = if t = zero then mk_sum ts
                       else mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" HOLogic.natT;

(*extract the outer Sucs from a term and convert them to a binary numeral*)
fun dest_Sucs (k, Const ("Suc", _) $ t) = dest_Sucs (k+1, t)
  | dest_Sucs (0, t) = t
  | dest_Sucs (k, t) = mk_plus (mk_numeral k, t);

fun dest_sum (Const ("0", _)) = []
  | dest_sum t =
      let val (t,u) = dest_plus t 
      in  dest_sum t @ dest_sum u  end
      handle _ => [t];

fun dest_Sucs_sum t = dest_sum (dest_Sucs (0,t));

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" HOLogic.natT;

val mk_eqv = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun prove_conv tacs sg (t, u) =
  if t aconv u then None
  else
  Some
     (mk_meta_eq (prove_goalw_cterm [] (cterm_of sg (mk_eqv (t, u)))
	(K tacs))
      handle ERROR => error 
	  ("The error(s) above occurred while trying to prove " ^
	   (string_of_cterm (cterm_of sg (mk_eqv (t, u))))));

fun all_simp_tac ss rules = ALLGOALS (simp_tac (ss addsimps rules));

val add_norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps add_ac));


structure InverseFoldData =
  struct
  val mk_numeral	= mk_numeral
  val dest_numeral	= dest_numeral
  val find_first_numeral = find_first_numeral []
  val mk_sum		= mk_sum
  val dest_sum		= dest_Sucs_sum
  val mk_diff    	= HOLogic.mk_binop "op -"
  val dest_diff		= HOLogic.dest_bin "op -" HOLogic.natT
  val double_diff_eq	= diff_add_assoc_diff
  val move_diff_eq	= diff_add_assoc2
  val prove_conv	= prove_conv
  val numeral_simp_tac	= all_simp_tac (simpset())
  val add_norm_tac	= ALLGOALS (simp_tac (simpset() addsimps Suc_eq_add_numeral_1::add_ac))
  end;

structure InverseFold = InverseFoldFun (InverseFoldData);

structure FoldSuc = FoldSucFun
 (open InverseFoldData
  val dest_Suc		= HOLogic.dest_Suc
  val numeral_simp_tac	= all_simp_tac (simpset()
					  addsimps [Suc_nat_number_of_add]));

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;
fun prep_pat s = Thm.read_cterm (Theory.sign_of Arith.thy) (s, HOLogic.termT);
val prep_pats = map prep_pat;

val inverse = 
    prep_simproc ("inverse_fold", 
		  (map prep_pat ["((i::nat) + j) - number_of v",
				 "Suc i - number_of v"]), 
		  InverseFold.proc);

val fold_Suc = 
    prep_simproc ("fold_Suc", 
		  [prep_pat "Suc (i + j)"], 
		  FoldSuc.proc);

(*To instantiate "k" in theorems such as eq_diff_iff*)
fun subst_inst_tac th t = 
    instantiate' [None] [Some (cterm_of (sign_of thy) t)] th;

fun mk_subst_tac th k = rtac (subst_inst_tac (th RS sym RS trans) k) 1;

structure CommonData =
  struct
  val mk_numeral	= mk_numeral
  val find_first_numeral = find_first_numeral []
  val mk_sum		= mk_sum
  val dest_sum		= dest_Sucs_sum
  val prove_conv	= prove_conv
  val all_simp_tac = all_simp_tac 
			(simpset() addsimprocs [inverse]) [disj_imp_le_add]
  end;


(* nat eq *)
structure EqCancelNumerals = CancelNumeralsFun
 (open CommonData
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT
  val subst_tac = mk_subst_tac eq_diff_iff);

(* nat less *)
structure LessCancelNumerals = CancelNumeralsFun
 (open CommonData
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT
  val subst_tac = mk_subst_tac less_diff_iff);

(* nat le *)
structure LeCancelNumerals = CancelNumeralsFun
 (open CommonData
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT
  val subst_tac = mk_subst_tac le_diff_iff);

(* nat diff *)
structure DiffCancelNumerals = CancelNumeralsFun
 (open CommonData
  val mk_bal   = HOLogic.mk_binop "op -"
  val dest_bal = HOLogic.dest_bin "op -" HOLogic.natT
  val subst_tac = mk_subst_tac diff_diff_eq);

val eq_pats = prep_pats ["(l::nat) + m = n", "(l::nat) = m + n"];
val less_pats = prep_pats ["(l::nat) + m < n", "(l::nat) < m + n"];
val le_pats = prep_pats ["(l::nat) + m <= n", "(l::nat) <= m + n"];

val diff_pat = prep_pat "(l::nat) - (m + n)"; 
                   (*but ((l::nat) + m) - n" is covered by inverse_fold*)

val cancel = 
  map prep_simproc
   [("nateq_cancel_numerals", eq_pats, EqCancelNumerals.proc),
    ("natless_cancel_numerals", less_pats, LessCancelNumerals.proc),
    ("natle_cancel_numerals", le_pats, LeCancelNumerals.proc),
    ("natdiff_cancel_numerals", [diff_pat], DiffCancelNumerals.proc)];

end;


Addsimprocs [Nat_Numeral_Simprocs.inverse, Nat_Numeral_Simprocs.fold_Suc];
Addsimprocs Nat_Numeral_Simprocs.cancel;

(*examples:
print_depth 22;
set proof_timing;
fun try s = (Goal s; by (simp_tac (simpset() 
  addsimprocs Nat_Numeral_Simprocs.cancel @
    [Nat_Numeral_Simprocs.inverse, Nat_Numeral_Simprocs.fold_Suc]) 1)); 

(*inverse*)
try "((i + j) + #12 + (k::nat)) - #15 = y";
try "((i + j) + #-12 + (k::nat)) - #15 = y";
try "((i + j) + #12 + (k::nat)) - #-15 = y";
try "(i + j + #22 + (k::nat)) - #15 = y";
try "((i + j) + #-12 + (k::nat)) - #-15 = y";
try "#7 + u - #5 = (yy::nat)";
try "#2 + u - #5 = (yy::nat)";

(*cancel*)
try "((i + j) + #12 + (k::nat)) = u + #15 + y";
try "((i + j) + #12 + (k::nat)) <= u + #15 + y";
try "((i + j) + #32 + (k::nat)) - (u + #15 + y) = zz";
try "((i + j) + #12 + (k::nat)) = u + #5 + y";
(*negative numerals*)
try "((i + j) + #-23 + (k::nat)) < u + #15 + y";
try "((i + j) + #3 + (k::nat)) < u + #-15 + y";

(*fold_Suc*)
try "Suc (i + j + #3 + k) = u";
try "Suc (i + j + #-3 + k) = u";


try "Suc u - #2 = y";
try "Suc (Suc (Suc u)) - #2 = y";


try "((i + j) + #12 + k) = Suc (u + y)";
try "(i + #2) = Suc u";
try "Suc (Suc (Suc (Suc (Suc (u + y))))) <= ((i + j) + #41 + k)";

try "((i + j) + #5 + k) = Suc (Suc (Suc (Suc (Suc (u + y)))))";
(*SLOW because of Addsimps [less_SucI, le_SucI];*)
try "((i + j) + #5 + k) < Suc (Suc (Suc (Suc (Suc (u + y)))))";
try "((i + j) + #5 + k) <= Suc (Suc (Suc (Suc (Suc (u + y)))))";
try "((i + j) + #5 + k) = Suc (Suc (Suc (Suc (Suc (u + y)))))";


(*so why is this fast?*)
try "((i + j) + #41 + k) < (#5::nat) + (u + y)";


try "((i + j) + #1 + k) = Suc (Suc (u + y))";


try "((i + j) + #1 + k) - #1 = (yy::nat)";
try "Suc (Suc (u + y)) - #1 = (yy::nat)";

try "((i + j) + #41 + k) - #5 = 0";
try "Suc (Suc (Suc (Suc (Suc (u + y))))) - #5 = 0";

try "((i + j) + #5 + k) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (u + y)))))))";
*)


(*** Prepare linear arithmetic for nat numerals ***)

let

(* reduce contradictory <= to False *)
val add_rules =
  [add_nat_number_of, diff_nat_number_of, mult_nat_number_of,
   eq_nat_number_of, less_nat_number_of, le_nat_number_of_eq_not_less,
   le_Suc_number_of,le_number_of_Suc,
   less_Suc_number_of,less_number_of_Suc,
   Suc_eq_number_of,eq_number_of_Suc,
   eq_number_of_0, eq_0_number_of, less_0_number_of,
   nat_number_of, Let_number_of, if_True, if_False];

val simprocs = [Nat_Plus_Assoc.conv,Nat_Times_Assoc.conv];

in
LA_Data_Ref.ss_ref := !LA_Data_Ref.ss_ref addsimps add_rules
                      addsimprocs simprocs
end;



(** For simplifying  Suc m - #n **)

Goal "#0 < n ==> Suc m - n = m - (n - #1)";
by (asm_full_simp_tac (numeral_ss addsplits [nat_diff_split']) 1);
qed "Suc_diff_eq_diff_pred";

(*Now just instantiating n to (number_of v) does the right simplification,
  but with some redundant inequality tests.*)

Goal "neg (number_of (bin_pred v)) = (number_of v = 0)";
by (subgoal_tac "neg (number_of (bin_pred v)) = (number_of v < 1)" 1);
by (Asm_simp_tac 1);
by (stac less_number_of_Suc 1);
by (Simp_tac 1);
qed "neg_number_of_bin_pred_iff_0";

Goal "neg (number_of (bin_minus v)) ==> \
\     Suc m - (number_of v) = m - (number_of (bin_pred v))";
by (stac Suc_diff_eq_diff_pred 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (asm_full_simp_tac
    (simpset_of Int.thy addsimps [less_0_number_of RS sym, 
				  neg_number_of_bin_pred_iff_0]) 1);
qed "Suc_diff_number_of";

(* now redundant because of the inverse_fold simproc
    Addsimps [Suc_diff_number_of]; *)


(** For simplifying  #m - Suc n **)

Goal "m - Suc n = (m - #1) - n";
by (simp_tac (numeral_ss addsplits [nat_diff_split']) 1);
qed "diff_Suc_eq_diff_pred";

Addsimps [inst "m" "number_of ?v" diff_Suc_eq_diff_pred];
