(*  Title:      HOL/nat_bin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the natural numbers
*)

val nat_number_of_def = thm "nat_number_of_def";

(** nat (coercion from int to nat) **)

Goal "nat (number_of w) = number_of w";
by (simp_tac (simpset() addsimps [nat_number_of_def]) 1);
qed "nat_number_of";
Addsimps [nat_number_of, nat_0, nat_1];

Goal "Numeral0 = (0::nat)";
by (simp_tac (simpset() addsimps [nat_number_of_def]) 1); 
qed "numeral_0_eq_0";

Goal "Numeral1 = (1::nat)";
by (simp_tac (simpset() addsimps [nat_1, nat_number_of_def]) 1); 
qed "numeral_1_eq_1";

Goal "Numeral1 = Suc 0";
by (simp_tac (simpset() addsimps [numeral_1_eq_1]) 1); 
qed "numeral_1_eq_Suc_0";

Goalw [nat_number_of_def] "2 = Suc (Suc 0)";
by (rtac nat_2 1); 
qed "numeral_2_eq_2";

(** int (coercion from nat to int) **)

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "int (number_of v :: nat) = \
\        (if neg (number_of v) then 0 \
\         else (number_of v :: int))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, nat_number_of_def, 
				  not_neg_nat, int_0]) 1);
qed "int_nat_number_of";
Addsimps [int_nat_number_of];


val nat_bin_arith_setup =
 [Fast_Arith.map_data 
   (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
     {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms,
      inj_thms = inj_thms,
      lessD = lessD,
      simpset = simpset addsimps [int_nat_number_of, not_neg_number_of_Pls,
                                  neg_number_of_Min,neg_number_of_BIT]})];

(** Successor **)

Goal "(0::int) <= z ==> Suc (nat z) = nat (1 + z)";
by (rtac sym 1);
by (asm_simp_tac (simpset() addsimps [nat_eq_iff, int_Suc]) 1);
qed "Suc_nat_eq_nat_zadd1";

Goal "Suc (number_of v + n) = \
\       (if neg (number_of v) then 1+n else number_of (bin_succ v) + n)";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, nat_1, not_neg_eq_ge_0, 
				  nat_number_of_def, int_Suc, 
				  Suc_nat_eq_nat_zadd1, number_of_succ]) 1);
qed "Suc_nat_number_of_add";

Goal "Suc (number_of v) = \
\       (if neg (number_of v) then 1 else number_of (bin_succ v))";
by (cut_inst_tac [("n","0")] Suc_nat_number_of_add 1);
by (asm_full_simp_tac (simpset() delcongs [if_weak_cong]) 1); 
qed "Suc_nat_number_of";
Addsimps [Suc_nat_number_of];

(** Addition **)

Goal "[| (0::int) <= z;  0 <= z' |] ==> nat (z+z') = nat z + nat z'";
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

Goal "[| (0::int) <= z';  z' <= z |] ==> nat (z-z') = nat z - nat z'";
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zdiff_int RS sym, nat_le_eq_zle]) 1);
qed "nat_diff_distrib";


Goal "nat z - nat z' = \
\       (if neg z' then nat z  \
\        else let d = z-z' in    \
\             if neg d then 0 else nat d)";
by (simp_tac (simpset() addsimps [Let_def, nat_diff_distrib RS sym,
				  neg_eq_less_0, not_neg_eq_ge_0]) 1);
by (simp_tac (simpset() addsimps [diff_is_0_eq, nat_le_eq_zle]) 1);
qed "diff_nat_eq_if";

Goalw [nat_number_of_def]
     "(number_of v :: nat) - number_of v' = \
\       (if neg (number_of v') then number_of v \
\        else let d = number_of (bin_add v (bin_minus v')) in    \
\             if neg d then 0 else nat d)";
by (simp_tac
    (simpset_of Int.thy delcongs [if_weak_cong]
			addsimps [not_neg_eq_ge_0, nat_0,
				  diff_nat_eq_if, diff_number_of_eq]) 1);
qed "diff_nat_number_of";

Addsimps [diff_nat_number_of];


(** Multiplication **)

Goal "(0::int) <= z ==> nat (z*z') = nat z * nat z'";
by (case_tac "0 <= z'" 1);
by (asm_full_simp_tac (simpset() addsimps [zmult_le_0_iff]) 2);
by (rtac (inj_int RS injD) 1);
by (asm_simp_tac (simpset() addsimps [zmult_int RS sym,
				      int_0_le_mult_iff]) 1);
qed "nat_mult_distrib";

Goal "z <= (0::int) ==> nat(z*z') = nat(-z) * nat(-z')"; 
by (rtac trans 1); 
by (rtac nat_mult_distrib 2); 
by Auto_tac;  
qed "nat_mult_distrib_neg";

Goal "(number_of v :: nat) * number_of v' = \
\      (if neg (number_of v) then 0 else number_of (bin_mult v v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  nat_mult_distrib RS sym, number_of_mult, 
				  nat_0]) 1);
qed "mult_nat_number_of";

Addsimps [mult_nat_number_of];


(** Quotient **)

Goal "(0::int) <= z ==> nat (z div z') = nat z div nat z'";
by (case_tac "0 <= z'" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [div_nonneg_neg_le0, DIVISION_BY_ZERO_DIV]));
by (case_tac "z' = 0" 1 THEN asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO]) 1);
 by (simp_tac (simpset() addsimps [numeral_0_eq_0, DIVISION_BY_ZERO_DIV]) 1);
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
by (rename_tac "m m'" 1);
by (subgoal_tac "0 <= int m div int m'" 1);
 by (asm_full_simp_tac 
     (simpset() addsimps [numeral_0_eq_0, pos_imp_zdiv_nonneg_iff]) 2);
by (rtac (inj_int RS injD) 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("r", "int (m mod m')")] quorem_div 1);
 by (Force_tac 2);
by (asm_full_simp_tac 
    (simpset() addsimps [nat_less_iff RS sym, quorem_def, 
	                 numeral_0_eq_0, zadd_int, zmult_int]) 1);
by (rtac (mod_div_equality RS sym RS trans) 1);
by (asm_simp_tac (simpset() addsimps add_ac@mult_ac) 1);
qed "nat_div_distrib";

Goal "(number_of v :: nat)  div  number_of v' = \
\         (if neg (number_of v) then 0 \
\          else nat (number_of v div number_of v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [not_neg_eq_ge_0, nat_number_of_def, neg_nat, 
				  nat_div_distrib RS sym, nat_0]) 1);
qed "div_nat_number_of";

Addsimps [div_nat_number_of];


(** Remainder **)

(*Fails if z'<0: the LHS collapses to (nat z) but the RHS doesn't*)
Goal "[| (0::int) <= z;  0 <= z' |] ==> nat (z mod z') = nat z mod nat z'";
by (case_tac "z' = 0" 1 THEN asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO]) 1);
 by (simp_tac (simpset() addsimps [numeral_0_eq_0, DIVISION_BY_ZERO_MOD]) 1);
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
by (rename_tac "m m'" 1);
by (subgoal_tac "0 <= int m mod int m'" 1);
 by (asm_full_simp_tac 
     (simpset() addsimps [nat_less_iff, numeral_0_eq_0, pos_mod_sign]) 2);
by (rtac (inj_int RS injD) 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("q", "int (m div m')")] quorem_mod 1);
 by (Force_tac 2);
by (asm_full_simp_tac 
     (simpset() addsimps [nat_less_iff RS sym, quorem_def, 
		          numeral_0_eq_0, zadd_int, zmult_int]) 1);
by (rtac (mod_div_equality RS sym RS trans) 1);
by (asm_simp_tac (simpset() addsimps add_ac@mult_ac) 1);
qed "nat_mod_distrib";

Goal "(number_of v :: nat)  mod  number_of v' = \
\       (if neg (number_of v) then 0 \
\        else if neg (number_of v') then number_of v \
\        else nat (number_of v mod number_of v'))";
by (simp_tac
    (simpset_of Int.thy addsimps [not_neg_eq_ge_0, nat_number_of_def, 
				  neg_nat, nat_0, DIVISION_BY_ZERO_MOD,
				  nat_mod_distrib RS sym]) 1);
qed "mod_nat_number_of";

Addsimps [mod_nat_number_of];

structure NatAbstractNumeralsData =
  struct
  val dest_eq		= HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral	= Bin_Simprocs.is_numeral
  val numeral_0_eq_0    = numeral_0_eq_0
  val numeral_1_eq_1    = numeral_1_eq_Suc_0
  val prove_conv   = Bin_Simprocs.prove_conv_nohyps "nat_abstract_numerals"
  fun norm_tac simps	= ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq  = Bin_Simprocs.simplify_meta_eq 
  end

structure NatAbstractNumerals = AbstractNumeralsFun (NatAbstractNumeralsData)

val nat_eval_numerals = 
  map Bin_Simprocs.prep_simproc
   [("nat_div_eval_numerals",
     Bin_Simprocs.prep_pats ["(Suc 0) div m"],
     NatAbstractNumerals.proc div_nat_number_of),
    ("nat_mod_eval_numerals",
     Bin_Simprocs.prep_pats ["(Suc 0) mod m"],
     NatAbstractNumerals.proc mod_nat_number_of)];

Addsimprocs nat_eval_numerals;


(*** Comparisons ***)

(** Equals (=) **)

Goal "[| (0::int) <= z;  0 <= z' |] ==> (nat z = nat z') = (z=z')";
by (auto_tac (claset() addSEs [nonneg_eq_int], simpset()));
qed "eq_nat_nat_iff";

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "((number_of v :: nat) = number_of v') = \
\     (if neg (number_of v) then (iszero (number_of v') | neg (number_of v')) \
\      else if neg (number_of v') then iszero (number_of v) \
\      else iszero (number_of (bin_add v (bin_minus v'))))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  eq_nat_nat_iff, eq_number_of_eq, nat_0]) 1);
by (simp_tac (simpset_of Int.thy addsimps [nat_eq_iff, nat_eq_iff2, 
					   iszero_def]) 1);
by (simp_tac (simpset () addsimps [not_neg_eq_ge_0 RS sym]) 1);
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
by (simp_tac (simpset_of Int.thy addsimps [neg_eq_less_0, zminus_zless, 
				number_of_minus, zless_nat_eq_int_zless]) 1);
qed "less_nat_number_of";

Addsimps [less_nat_number_of];


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::nat)) = \
\     (~ number_of y < (number_of x::nat))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_nat_number_of_eq_not_less"; 

Addsimps [le_nat_number_of_eq_not_less];


(*Maps #n to n for n = 0, 1, 2*)
bind_thms ("numerals", [numeral_0_eq_0, numeral_1_eq_1, numeral_2_eq_2]);
val numeral_ss = simpset() addsimps numerals;

(** Nat **)

Goal "0 < n ==> n = Suc(n - 1)";
by (asm_full_simp_tac numeral_ss 1);
qed "Suc_pred'";

(*Expresses a natural number constant as the Suc of another one.
  NOT suitable for rewriting because n recurs in the condition.*)
bind_thm ("expand_Suc", inst "n" "number_of ?v" Suc_pred');

(** Arith **)

Goal "Suc n = n + 1";
by (asm_simp_tac numeral_ss 1);
qed "Suc_eq_add_numeral_1";

(* These two can be useful when m = number_of... *)

Goal "(m::nat) + n = (if m=0 then n else Suc ((m - 1) + n))";
by (case_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "add_eq_if";

Goal "(m::nat) * n = (if m=0 then 0 else n + ((m - 1) * n))";
by (case_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "mult_eq_if";

Goal "(p ^ m :: nat) = (if m=0 then 1 else p * (p ^ (m - 1)))";
by (case_tac "m" 1);
by (ALLGOALS (asm_simp_tac numeral_ss));
qed "power_eq_if";

Goal "[| 0<n; 0<m |] ==> m - n < (m::nat)";
by (asm_full_simp_tac (numeral_ss addsimps [diff_less]) 1);
qed "diff_less'";

Addsimps [inst "n" "number_of ?v" diff_less'];

(** Power **)

Goal "(p::nat) ^ 2 = p*p";
by (simp_tac numeral_ss 1);
qed "power_two";


(*** Comparisons involving (0::nat) ***)

Goal "(number_of v = (0::nat)) = \
\     (if neg (number_of v) then True else iszero (number_of v))";
by (simp_tac (simpset() addsimps [numeral_0_eq_0 RS sym, iszero_0]) 1);
qed "eq_number_of_0"; 

Goal "((0::nat) = number_of v) = \
\     (if neg (number_of v) then True else iszero (number_of v))";
by (rtac ([eq_sym_conv, eq_number_of_0] MRS trans) 1);
qed "eq_0_number_of";

Goal "((0::nat) < number_of v) = neg (number_of (bin_minus v))";
by (simp_tac (simpset() addsimps [numeral_0_eq_0 RS sym]) 1);
qed "less_0_number_of";

(*Simplification already handles n<0, n<=0 and 0<=n.*)
Addsimps [eq_number_of_0, eq_0_number_of, less_0_number_of];

Goal "neg (number_of v) ==> number_of v = (0::nat)";
by (asm_simp_tac (simpset() addsimps [numeral_0_eq_0 RS sym, iszero_0]) 1);
qed "neg_imp_number_of_eq_0";



(*** Comparisons involving Suc ***)

Goal "(number_of v = Suc n) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then False else nat pv = n)";
by (simp_tac
    (simpset_of Int.thy addsimps
      [Let_def, neg_eq_less_0, linorder_not_less, number_of_pred,
       nat_number_of_def, zadd_0] @ zadd_ac) 1);
by (res_inst_tac [("x", "number_of v")] spec 1);
by (auto_tac (claset(), simpset() addsimps [nat_eq_iff]));
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
       nat_number_of_def, zadd_0] @ zadd_ac) 1);
by (res_inst_tac [("x", "number_of v")] spec 1);
by (auto_tac (claset(), simpset() addsimps [nat_less_iff]));
qed "less_number_of_Suc";

Goal "(Suc n < number_of v) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then False else n < nat pv)";
by (simp_tac
    (simpset_of Int.thy addsimps
      [Let_def, neg_eq_less_0, linorder_not_less, number_of_pred,
       nat_number_of_def, zadd_0] @ zadd_ac) 1);
by (res_inst_tac [("x", "number_of v")] spec 1);
by (auto_tac (claset(), simpset() addsimps [zless_nat_eq_int_zless]));
qed "less_Suc_number_of";

Goal "(number_of v <= Suc n) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then True else nat pv <= n)";
by (simp_tac
    (simpset () addsimps
      [Let_def, less_Suc_number_of, linorder_not_less RS sym]) 1);
qed "le_number_of_Suc";

Goal "(Suc n <= number_of v) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then False else n <= nat pv)";
by (simp_tac
    (simpset () addsimps
      [Let_def, less_number_of_Suc, linorder_not_less RS sym]) 1);
qed "le_Suc_number_of";

Addsimps [eq_number_of_Suc, Suc_eq_number_of, 
	  less_number_of_Suc, less_Suc_number_of, 
	  le_number_of_Suc, le_Suc_number_of];

(* Push int(.) inwards: *)
Addsimps [zadd_int RS sym];

Goal "(m+m = n+n) = (m = (n::int))";
by Auto_tac;
val lemma1 = result();

Goal "m+m ~= (1::int) + n + n";
by Auto_tac;
by (dres_inst_tac [("f", "%x. x mod 2")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1); 
val lemma2 = result();

Goal "((number_of (v BIT x) ::int) = number_of (w BIT y)) = \
\     (x=y & (((number_of v) ::int) = number_of w))"; 
by (simp_tac (simpset_of Int.thy addsimps
	       [number_of_BIT, lemma1, lemma2, eq_commute]) 1); 
qed "eq_number_of_BIT_BIT"; 

Goal "((number_of (v BIT x) ::int) = number_of Pls) = \
\     (x=False & (((number_of v) ::int) = number_of Pls))"; 
by (simp_tac (simpset_of Int.thy addsimps
	       [number_of_BIT, number_of_Pls, eq_commute]) 1); 
by (res_inst_tac [("x", "number_of v")] spec 1);
by Safe_tac;
by (ALLGOALS Full_simp_tac);
by (dres_inst_tac [("f", "%x. x mod 2")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1); 
qed "eq_number_of_BIT_Pls"; 

Goal "((number_of (v BIT x) ::int) = number_of Min) = \
\     (x=True & (((number_of v) ::int) = number_of Min))"; 
by (simp_tac (simpset_of Int.thy addsimps
	       [number_of_BIT, number_of_Min, eq_commute]) 1); 
by (res_inst_tac [("x", "number_of v")] spec 1);
by Auto_tac;
by (dres_inst_tac [("f", "%x. x mod 2")] arg_cong 1);
by Auto_tac;
qed "eq_number_of_BIT_Min"; 

Goal "(number_of Pls ::int) ~= number_of Min"; 
by Auto_tac;
qed "eq_number_of_Pls_Min"; 


(*** Further lemmas about "nat" ***)

Goal "nat (abs (w * z)) = nat (abs w) * nat (abs z)";
by (case_tac "z=0 | w=0" 1);
by Auto_tac;  
by (simp_tac (simpset() addsimps [zabs_def, nat_mult_distrib RS sym, 
                          nat_mult_distrib_neg RS sym, zmult_less_0_iff]) 1);
by (arith_tac 1);
qed "nat_abs_mult_distrib";

(*Distributive laws for literals*)
Addsimps (map (inst "k" "number_of ?v")
	  [add_mult_distrib, add_mult_distrib2,
	   diff_mult_distrib, diff_mult_distrib2]);


(*** Literal arithmetic involving powers, type nat ***)

Goal "(0::int) <= z ==> nat (z^n) = nat z ^ n";
by (induct_tac "n" 1); 
by (ALLGOALS (asm_simp_tac (simpset() addsimps [nat_mult_distrib])));
qed "nat_power_eq";

Goal "(number_of v :: nat) ^ n = \
\      (if neg (number_of v) then 0^n else nat ((number_of v :: int) ^ n))";
by (simp_tac
    (simpset_of Int.thy addsimps [neg_nat, not_neg_eq_ge_0, nat_number_of_def, 
				  nat_power_eq]) 1);
qed "power_nat_number_of";

Addsimps [inst "n" "number_of ?w" power_nat_number_of];



(*** Literal arithmetic involving powers, type int ***)

Goal "(z::int) ^ (2*a) = (z^a)^2";
by (simp_tac (simpset() addsimps [zpower_zpower, mult_commute]) 1); 
qed "zpower_even";

Goal "(p::int) ^ 2 = p*p"; 
by (simp_tac numeral_ss 1);
qed "zpower_two";  

Goal "(z::int) ^ (2*a + 1) = z * (z^a)^2";
by (simp_tac (simpset() addsimps [zpower_even, zpower_zadd_distrib]) 1); 
qed "zpower_odd";

Goal "(z::int) ^ number_of (w BIT False) = \
\     (let w = z ^ (number_of w) in  w*w)";
by (simp_tac (simpset_of Int.thy addsimps [nat_number_of_def,
        number_of_BIT, Let_def]) 1);
by (res_inst_tac [("x","number_of w")] spec 1 THEN Clarify_tac 1); 
by (case_tac "(0::int) <= x" 1);
by (auto_tac (claset(), 
     simpset() addsimps [nat_mult_distrib, zpower_even, zpower_two])); 
qed "zpower_number_of_even";

Goal "(z::int) ^ number_of (w BIT True) = \
\         (if (0::int) <= number_of w                   \
\          then (let w = z ^ (number_of w) in  z*w*w)   \
\          else 1)";
by (simp_tac (simpset_of Int.thy addsimps [nat_number_of_def,
        number_of_BIT, Let_def]) 1);
by (res_inst_tac [("x","number_of w")] spec 1 THEN Clarify_tac 1); 
by (case_tac "(0::int) <= x" 1);
by (auto_tac (claset(), 
              simpset() addsimps [nat_add_distrib, nat_mult_distrib, 
                                  zpower_even, zpower_two])); 
qed "zpower_number_of_odd";

Addsimps (map (inst "z" "number_of ?v")
              [zpower_number_of_even, zpower_number_of_odd]);

