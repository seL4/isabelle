(*  Title:      HOL/NatSimprocs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Simprocs for nat numerals
*)

Goal "number_of v + (number_of v' + (k::nat)) = \
\        (if neg (number_of v) then number_of v' + k \
\         else if neg (number_of v') then number_of v + k \
\         else number_of (bin_add v v') + k)";
by (Simp_tac 1);
qed "nat_number_of_add_left";


(** For combine_numerals **)

Goal "i*u + (j*u + k) = (i+j)*u + (k::nat)";
by (asm_simp_tac (simpset() addsimps [add_mult_distrib]) 1);
qed "left_add_mult_distrib";


(** For cancel_numerals **)

Goal "j <= (i::nat) ==> ((i*u + m) - (j*u + n)) = (((i-j)*u + m) - n)";
by (asm_simp_tac (simpset() addsplits [nat_diff_split'] 
		            addsimps [add_mult_distrib]) 1);
qed "nat_diff_add_eq1";

Goal "i <= (j::nat) ==> ((i*u + m) - (j*u + n)) = (m - ((j-i)*u + n))";
by (asm_simp_tac (simpset() addsplits [nat_diff_split'] 
		            addsimps [add_mult_distrib]) 1);
qed "nat_diff_add_eq2";

Goal "j <= (i::nat) ==> (i*u + m = j*u + n) = ((i-j)*u + m = n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split'] 
                                  addsimps [add_mult_distrib]));
qed "nat_eq_add_iff1";

Goal "i <= (j::nat) ==> (i*u + m = j*u + n) = (m = (j-i)*u + n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split'] 
                                  addsimps [add_mult_distrib]));
qed "nat_eq_add_iff2";

Goal "j <= (i::nat) ==> (i*u + m < j*u + n) = ((i-j)*u + m < n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split'] 
                                  addsimps [add_mult_distrib]));
qed "nat_less_add_iff1";

Goal "i <= (j::nat) ==> (i*u + m < j*u + n) = (m < (j-i)*u + n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split'] 
                                  addsimps [add_mult_distrib]));
qed "nat_less_add_iff2";

Goal "j <= (i::nat) ==> (i*u + m <= j*u + n) = ((i-j)*u + m <= n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split'] 
                                  addsimps [add_mult_distrib]));
qed "nat_le_add_iff1";

Goal "i <= (j::nat) ==> (i*u + m <= j*u + n) = (m <= (j-i)*u + n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split'] 
                                  addsimps [add_mult_distrib]));
qed "nat_le_add_iff2";


structure Nat_Numeral_Simprocs =
struct

(*Utilities*)

fun mk_numeral n = HOLogic.number_of_const HOLogic.natT $ 
                   NumeralSyntax.mk_bin n;

(*Decodes a unary or binary numeral to a NATURAL NUMBER*)
fun dest_numeral (Const ("0", _)) = 0
  | dest_numeral (Const ("Suc", _) $ t) = 1 + dest_numeral t
  | dest_numeral (Const("Numeral.number_of", _) $ w) = 
      (BasisLibrary.Int.max (0, NumeralSyntax.dest_bin w)
       handle Match => raise TERM("Nat_Numeral_Simprocs.dest_numeral:1", [w]))
  | dest_numeral t = raise TERM("Nat_Numeral_Simprocs.dest_numeral:2", [t]);

fun find_first_numeral past (t::terms) =
	((dest_numeral t, t, rev past @ terms)
	 handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

(*Thus mk_sum[t] yields t+#0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" HOLogic.natT;

(*extract the outer Sucs from a term and convert them to a binary numeral*)
fun dest_Sucs (k, Const ("Suc", _) $ t) = dest_Sucs (k+1, t)
  | dest_Sucs (0, t) = t
  | dest_Sucs (k, t) = mk_plus (mk_numeral k, t);

fun dest_sum t =
      let val (t,u) = dest_plus t 
      in  dest_sum t @ dest_sum u  end
      handle TERM _ => [t];

fun dest_Sucs_sum t = dest_sum (dest_Sucs (0,t));

val subst_tac = Int_Numeral_Simprocs.subst_tac;

val prove_conv = Int_Numeral_Simprocs.prove_conv;

val bin_simps = [add_nat_number_of, nat_number_of_add_left,
		 diff_nat_number_of, le_nat_number_of_eq_not_less, 
		 less_nat_number_of, Let_number_of, nat_number_of] @ 
                bin_arith_simps @ bin_rel_simps;

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;
fun prep_pat s = Thm.read_cterm (Theory.sign_of Arith.thy) (s, HOLogic.termT);
val prep_pats = map prep_pat;


(*** CancelNumerals simprocs ***)

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" HOLogic.natT;

fun dest_prod t =
      let val (t,u) = dest_times t 
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*) 
fun mk_coeff (k, ts) = mk_times (mk_numeral k, ts);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff t =
    let val ts = sort Term.term_ord (dest_prod t)
	val (n, _, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, one, ts)
    in (n, mk_prod ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", []) 
  | find_first_coeff past u (t::terms) =
	let val (n,u') = dest_coeff t
	in  if u aconv u' then (n, rev past @ terms)
			  else find_first_coeff (t::past) u terms
	end
	handle TERM _ => find_first_coeff (t::past) u terms;


(*Simplify #1*n and n*#1 to n*)
val add_0s = map (rename_numerals NatBin.thy) [add_0, add_0_right];
val mult_1s = map (rename_numerals NatBin.thy) [mult_1, mult_1_right];

structure CancelNumeralsCommon =
  struct
  val mk_sum    	= mk_sum
  val dest_sum		= dest_Sucs_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff
  val find_first_coeff	= find_first_coeff []
  val subst_tac          = subst_tac
  val norm_tac = ALLGOALS
                   (simp_tac (HOL_ss addsimps add_0s@mult_1s@
                                       [add_0, Suc_eq_add_numeral_1]@add_ac))
                 THEN ALLGOALS (simp_tac
				(HOL_ss addsimps bin_simps@add_ac@mult_ac))
  val numeral_simp_tac	= ALLGOALS
                (simp_tac (HOL_ss addsimps [numeral_0_eq_0 RS sym]@add_0s@bin_simps))
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = prove_conv "nateq_cancel_numerals"
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT
  val bal_add1 = nat_eq_add_iff1 RS trans
  val bal_add2 = nat_eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = prove_conv "natless_cancel_numerals"
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT
  val bal_add1 = nat_less_add_iff1 RS trans
  val bal_add2 = nat_less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = prove_conv "natle_cancel_numerals"
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT
  val bal_add1 = nat_le_add_iff1 RS trans
  val bal_add2 = nat_le_add_iff2 RS trans
);

structure DiffCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = prove_conv "natdiff_cancel_numerals"
  val mk_bal   = HOLogic.mk_binop "op -"
  val dest_bal = HOLogic.dest_bin "op -" HOLogic.natT
  val bal_add1 = nat_diff_add_eq1 RS trans
  val bal_add2 = nat_diff_add_eq2 RS trans
);


val cancel_numerals = 
  map prep_simproc
   [("nateq_cancel_numerals",
     prep_pats ["(l::nat) + m = n", "(l::nat) = m + n", 
		"(l::nat) * m = n", "(l::nat) = m * n", 
		"Suc m = n", "m = Suc n"], 
     EqCancelNumerals.proc),
    ("natless_cancel_numerals", 
     prep_pats ["(l::nat) + m < n", "(l::nat) < m + n", 
		"(l::nat) * m < n", "(l::nat) < m * n", 
		"Suc m < n", "m < Suc n"], 
     LessCancelNumerals.proc),
    ("natle_cancel_numerals", 
     prep_pats ["(l::nat) + m <= n", "(l::nat) <= m + n", 
		"(l::nat) * m <= n", "(l::nat) <= m * n", 
		"Suc m <= n", "m <= Suc n"], 
     LeCancelNumerals.proc),
    ("natdiff_cancel_numerals", 
     prep_pats ["((l::nat) + m) - n", "(l::nat) - (m + n)", 
		"(l::nat) * m - n", "(l::nat) - m * n", 
		"Suc m - n", "m - Suc n"], 
     DiffCancelNumerals.proc)];


structure CombineNumeralsData =
  struct
  val mk_sum    	= long_mk_sum    (*to work for e.g. #2*x + #3*x *)
  val dest_sum		= dest_Sucs_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff
  val left_distrib	= left_add_mult_distrib RS trans
  val prove_conv	= prove_conv "nat_combine_numerals"
  val subst_tac          = subst_tac
  val norm_tac = ALLGOALS
                   (simp_tac (HOL_ss addsimps add_0s@mult_1s@
                                       [add_0, Suc_eq_add_numeral_1]@add_ac))
                 THEN ALLGOALS (simp_tac
				(HOL_ss addsimps bin_simps@add_ac@mult_ac))
  val numeral_simp_tac	= ALLGOALS
                (simp_tac (HOL_ss addsimps [numeral_0_eq_0 RS sym]@add_0s@bin_simps))
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);
  
val combine_numerals = 
    prep_simproc ("nat_combine_numerals",
		  prep_pats ["(i::nat) + j", "Suc (i + j)"],
		  CombineNumerals.proc);

end;


Addsimprocs Nat_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Nat_Numeral_Simprocs.combine_numerals];

(*examples:
print_depth 22;
set proof_timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1)); 

(*cancel_numerals*)
test "l +( #2) + (#2) + #2 + (l + #2) + (oo  + #2) = (uu::nat)";
test "(#2*length xs < #2*length xs + j)";
test "(#2*length xs < length xs * #2 + j)";
test "#2*u = (u::nat)";
test "#2*u = Suc (u)";
test "(i + j + #12 + (k::nat)) - #15 = y";
test "(i + j + #12 + (k::nat)) - #5 = y";
test "Suc u - #2 = y";
test "Suc (Suc (Suc u)) - #2 = y";
(*Unary*)
test "(i + j + #2 + (k::nat)) - 1 = y";
test "(i + j + #1 + (k::nat)) - 2 = y";

test "(#2*x + (u*v) + y) - v*#3*u = (w::nat)";
test "(#2*x*u*v + (u*v)*#4 + y) - v*u*#4 = (w::nat)";
test "(#2*x*u*v + (u*v)*#4 + y) - v*u = (w::nat)";
test "Suc (Suc (#2*x*u*v + u*#4 + y)) - u = w";
test "Suc ((u*v)*#4) - v*#3*u = w";
test "Suc (Suc ((u*v)*#3)) - v*#3*u = w";

test "(i + j + #12 + (k::nat)) = u + #15 + y";
test "(i + j + #32 + (k::nat)) - (u + #15 + y) = zz";
test "(i + j + #12 + (k::nat)) = u + #5 + y";
(*Suc*)
test "(i + j + #12 + k) = Suc (u + y)";
test "Suc (Suc (Suc (Suc (Suc (u + y))))) <= ((i + j) + #41 + k)";
test "(i + j + #5 + k) < Suc (Suc (Suc (Suc (Suc (u + y)))))";
test "Suc (Suc (Suc (Suc (Suc (u + y))))) - #5 = v";
test "(i + j + #5 + k) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (u + y)))))))";
test "#2*y + #3*z + #2*u = Suc (u)";
test "#2*y + #3*z + #6*w + #2*y + #3*z + #2*u = Suc (u)";
test "#2*y + #3*z + #6*w + #2*y + #3*z + #2*u = #2*y' + #3*z' + #6*w' + #2*y' + #3*z' + u + (vv::nat)";
test "#6 + #2*y + #3*z + #4*u = Suc (vv + #2*u + z)";
test "(#2*n*m) < (#3*(m*n)) + (u::nat)";

(*negative numerals: FAIL*)
test "(i + j + #-23 + (k::nat)) < u + #15 + y";
test "(i + j + #3 + (k::nat)) < u + #-15 + y";
test "(i + j + #-12 + (k::nat)) - #15 = y";
test "(i + j + #12 + (k::nat)) - #-15 = y";
test "(i + j + #-12 + (k::nat)) - #-15 = y";

(*combine_numerals*)
test "k + #3*k = (u::nat)";
test "Suc (i + #3) = u";
test "Suc (i + j + #3 + k) = u";
test "k + j + #3*k + j = (u::nat)";
test "Suc (j*i + i + k + #5 + #3*k + i*j*#4) = (u::nat)";
test "(#2*n*m) + (#3*(m*n)) = (u::nat)";
(*negative numerals: FAIL*)
test "Suc (i + j + #-3 + k) = u";
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

val simprocs = [Nat_Times_Assoc.conv,
		Nat_Numeral_Simprocs.combine_numerals]@ 
		Nat_Numeral_Simprocs.cancel_numerals;

in
LA_Data_Ref.ss_ref := !LA_Data_Ref.ss_ref addsimps add_rules 
                                          addsimps basic_renamed_arith_simps
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


(** Evens and Odds, for Mutilated Chess Board **)

(*Case analysis on b<#2*)
Goal "(n::nat) < #2 ==> n = #0 | n = #1";
by (arith_tac 1);
qed "less_2_cases";

Goal "Suc(Suc(m)) mod #2 = m mod #2";
by (subgoal_tac "m mod #2 < #2" 1);
by (Asm_simp_tac 2);
be (less_2_cases RS disjE) 1;
by (ALLGOALS (asm_simp_tac (simpset() addsimps [mod_Suc])));
qed "mod2_Suc_Suc";
Addsimps [mod2_Suc_Suc];

Goal "(0 < m mod #2) = (m mod #2 = #1)";
by (subgoal_tac "m mod #2 < #2" 1);
by (Asm_simp_tac 2);
by (auto_tac (claset(), simpset() delsimps [mod_less_divisor]));
qed "mod2_gr_0";
Addsimps [mod2_gr_0, rename_numerals thy mod2_gr_0];

