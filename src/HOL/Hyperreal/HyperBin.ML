(*  Title:      HOL/Hyperreal/HyperBin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Binary arithmetic for the hypreals (integer literals only).
*)

(** hypreal_of_real (coercion from int to real) **)

Goal "hypreal_of_real (number_of w) = number_of w";
by (simp_tac (simpset() addsimps [hypreal_number_of_def]) 1);
qed "hypreal_number_of";
Addsimps [hypreal_number_of];

Goalw [hypreal_number_of_def] "(0::hypreal) = Numeral0";
by (simp_tac (simpset() addsimps [hypreal_of_real_zero RS sym]) 1);
qed "zero_eq_numeral_0";

Goalw [hypreal_number_of_def] "1hr = Numeral1";
by (simp_tac (simpset() addsimps [hypreal_of_real_one RS sym]) 1);
qed "one_eq_numeral_1";

(** Addition **)

Goal "(number_of v :: hypreal) + number_of v' = number_of (bin_add v v')";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def, 
                      hypreal_of_real_add RS sym, add_real_number_of]) 1);
qed "add_hypreal_number_of";
Addsimps [add_hypreal_number_of];


(** Subtraction **)

Goalw [hypreal_number_of_def]
     "- (number_of w :: hypreal) = number_of (bin_minus w)";
by (simp_tac
    (HOL_ss addsimps [minus_real_number_of, hypreal_of_real_minus RS sym]) 1);
qed "minus_hypreal_number_of";
Addsimps [minus_hypreal_number_of];

Goalw [hypreal_number_of_def, hypreal_diff_def]
     "(number_of v :: hypreal) - number_of w = \
\     number_of (bin_add v (bin_minus w))";
by (Simp_tac 1); 
qed "diff_hypreal_number_of";
Addsimps [diff_hypreal_number_of];


(** Multiplication **)

Goal "(number_of v :: hypreal) * number_of v' = number_of (bin_mult v v')";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def, 
	              hypreal_of_real_mult RS sym, mult_real_number_of]) 1);
qed "mult_hypreal_number_of";
Addsimps [mult_hypreal_number_of];

Goal "(2::hypreal) = Numeral1 + Numeral1";
by (Simp_tac 1);
val lemma = result();

(*For specialist use: NOT as default simprules*)
Goal "2 * z = (z+z::hypreal)";
by (simp_tac (simpset ()
	      addsimps [lemma, hypreal_add_mult_distrib,
			one_eq_numeral_1 RS sym]) 1);
qed "hypreal_mult_2";

Goal "z * 2 = (z+z::hypreal)";
by (stac hypreal_mult_commute 1 THEN rtac hypreal_mult_2 1);
qed "hypreal_mult_2_right";


(*** Comparisons ***)

(** Equals (=) **)

Goal "((number_of v :: hypreal) = number_of v') = \
\     iszero (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def, 
	              hypreal_of_real_eq_iff, eq_real_number_of]) 1);
qed "eq_hypreal_number_of";
Addsimps [eq_hypreal_number_of];

(** Less-than (<) **)

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "((number_of v :: hypreal) < number_of v') = \
\     neg (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def, hypreal_of_real_less_iff, 
		      less_real_number_of]) 1);
qed "less_hypreal_number_of";
Addsimps [less_hypreal_number_of];


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::hypreal)) = \
\     (~ number_of y < (number_of x::hypreal))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_hypreal_number_of_eq_not_less"; 
Addsimps [le_hypreal_number_of_eq_not_less];

(*** New versions of existing theorems involving 0, 1hr ***)

Goal "- Numeral1 = (-1::hypreal)";
by (Simp_tac 1);
qed "minus_numeral_one";

(*Maps 0 to Numeral0 and 1hr to Numeral1 and -1hr to -1*)
val hypreal_numeral_ss = 
    real_numeral_ss addsimps [zero_eq_numeral_0, one_eq_numeral_1, 
		              minus_numeral_one];

fun rename_numerals th = 
    asm_full_simplify hypreal_numeral_ss (Thm.transfer (the_context ()) th);


(*Now insert some identities previously stated for 0 and 1hr*)

(** HyperDef **)

Addsimps (map rename_numerals
	  [hypreal_minus_zero, hypreal_minus_zero_iff,
	   hypreal_add_zero_left, hypreal_add_zero_right, 
	   hypreal_diff_zero, hypreal_diff_zero_right,
	   hypreal_mult_0_right, hypreal_mult_0, 
           hypreal_mult_1_right, hypreal_mult_1,
	   hypreal_inverse_1, hypreal_minus_zero_less_iff]);

bind_thm ("hypreal_0_less_mult_iff", 
	  rename_numerals hypreal_zero_less_mult_iff);
bind_thm ("hypreal_0_le_mult_iff", 
	  rename_numerals hypreal_zero_le_mult_iff);
bind_thm ("hypreal_mult_less_0_iff", 
	  rename_numerals hypreal_mult_less_zero_iff);
bind_thm ("hypreal_mult_le_0_iff", 
	  rename_numerals hypreal_mult_le_zero_iff);

bind_thm ("hypreal_inverse_less_0", rename_numerals hypreal_inverse_less_zero);
bind_thm ("hypreal_inverse_gt_0", rename_numerals hypreal_inverse_gt_zero);

Addsimps [zero_eq_numeral_0,one_eq_numeral_1];


(** Simplification of arithmetic when nested to the right **)

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::hypreal)";
by Auto_tac; 
qed "hypreal_add_number_of_left";

Goal "number_of v *(number_of w * z) = (number_of(bin_mult v w) * z::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_mult_assoc RS sym]) 1);
qed "hypreal_mult_number_of_left";

Goalw [hypreal_diff_def]
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::hypreal)";
by (rtac hypreal_add_number_of_left 1);
qed "hypreal_add_number_of_diff1";

Goal "number_of v + (c - number_of w) = \
\     number_of (bin_add v (bin_minus w)) + (c::hypreal)";
by (stac (diff_hypreal_number_of RS sym) 1);
by Auto_tac;
qed "hypreal_add_number_of_diff2";

Addsimps [hypreal_add_number_of_left, hypreal_mult_number_of_left,
	  hypreal_add_number_of_diff1, hypreal_add_number_of_diff2]; 


(**** Simprocs for numeric literals ****)

(** Combining of literal coefficients in sums of products **)

Goal "(x < y) = (x-y < (Numeral0::hypreal))";
by (simp_tac (simpset() addsimps [hypreal_diff_less_eq]) 1);   
qed "hypreal_less_iff_diff_less_0";

Goal "(x = y) = (x-y = (Numeral0::hypreal))";
by (simp_tac (simpset() addsimps [hypreal_diff_eq_eq]) 1);   
qed "hypreal_eq_iff_diff_eq_0";

Goal "(x <= y) = (x-y <= (Numeral0::hypreal))";
by (simp_tac (simpset() addsimps [hypreal_diff_le_eq]) 1);   
qed "hypreal_le_iff_diff_le_0";


(** For combine_numerals **)

Goal "i*u + (j*u + k) = (i+j)*u + (k::hypreal)";
by (asm_simp_tac (simpset() addsimps [hypreal_add_mult_distrib]) 1);
qed "left_hypreal_add_mult_distrib";


(** For cancel_numerals **)

val rel_iff_rel_0_rls = 
    map (inst "y" "?u+?v")
      [hypreal_less_iff_diff_less_0, hypreal_eq_iff_diff_eq_0, 
       hypreal_le_iff_diff_le_0] @
    map (inst "y" "n")
      [hypreal_less_iff_diff_less_0, hypreal_eq_iff_diff_eq_0, 
       hypreal_le_iff_diff_le_0];

Goal "!!i::hypreal. (i*u + m = j*u + n) = ((i-j)*u + m = n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, hypreal_add_mult_distrib]@
	                 hypreal_add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_eq_add_iff1";

Goal "!!i::hypreal. (i*u + m = j*u + n) = (m = (j-i)*u + n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, hypreal_add_mult_distrib]@
                         hypreal_add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_eq_add_iff2";

Goal "!!i::hypreal. (i*u + m < j*u + n) = ((i-j)*u + m < n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, hypreal_add_mult_distrib]@
                         hypreal_add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_less_add_iff1";

Goal "!!i::hypreal. (i*u + m < j*u + n) = (m < (j-i)*u + n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, hypreal_add_mult_distrib]@
                         hypreal_add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_less_add_iff2";

Goal "!!i::hypreal. (i*u + m <= j*u + n) = ((i-j)*u + m <= n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, hypreal_add_mult_distrib]@
                         hypreal_add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_le_add_iff1";

Goal "!!i::hypreal. (i*u + m <= j*u + n) = (m <= (j-i)*u + n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, hypreal_add_mult_distrib]@
                        hypreal_add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_le_add_iff2";

Goal "(z::hypreal) * -1 = -z";
by (stac (minus_numeral_one RS sym) 1);
by (stac (hypreal_minus_mult_eq2 RS sym) 1); 
by Auto_tac;  
qed "hypreal_mult_minus_1_right";
Addsimps [hypreal_mult_minus_1_right];

Goal "-1 * (z::hypreal) = -z";
by (simp_tac (simpset() addsimps [hypreal_mult_commute]) 1); 
qed "hypreal_mult_minus_1";
Addsimps [hypreal_mult_minus_1];



structure Hyperreal_Numeral_Simprocs =
struct

(*Utilities*)


val hyprealT = Type("HyperDef.hypreal",[]);

fun mk_numeral n = HOLogic.number_of_const hyprealT $ HOLogic.mk_bin n;

val dest_numeral = Real_Numeral_Simprocs.dest_numeral;

val find_first_numeral = Real_Numeral_Simprocs.find_first_numeral;

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", hyprealT --> hyprealT);

(*Thus mk_sum[t] yields t+Numeral0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" hyprealT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
	if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" hyprealT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" hyprealT;

fun dest_prod t =
      let val (t,u) = dest_times t 
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*) 
fun mk_coeff (k, ts) = mk_times (mk_numeral k, ts);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const ("uminus", _) $ t) = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort Term.term_ord (dest_prod t)
	val (n, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, ts)
    in (sign*n, mk_prod ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", []) 
  | find_first_coeff past u (t::terms) =
	let val (n,u') = dest_coeff 1 t
	in  if u aconv u' then (n, rev past @ terms)
			  else find_first_coeff (t::past) u terms
	end
	handle TERM _ => find_first_coeff (t::past) u terms;


(*Simplify Numeral1*n and n*Numeral1 to n*)
val add_0s = map rename_numerals
                 [hypreal_add_zero_left, hypreal_add_zero_right];
val mult_plus_1s = map rename_numerals
                      [hypreal_mult_1, hypreal_mult_1_right];
val mult_minus_1s = map rename_numerals
                      [hypreal_mult_minus_1, hypreal_mult_minus_1_right];
val mult_1s = mult_plus_1s @ mult_minus_1s;

(*To perform binary arithmetic*)
val bin_simps =
    [add_hypreal_number_of, hypreal_add_number_of_left, 
     minus_hypreal_number_of, diff_hypreal_number_of, mult_hypreal_number_of, 
     hypreal_mult_number_of_left] @ bin_arith_simps @ bin_rel_simps;

(*To evaluate binary negations of coefficients*)
val hypreal_minus_simps = NCons_simps @
                   [minus_hypreal_number_of, 
		    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
		    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];

(*To let us treat subtraction as addition*)
val diff_simps = [hypreal_diff_def, hypreal_minus_add_distrib, 
                  hypreal_minus_minus];

(*push the unary minus down: - x * y = x * - y *)
val hypreal_minus_mult_eq_1_to_2 = 
    [hypreal_minus_mult_eq1 RS sym, hypreal_minus_mult_eq2] MRS trans 
    |> standard;

(*to extract again any uncancelled minuses*)
val hypreal_minus_from_mult_simps = 
    [hypreal_minus_minus, hypreal_minus_mult_eq1 RS sym, 
     hypreal_minus_mult_eq2 RS sym];

(*combine unary minus with numeric literals, however nested within a product*)
val hypreal_mult_minus_simps =
    [hypreal_mult_assoc, hypreal_minus_mult_eq1, hypreal_minus_mult_eq_1_to_2];

(*Apply the given rewrite (if present) just once*)
fun trans_tac None      = all_tac
  | trans_tac (Some th) = ALLGOALS (rtac (th RS trans));

fun prove_conv name tacs sg (hyps: thm list) (t,u) =
  if t aconv u then None
  else
  let val ct = cterm_of sg (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u)))
  in Some
     (prove_goalw_cterm [] ct (K tacs)
      handle ERROR => error 
	  ("The error(s) above occurred while trying to prove " ^
	   string_of_cterm ct ^ "\nInternal failure of simproc " ^ name))
  end;

(*version without the hyps argument*)
fun prove_conv_nohyps name tacs sg = prove_conv name tacs sg [];

(*Final simplification: cancel + and *  *)
val simplify_meta_eq = 
    Int_Numeral_Simprocs.simplify_meta_eq
         [hypreal_add_zero_left, hypreal_add_zero_right,
 	  hypreal_mult_0, hypreal_mult_0_right, hypreal_mult_1, 
          hypreal_mult_1_right];

val prep_simproc = Real_Numeral_Simprocs.prep_simproc;
val prep_pats = map Real_Numeral_Simprocs.prep_pat;

structure CancelNumeralsCommon =
  struct
  val mk_sum    	= mk_sum
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val find_first_coeff	= find_first_coeff []
  val trans_tac         = trans_tac
  val norm_tac = 
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         hypreal_minus_simps@hypreal_add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps@
                                         hypreal_add_ac@hypreal_mult_ac))
  val numeral_simp_tac	= ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = prove_conv "hyprealeq_cancel_numerals"
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hyprealT
  val bal_add1 = hypreal_eq_add_iff1 RS trans
  val bal_add2 = hypreal_eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = prove_conv "hyprealless_cancel_numerals"
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" hyprealT
  val bal_add1 = hypreal_less_add_iff1 RS trans
  val bal_add2 = hypreal_less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = prove_conv "hyprealle_cancel_numerals"
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" hyprealT
  val bal_add1 = hypreal_le_add_iff1 RS trans
  val bal_add2 = hypreal_le_add_iff2 RS trans
);

val cancel_numerals = 
  map prep_simproc
   [("hyprealeq_cancel_numerals",
     prep_pats ["(l::hypreal) + m = n", "(l::hypreal) = m + n", 
		"(l::hypreal) - m = n", "(l::hypreal) = m - n", 
		"(l::hypreal) * m = n", "(l::hypreal) = m * n"], 
     EqCancelNumerals.proc),
    ("hyprealless_cancel_numerals", 
     prep_pats ["(l::hypreal) + m < n", "(l::hypreal) < m + n", 
		"(l::hypreal) - m < n", "(l::hypreal) < m - n", 
		"(l::hypreal) * m < n", "(l::hypreal) < m * n"], 
     LessCancelNumerals.proc),
    ("hyprealle_cancel_numerals", 
     prep_pats ["(l::hypreal) + m <= n", "(l::hypreal) <= m + n", 
		"(l::hypreal) - m <= n", "(l::hypreal) <= m - n", 
		"(l::hypreal) * m <= n", "(l::hypreal) <= m * n"], 
     LeCancelNumerals.proc)];


structure CombineNumeralsData =
  struct
  val add		= op + : int*int -> int 
  val mk_sum    	= long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val left_distrib	= left_hypreal_add_mult_distrib RS trans
  val prove_conv	= prove_conv_nohyps "hypreal_combine_numerals"
  val trans_tac          = trans_tac
  val norm_tac = 
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         hypreal_minus_simps@hypreal_add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps@
                                              hypreal_add_ac@hypreal_mult_ac))
  val numeral_simp_tac	= ALLGOALS 
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);
  
val combine_numerals = 
    prep_simproc ("hypreal_combine_numerals",
		  prep_pats ["(i::hypreal) + j", "(i::hypreal) - j"],
		  CombineNumerals.proc);


(** Declarations for ExtractCommonTerm **)

(*this version ALWAYS includes a trailing one*)
fun long_mk_prod []        = one
  | long_mk_prod (t :: ts) = mk_times (t, mk_prod ts);

(*Find first term that matches u*)
fun find_first past u []         = raise TERM("find_first", []) 
  | find_first past u (t::terms) =
	if u aconv t then (rev past @ terms)
        else find_first (t::past) u terms
	handle TERM _ => find_first (t::past) u terms;

(*Final simplification: cancel + and *  *)
fun cancel_simplify_meta_eq cancel_th th = 
    Int_Numeral_Simprocs.simplify_meta_eq 
        [hypreal_mult_1, hypreal_mult_1_right] 
        (([th, cancel_th]) MRS trans);

end;

Addsimprocs Hyperreal_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Hyperreal_Numeral_Simprocs.combine_numerals];

(*The Abel_Cancel simprocs are now obsolete*)
Delsimprocs [Hyperreal_Cancel.sum_conv, Hyperreal_Cancel.rel_conv];

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1)); 

test "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = (uu::hypreal)";
test "2*u = (u::hypreal)";
test "(i + j + 12 + (k::hypreal)) - 15 = y";
test "(i + j + 12 + (k::hypreal)) - 5 = y";

test "y - b < (b::hypreal)";
test "y - (3*b + c) < (b::hypreal) - 2*c";

test "(2*x - (u*v) + y) - v*3*u = (w::hypreal)";
test "(2*x*u*v + (u*v)*4 + y) - v*u*4 = (w::hypreal)";
test "(2*x*u*v + (u*v)*4 + y) - v*u = (w::hypreal)";
test "u*v - (x*u*v + (u*v)*4 + y) = (w::hypreal)";

test "(i + j + 12 + (k::hypreal)) = u + 15 + y";
test "(i + j*2 + 12 + (k::hypreal)) = j + 5 + y";

test "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::hypreal)";

test "a + -(b+c) + b = (d::hypreal)";
test "a + -(b+c) - b = (d::hypreal)";

(*negative numerals*)
test "(i + j + -2 + (k::hypreal)) - (u + 5 + y) = zz";
test "(i + j + -3 + (k::hypreal)) < u + 5 + y";
test "(i + j + 3 + (k::hypreal)) < u + -6 + y";
test "(i + j + -12 + (k::hypreal)) - 15 = y";
test "(i + j + 12 + (k::hypreal)) - -15 = y";
test "(i + j + -12 + (k::hypreal)) - -15 = y";
*)


(** Constant folding for hypreal plus and times **)

(*We do not need
    structure Hyperreal_Plus_Assoc = Assoc_Fold (Hyperreal_Plus_Assoc_Data);
  because combine_numerals does the same thing*)

structure Hyperreal_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T	     = Hyperreal_Numeral_Simprocs.hyprealT
  val plus   = Const ("op *", [T,T] ---> T)
  val add_ac = hypreal_mult_ac
end;

structure Hyperreal_Times_Assoc = Assoc_Fold (Hyperreal_Times_Assoc_Data);

Addsimprocs [Hyperreal_Times_Assoc.conv];

Addsimps [rename_numerals hypreal_of_real_zero_iff];

(*Simplification of  x-y < 0, etc.*)
AddIffs [hypreal_less_iff_diff_less_0 RS sym];
AddIffs [hypreal_eq_iff_diff_eq_0 RS sym];
AddIffs [hypreal_le_iff_diff_le_0 RS sym];


(** number_of related to hypreal_of_real **)

Goal "(number_of w < hypreal_of_real z) = (number_of w < z)";
by (stac (hypreal_of_real_less_iff RS sym) 1); 
by (Simp_tac 1); 
qed "number_of_less_hypreal_of_real_iff";
Addsimps [number_of_less_hypreal_of_real_iff];

Goal "(number_of w <= hypreal_of_real z) = (number_of w <= z)";
by (stac (hypreal_of_real_le_iff RS sym) 1); 
by (Simp_tac 1); 
qed "number_of_le_hypreal_of_real_iff";
Addsimps [number_of_le_hypreal_of_real_iff];

Goal "(hypreal_of_real z < number_of w) = (z < number_of w)";
by (stac (hypreal_of_real_less_iff RS sym) 1); 
by (Simp_tac 1); 
qed "hypreal_of_real_less_number_of_iff";
Addsimps [hypreal_of_real_less_number_of_iff];

Goal "(hypreal_of_real z <= number_of w) = (z <= number_of w)";
by (stac (hypreal_of_real_le_iff RS sym) 1); 
by (Simp_tac 1); 
qed "hypreal_of_real_le_number_of_iff";
Addsimps [hypreal_of_real_le_number_of_iff];

(** <= monotonicity results: needed for arithmetic **)

Goal "[| i <= j;  (0::hypreal) <= k |] ==> i*k <= j*k";
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, hypreal_mult_less_mono1]));  
qed "hypreal_mult_le_mono1";

Goal "[| i <= j;  (0::hypreal) <= k |] ==> k*i <= k*j";
by (dtac hypreal_mult_le_mono1 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [hypreal_mult_commute])));
qed "hypreal_mult_le_mono2";

Goal "[| u <= v;  x <= y;  0 <= v;  (0::hypreal) <= x |] ==> u * x <= v * y";
by (etac (hypreal_mult_le_mono1 RS order_trans) 1);
by (assume_tac 1);
by (etac hypreal_mult_le_mono2 1);
by (assume_tac 1);
qed "hypreal_mult_le_mono";

