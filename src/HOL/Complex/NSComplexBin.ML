(*  Title:      NSComplexBin.ML
    Author:     Jacques D. Fleuriot
    Copyright:  2001 University of Edinburgh
    Descrition: Binary arithmetic for the nonstandard complex numbers
*)

(** hcomplex_of_complex (coercion from complex to nonstandard complex) **)

Goal "hcomplex_of_complex (number_of w) = number_of w";
by (simp_tac (simpset() addsimps [hcomplex_number_of_def]) 1);
qed "hcomplex_number_of";
Addsimps [hcomplex_number_of];

Goalw [hypreal_of_real_def]
     "hcomplex_of_hypreal (hypreal_of_real x) = \
\     hcomplex_of_complex(complex_of_real x)";
by (simp_tac (simpset() addsimps [hcomplex_of_hypreal,
    hcomplex_of_complex_def,complex_of_real_def]) 1);
qed "hcomplex_of_hypreal_eq_hcomplex_of_complex";

Goalw [complex_number_of_def,hypreal_number_of_def] 
  "hcomplex_of_complex (number_of w) = hcomplex_of_hypreal(number_of w)";
by (rtac (hcomplex_of_hypreal_eq_hcomplex_of_complex RS sym) 1);
qed "hcomplex_hypreal_number_of";

Goalw [hcomplex_number_of_def] "Numeral0 = (0::hcomplex)";
by(Simp_tac 1);
qed "hcomplex_numeral_0_eq_0";

Goalw [hcomplex_number_of_def] "Numeral1 = (1::hcomplex)";
by(Simp_tac 1);
qed "hcomplex_numeral_1_eq_1";

(*
Goal "z + hcnj z = \
\     hcomplex_of_hypreal (2 * hRe(z))";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),HOL_ss addsimps [hRe,hcnj,hcomplex_add,
    hypreal_mult,hcomplex_of_hypreal,complex_add_cnj]));
qed "hcomplex_add_hcnj";

Goal "z - hcnj z = \
\     hcomplex_of_hypreal (hypreal_of_real #2 * hIm(z)) * iii";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hIm,hcnj,hcomplex_diff,
    hypreal_of_real_def,hypreal_mult,hcomplex_of_hypreal,
    complex_diff_cnj,iii_def,hcomplex_mult]));
qed "hcomplex_diff_hcnj";
*)

(** Addition **)

Goal "(number_of v :: hcomplex) + number_of v' = number_of (bin_add v v')";
by (simp_tac
    (HOL_ss addsimps [hcomplex_number_of_def, 
                      hcomplex_of_complex_add RS sym, add_complex_number_of]) 1);
qed "add_hcomplex_number_of";
Addsimps [add_hcomplex_number_of];


(** Subtraction **)

Goalw [hcomplex_number_of_def]
     "- (number_of w :: hcomplex) = number_of (bin_minus w)";
by (simp_tac
    (HOL_ss addsimps [minus_complex_number_of, hcomplex_of_complex_minus RS sym]) 1);
qed "minus_hcomplex_number_of";
Addsimps [minus_hcomplex_number_of];

Goalw [hcomplex_number_of_def, hcomplex_diff_def]
     "(number_of v :: hcomplex) - number_of w = \
\     number_of (bin_add v (bin_minus w))";
by (Simp_tac 1); 
qed "diff_hcomplex_number_of";
Addsimps [diff_hcomplex_number_of];


(** Multiplication **)

Goal "(number_of v :: hcomplex) * number_of v' = number_of (bin_mult v v')";
by (simp_tac
    (HOL_ss addsimps [hcomplex_number_of_def, 
	              hcomplex_of_complex_mult RS sym, mult_complex_number_of]) 1);
qed "mult_hcomplex_number_of";
Addsimps [mult_hcomplex_number_of];

Goal "(2::hcomplex) = 1 + 1";
by (simp_tac (simpset() addsimps [hcomplex_numeral_1_eq_1 RS sym]) 1);
val lemma = result();

(*For specialist use: NOT as default simprules*)
Goal "2 * z = (z+z::hcomplex)";
by (simp_tac (simpset() addsimps [lemma, hcomplex_add_mult_distrib]) 1);
qed "hcomplex_mult_2";

Goal "z * 2 = (z+z::hcomplex)";
by (stac hcomplex_mult_commute 1 THEN rtac hcomplex_mult_2 1);
qed "hcomplex_mult_2_right";

(** Equals (=) **)

Goal "((number_of v :: hcomplex) = number_of v') = \
\     iszero (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (HOL_ss addsimps [hcomplex_number_of_def, 
	              hcomplex_of_complex_eq_iff, eq_complex_number_of]) 1);
qed "eq_hcomplex_number_of";
Addsimps [eq_hcomplex_number_of];

(*** New versions of existing theorems involving 0, 1hc ***)

Goal "- 1 = (-1::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_numeral_1_eq_1 RS sym]) 1);
qed "hcomplex_minus_1_eq_m1";

Goal "-1 * z = -(z::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_minus_1_eq_m1 RS sym]) 1);
qed "hcomplex_mult_minus1";

Goal "z * -1 = -(z::hcomplex)";
by (stac hcomplex_mult_commute 1 THEN rtac hcomplex_mult_minus1 1);
qed "hcomplex_mult_minus1_right";

Addsimps [hcomplex_mult_minus1,hcomplex_mult_minus1_right];

(*Maps 0 to Numeral0 and 1 to Numeral1 and -Numeral1 to -1*)
val hcomplex_numeral_ss = 
    complex_numeral_ss addsimps [hcomplex_numeral_0_eq_0 RS sym, hcomplex_numeral_1_eq_1 RS sym, 
		                 hcomplex_minus_1_eq_m1];

fun rename_numerals th = 
    asm_full_simplify hcomplex_numeral_ss (Thm.transfer (the_context ()) th);


(*Now insert some identities previously stated for 0 and 1hc*)


Addsimps [hcomplex_numeral_0_eq_0,hcomplex_numeral_1_eq_1];

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::hcomplex)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_add_assoc RS sym]));
qed "hcomplex_add_number_of_left";

Goal "number_of v *(number_of w * z) = (number_of(bin_mult v w) * z::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_mult_assoc RS sym]) 1);
qed "hcomplex_mult_number_of_left";

Goalw [hcomplex_diff_def]
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::hcomplex)";
by (rtac hcomplex_add_number_of_left 1);
qed "hcomplex_add_number_of_diff1";

Goal "number_of v + (c - number_of w) = \
\     number_of (bin_add v (bin_minus w)) + (c::hcomplex)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff_def]@ add_ac));
qed "hcomplex_add_number_of_diff2";

Addsimps [hcomplex_add_number_of_left, hcomplex_mult_number_of_left,
	  hcomplex_add_number_of_diff1, hcomplex_add_number_of_diff2]; 


(**** Simprocs for numeric literals ****)

(** Combining of literal coefficients in sums of products **)

Goal "(x = y) = (x-y = (0::hcomplex))";
by (simp_tac (simpset() addsimps [hcomplex_diff_eq_eq]) 1);   
qed "hcomplex_eq_iff_diff_eq_0";

(** For combine_numerals **)

Goal "i*u + (j*u + k) = (i+j)*u + (k::hcomplex)";
by (asm_simp_tac (simpset() addsimps [hcomplex_add_mult_distrib]
    @ add_ac) 1);
qed "left_hcomplex_add_mult_distrib";

(** For cancel_numerals **)

Goal "((x::hcomplex) = u + v) = (x - (u + v) = 0)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff_eq_eq]));
qed "hcomplex_eq_add_diff_eq_0";

Goal "((x::hcomplex) = n) = (x - n = 0)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff_eq_eq]));
qed "hcomplex_eq_diff_eq_0";

val hcomplex_rel_iff_rel_0_rls = [hcomplex_eq_diff_eq_0,hcomplex_eq_add_diff_eq_0];

Goal "!!i::hcomplex. (i*u + m = j*u + n) = ((i-j)*u + m = n)";
by (auto_tac (claset(), simpset() addsimps [hcomplex_add_mult_distrib,
    hcomplex_diff_def] @ add_ac));
by (asm_simp_tac (simpset() addsimps [hcomplex_add_assoc RS sym]) 1);
by (simp_tac (simpset() addsimps [hcomplex_add_assoc]) 1);
qed "hcomplex_eq_add_iff1";

Goal "!!i::hcomplex. (i*u + m = j*u + n) = (m = (j-i)*u + n)";
by (res_inst_tac [("z","i")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","j")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","u")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","m")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","n")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [hcomplex_diff,hcomplex_add,
    hcomplex_mult,complex_eq_add_iff2]));
qed "hcomplex_eq_add_iff2";


structure HComplex_Numeral_Simprocs =
struct

(*Utilities*)

val hcomplexT = Type("NSComplex.hcomplex",[]);

fun mk_numeral n = HOLogic.number_of_const hcomplexT $ HOLogic.mk_bin n;

val dest_numeral = Complex_Numeral_Simprocs.dest_numeral;

val find_first_numeral = Complex_Numeral_Simprocs.find_first_numeral;

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", hcomplexT --> hcomplexT);

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" hcomplexT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
	if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" hcomplexT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" hcomplexT;

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



(*Simplify Numeral0+n, n+Numeral0, Numeral1*n, n*Numeral1*)
val add_0s = map rename_numerals [hcomplex_add_zero_left, hcomplex_add_zero_right];
val mult_plus_1s = map rename_numerals [hcomplex_mult_one_left, hcomplex_mult_one_right];
val mult_minus_1s = map rename_numerals [hcomplex_mult_minus1, hcomplex_mult_minus1_right];
val mult_1s = mult_plus_1s @ mult_minus_1s;

(*To perform binary arithmetic*)
val bin_simps =
    [hcomplex_numeral_0_eq_0 RS sym, hcomplex_numeral_1_eq_1 RS sym,
     add_hcomplex_number_of, hcomplex_add_number_of_left, 
     minus_hcomplex_number_of, diff_hcomplex_number_of, mult_hcomplex_number_of, 
     hcomplex_mult_number_of_left] @ bin_arith_simps @ bin_rel_simps;

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [hcomplex_add_number_of_left, add_hcomplex_number_of];

(*To evaluate binary negations of coefficients*)
val hcomplex_minus_simps = NCons_simps @
                   [hcomplex_minus_1_eq_m1,minus_hcomplex_number_of, 
		    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
		    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];


(*To let us treat subtraction as addition*)
val diff_simps = [hcomplex_diff_def, minus_add_distrib, minus_minus];

(*push the unary minus down: - x * y = x * - y *)
val hcomplex_minus_mult_eq_1_to_2 = 
    [minus_mult_left RS sym, minus_mult_right] MRS trans 
    |> standard;

(*to extract again any uncancelled minuses*)
val hcomplex_minus_from_mult_simps = 
    [minus_minus, minus_mult_left RS sym, minus_mult_right RS sym];

(*combine unary minus with numeric literals, however nested within a product*)
val hcomplex_mult_minus_simps =
    [hcomplex_mult_assoc, minus_mult_left, hcomplex_minus_mult_eq_1_to_2];

(*Final simplification: cancel + and *  *)
val simplify_meta_eq = 
    Int_Numeral_Simprocs.simplify_meta_eq
         [add_zero_left, add_zero_right,
 	  mult_zero_left, mult_zero_right, mult_1, mult_1_right];

val prep_simproc = Complex_Numeral_Simprocs.prep_simproc;


structure CancelNumeralsCommon =
  struct
  val mk_sum    	= mk_sum
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val find_first_coeff	= find_first_coeff []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = 
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         hcomplex_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@hcomplex_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps hcomplex_minus_from_mult_simps@
                                         add_ac@mult_ac))
  val numeral_simp_tac	= ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hcomplexT
  val bal_add1 = hcomplex_eq_add_iff1 RS trans
  val bal_add2 = hcomplex_eq_add_iff2 RS trans
);


val cancel_numerals = 
  map prep_simproc
   [("hcomplexeq_cancel_numerals",
      ["(l::hcomplex) + m = n", "(l::hcomplex) = m + n", 
		"(l::hcomplex) - m = n", "(l::hcomplex) = m - n", 
		"(l::hcomplex) * m = n", "(l::hcomplex) = m * n"], 
     EqCancelNumerals.proc)];

structure CombineNumeralsData =
  struct
  val add		= op + : int*int -> int 
  val mk_sum    	= long_mk_sum    (*to work for e.g. #2*x + #3*x *)
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val left_distrib	= left_hcomplex_add_mult_distrib RS trans
  val prove_conv	= Bin_Simprocs.prove_conv_nohyps
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = 
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         hcomplex_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@hcomplex_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps hcomplex_minus_from_mult_simps@
                                              add_ac@mult_ac))
  val numeral_simp_tac	= ALLGOALS 
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals = 
    prep_simproc ("hcomplex_combine_numerals",
		  ["(i::hcomplex) + j", "(i::hcomplex) - j"],
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
        [hcomplex_mult_one_left, hcomplex_mult_one_right] 
        (([th, cancel_th]) MRS trans);

(*** Making constant folding work for 0 and 1 too ***)

structure HComplexAbstractNumeralsData =
  struct
  val dest_eq         = HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral      = Bin_Simprocs.is_numeral
  val numeral_0_eq_0  = hcomplex_numeral_0_eq_0
  val numeral_1_eq_1  = hcomplex_numeral_1_eq_1
  val prove_conv      = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps  = ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq = Bin_Simprocs.simplify_meta_eq
  end

structure HComplexAbstractNumerals = AbstractNumeralsFun (HComplexAbstractNumeralsData)

(*For addition, we already have rules for the operand 0.
  Multiplication is omitted because there are already special rules for
  both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
  For the others, having three patterns is a compromise between just having
  one (many spurious calls) and having nine (just too many!) *)
val eval_numerals =
  map prep_simproc
   [("hcomplex_add_eval_numerals",
     ["(m::hcomplex) + 1", "(m::hcomplex) + number_of v"],
     HComplexAbstractNumerals.proc add_hcomplex_number_of),
    ("hcomplex_diff_eval_numerals",
     ["(m::hcomplex) - 1", "(m::hcomplex) - number_of v"],
     HComplexAbstractNumerals.proc diff_hcomplex_number_of),
    ("hcomplex_eq_eval_numerals",
     ["(m::hcomplex) = 0", "(m::hcomplex) = 1", "(m::hcomplex) = number_of v"],
     HComplexAbstractNumerals.proc eq_hcomplex_number_of)]

end;

Addsimprocs HComplex_Numeral_Simprocs.eval_numerals;
Addsimprocs HComplex_Numeral_Simprocs.cancel_numerals;
Addsimprocs [HComplex_Numeral_Simprocs.combine_numerals];


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1)); 

test "l +  2 +  2 +  2 + (l +  2) + (oo +  2) = (uu::hcomplex)";
test " 2*u = (u::hcomplex)";
test "(i + j + 12 + (k::hcomplex)) - 15 = y";
test "(i + j + 12 + (k::hcomplex)) -  5 = y";

test "( 2*x - (u*v) + y) - v* 3*u = (w::hcomplex)";
test "( 2*x*u*v + (u*v)* 4 + y) - v*u* 4 = (w::hcomplex)";
test "( 2*x*u*v + (u*v)* 4 + y) - v*u = (w::hcomplex)";
test "u*v - (x*u*v + (u*v)* 4 + y) = (w::hcomplex)";

test "(i + j + 12 + (k::hcomplex)) = u + 15 + y";
test "(i + j* 2 + 12 + (k::hcomplex)) = j +  5 + y";

test " 2*y +  3*z +  6*w +  2*y +  3*z +  2*u =  2*y' +  3*z' +  6*w' +  2*y' +  3*z' + u + (vv::hcomplex)";

test "a + -(b+c) + b = (d::hcomplex)";
test "a + -(b+c) - b = (d::hcomplex)";

(*negative numerals*)
test "(i + j +  -2 + (k::hcomplex)) - (u +  5 + y) = zz";

test "(i + j +  -12 + (k::hcomplex)) - 15 = y";
test "(i + j + 12 + (k::hcomplex)) -  -15 = y";
test "(i + j +  -12 + (k::hcomplex)) - -15 = y";
*)

(** Constant folding for hcomplex plus and times **)

structure HComplex_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T	     = HComplex_Numeral_Simprocs.hcomplexT
  val plus   = Const ("op *", [T,T] ---> T)
  val add_ac = mult_ac
end;

structure HComplex_Times_Assoc = Assoc_Fold (HComplex_Times_Assoc_Data);

Addsimprocs [HComplex_Times_Assoc.conv];

Addsimps [hcomplex_of_complex_zero_iff];

(*Simplification of  x-y = 0 *)

AddIffs [hcomplex_eq_iff_diff_eq_0 RS sym];

(** extra thms **)

Goal "(hcnj z = 0) = (z = 0)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_hcnj_zero_iff]));
qed "hcomplex_hcnj_num_zero_iff";
Addsimps [hcomplex_hcnj_num_zero_iff];

Goal "0 = Abs_hcomplex (hcomplexrel `` {%n. 0})";
by (simp_tac (simpset() addsimps [hcomplex_zero_def RS meta_eq_to_obj_eq RS sym]) 1);
qed "hcomplex_zero_num";

Goal "1 =  Abs_hcomplex (hcomplexrel `` {%n. 1})";
by (simp_tac (simpset() addsimps [hcomplex_one_def RS meta_eq_to_obj_eq RS sym]) 1);
qed "hcomplex_one_num";

(*** Real and imaginary stuff ***)

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya = \
\       number_of xb + iii * number_of yb) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff,
     hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iff";
Addsimps [hcomplex_number_of_eq_cancel_iff];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii = \
\       number_of xb + number_of yb * iii) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iffA,
    hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iffA";
Addsimps [hcomplex_number_of_eq_cancel_iffA];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii = \
\       number_of xb + iii * number_of yb) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iffB,
    hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iffB";
Addsimps [hcomplex_number_of_eq_cancel_iffB];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya = \
\       number_of xb + number_of yb * iii) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iffC,
     hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iffC";
Addsimps [hcomplex_number_of_eq_cancel_iffC];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya = \
\       number_of xb) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = 0))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff2,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff2";
Addsimps [hcomplex_number_of_eq_cancel_iff2];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii = \
\       number_of xb) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = 0))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff2a,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff2a";
Addsimps [hcomplex_number_of_eq_cancel_iff2a];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya = \
\    iii * number_of yb) = \
\  (((number_of xa :: hcomplex) = 0) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff3,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff3";
Addsimps [hcomplex_number_of_eq_cancel_iff3];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii= \
\    iii * number_of yb) = \
\  (((number_of xa :: hcomplex) = 0) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff3a,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff3a";
Addsimps [hcomplex_number_of_eq_cancel_iff3a];

Goalw [hcomplex_number_of_def] "hcnj (number_of v :: hcomplex) = number_of v";
by (rtac (hcomplex_hypreal_number_of RS ssubst) 1);
by (rtac hcomplex_hcnj_hcomplex_of_hypreal 1);
qed "hcomplex_number_of_hcnj";
Addsimps [hcomplex_number_of_hcnj];

Goalw [hcomplex_number_of_def] 
      "hcmod(number_of v :: hcomplex) = abs (number_of v :: hypreal)";
by (rtac (hcomplex_hypreal_number_of RS ssubst) 1);
by (auto_tac (claset(), HOL_ss addsimps [hcmod_hcomplex_of_hypreal]));
qed "hcomplex_number_of_hcmod";
Addsimps [hcomplex_number_of_hcmod];

Goalw [hcomplex_number_of_def] 
      "hRe(number_of v :: hcomplex) = number_of v";
by (rtac (hcomplex_hypreal_number_of RS ssubst) 1);
by (auto_tac (claset(), HOL_ss addsimps [hRe_hcomplex_of_hypreal]));
qed "hcomplex_number_of_hRe";
Addsimps [hcomplex_number_of_hRe];

Goalw [hcomplex_number_of_def] 
      "hIm(number_of v :: hcomplex) = 0";
by (rtac (hcomplex_hypreal_number_of RS ssubst) 1);
by (auto_tac (claset(), HOL_ss addsimps [hIm_hcomplex_of_hypreal]));
qed "hcomplex_number_of_hIm";
Addsimps [hcomplex_number_of_hIm];



