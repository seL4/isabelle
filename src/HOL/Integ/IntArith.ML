(*  Title:      HOL/Integ/IntArith.thy
    ID:         $Id$
    Authors:    Larry Paulson and Tobias Nipkow

Simprocs and decision procedure for linear arithmetic.
*)

(*** Simprocs for numeric literals ***)

(** Combining of literal coefficients in sums of products **)

Goal "(x < y) = (x-y < (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zless_iff_zdiff_zless_0";

Goal "(x = y) = (x-y = (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "eq_iff_zdiff_eq_0";

Goal "(x <= y) = (x-y <= (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zle_iff_zdiff_zle_0";


(** For cancel_numerals **)

Goal "!!i::int. ((i*u + m) - (j*u + n)) = (((i-j)*u + m) - n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]) 1);
qed "diff_add_eq1";

Goal "!!i::int. ((i*u + m) - (j*u + n)) = (m - ((j-i)*u + n))";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]) 1);
qed "diff_add_eq2";

val rel_iff_rel_0_rls = map (inst "y" "?u+?v")
                          [zless_iff_zdiff_zless_0, eq_iff_zdiff_eq_0, 
			   zle_iff_zdiff_zle_0] @
		        map (inst "y" "n")
                          [zless_iff_zdiff_zless_0, eq_iff_zdiff_eq_0, 
			   zle_iff_zdiff_zle_0];

Goal "!!i::int. (i*u + m = j*u + n) = ((i-j)*u + m = n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]@
		                     zadd_ac@rel_iff_rel_0_rls) 1);
qed "eq_add_iff1";

Goal "!!i::int. (i*u + m = j*u + n) = (m = (j-i)*u + n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]@
                                     zadd_ac@rel_iff_rel_0_rls) 1);
qed "eq_add_iff2";

Goal "!!i::int. (i*u + m < j*u + n) = ((i-j)*u + m < n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]@
                                     zadd_ac@rel_iff_rel_0_rls) 1);
qed "less_add_iff1";

Goal "!!i::int. (i*u + m < j*u + n) = (m < (j-i)*u + n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]@
                                     zadd_ac@rel_iff_rel_0_rls) 1);
qed "less_add_iff2";

Goal "!!i::int. (i*u + m <= j*u + n) = ((i-j)*u + m <= n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]@
                                     zadd_ac@rel_iff_rel_0_rls) 1);
qed "le_add_iff1";

Goal "!!i::int. (i*u + m <= j*u + n) = (m <= (j-i)*u + n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]
                                     @zadd_ac@rel_iff_rel_0_rls) 1);
qed "le_add_iff2";


structure Int_Numeral_Simprocs =
struct

(*Utilities*)

fun mk_numeral n = HOLogic.number_of_const HOLogic.intT $ 
                   NumeralSyntax.mk_bin n;

(*Decodes a binary INTEGER*)
fun dest_numeral (Const("Numeral.number_of", _) $ w) = NumeralSyntax.dest_bin w
  | dest_numeral t = raise TERM("dest_numeral", [t]);

fun find_first_numeral past (t::terms) =
	((dest_numeral t, rev past @ terms)
	 handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", HOLogic.intT --> HOLogic.intT);

(*Thus mk_sum[t] yields t+#0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" HOLogic.intT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
	if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" HOLogic.intT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" HOLogic.intT;

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


(*Simplify #1*n and n*#1 to n*)
val add_0s = [zadd_0, zadd_0_right];
val mult_1s = [zmult_1, zmult_1_right, zmult_minus1, zmult_minus1_right];

(*To perform binary arithmetic*)
val bin_simps = [number_of_add RS sym, add_number_of_left] @ 
                bin_arith_simps @ bin_rel_simps;

(*To let us treat subtraction as addition*)
val diff_simps = [zdiff_def, zminus_zadd_distrib, zminus_zminus];

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

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;
fun prep_pat s = Thm.read_cterm (Theory.sign_of Int.thy) (s, HOLogic.termT);
val prep_pats = map prep_pat;

structure CancelNumeralsCommon =
  struct
  val mk_sum    	= mk_sum
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val find_first_coeff	= find_first_coeff []
  val prove_conv	= prove_conv
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@zadd_ac))
                 THEN ALLGOALS
                    (simp_tac (HOL_ss addsimps [zmult_zminus_right RS sym]@bin_simps@zmult_ac))
  val numeral_simp_tac	= ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  end;


(* int eq *)
structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.intT
  val bal_add1	= eq_add_iff1 RS trans
  val bal_add2	= eq_add_iff2 RS trans
);

(* int less *)
structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.intT
  val bal_add1	= less_add_iff1 RS trans
  val bal_add2	= less_add_iff2 RS trans
);

(* int le *)
structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.intT
  val bal_add1	= le_add_iff1 RS trans
  val bal_add2	= le_add_iff2 RS trans
);

(* int diff *)
structure DiffCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binop "op -"
  val dest_bal = HOLogic.dest_bin "op -" HOLogic.intT
  val bal_add1	= diff_add_eq1 RS trans
  val bal_add2	= diff_add_eq2 RS trans
);


val cancel_numerals = 
  map prep_simproc
   [("inteq_cancel_numerals",
     prep_pats ["(l::int) + m = n", "(l::int) = m + n", 
		"(l::int) - m = n", "(l::int) = m - n", 
		"(l::int) * m = n", "(l::int) = m * n"], 
     EqCancelNumerals.proc),
    ("intless_cancel_numerals", 
     prep_pats ["(l::int) + m < n", "(l::int) < m + n", 
		"(l::int) - m < n", "(l::int) < m - n", 
		"(l::int) * m < n", "(l::int) < m * n"], 
     LessCancelNumerals.proc),
    ("intle_cancel_numerals", 
     prep_pats ["(l::int) + m <= n", "(l::int) <= m + n", 
		"(l::int) - m <= n", "(l::int) <= m - n", 
		"(l::int) * m <= n", "(l::int) <= m * n"], 
     LeCancelNumerals.proc),
    ("intdiff_cancel_numerals", 
     prep_pats ["((l::int) + m) - n", "(l::int) - (m + n)", 
		"((l::int) - m) - n", "(l::int) - (m - n)", 
		"(l::int) * m - n", "(l::int) - m * n"], 
     DiffCancelNumerals.proc)];

end;


Addsimprocs Int_Numeral_Simprocs.cancel_numerals;

(*examples:
print_depth 22;
set proof_timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1)); 

test "#2*u = (u::int)";
test "(i + j + #12 + (k::int)) - #15 = y";
test "(i + j + #12 + (k::int)) - #5 = y";

test "y - b < (b::int)";
test "y - (#3*b + c) < (b::int) - #2*c";

test "(#2*x + (u*v) + y) - v*#3*u = (w::int)";
test "(#2*x*u*v + (u*v)*#4 + y) - v*u*#4 = (w::int)";
test "(#2*x*u*v + (u*v)*#4 + y) - v*u = (w::int)";

test "(i + j + #12 + (k::int)) = u + #15 + y";
test "(i + j*#2 + #12 + (k::int)) = j + #5 + y";

test "#2*y + #3*z + #6*w + #2*y + #3*z + #2*u = #2*y' + #3*z' + #6*w' + #2*y' + #3*z' + u + (vv::int)";

(*negative numerals*)
test "(i + j + #-2 + (k::int)) - (u + #5 + y) = zz";
test "(i + j + #-3 + (k::int)) < u + #5 + y";
test "(i + j + #3 + (k::int)) < u + #-6 + y";
test "(i + j + #-12 + (k::int)) - #15 = y";
test "(i + j + #12 + (k::int)) - #-15 = y";
test "(i + j + #-12 + (k::int)) - #-15 = y";
*)



(****************************************************************************************************************************************************************************************************************************************************************


structure Int_CC_Data : COMBINE_COEFF_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy		= Bin.thy
  val T			= HOLogic.intT

  val trans		= trans
  val add_ac		= zadd_ac
  val diff_def		= zdiff_def
  val minus_add_distrib	= zminus_zadd_distrib
  val minus_minus	= zminus_zminus
  val mult_commute	= zmult_commute
  val mult_1_right	= zmult_1_right
  val add_mult_distrib = zadd_zmult_distrib2
  val diff_mult_distrib = zdiff_zmult_distrib2
  val mult_minus_right = zmult_zminus_right

  val rel_iff_rel_0_rls = [zless_iff_zdiff_zless_0, eq_iff_zdiff_eq_0, 
			   zle_iff_zdiff_zle_0]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

end;

structure Int_CC = Combine_Coeff (Int_CC_Data);

Addsimprocs [Int_CC.sum_conv, Int_CC.rel_conv];
****************************************************************)


(** Constant folding for integer plus and times **)

(*We do not need
    structure Int_Plus_Assoc = Assoc_Fold (Int_Plus_Assoc_Data);
  because cancel_coeffs does the same thing*)

structure Int_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.intT
  val plus   = Const ("op *", [HOLogic.intT,HOLogic.intT] ---> HOLogic.intT);
  val add_ac = zmult_ac
end;

structure Int_Times_Assoc = Assoc_Fold (Int_Times_Assoc_Data);

Addsimprocs [Int_Times_Assoc.conv];


(** The same for the naturals **)

structure Nat_Plus_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.natT
  val plus   = Const ("op +", [HOLogic.natT,HOLogic.natT] ---> HOLogic.natT);
  val add_ac = add_ac
end;

structure Nat_Plus_Assoc = Assoc_Fold (Nat_Plus_Assoc_Data);

structure Nat_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.natT
  val plus   = Const ("op *", [HOLogic.natT,HOLogic.natT] ---> HOLogic.natT);
  val add_ac = mult_ac
end;

structure Nat_Times_Assoc = Assoc_Fold (Nat_Times_Assoc_Data);

Addsimprocs [Nat_Plus_Assoc.conv, Nat_Times_Assoc.conv];



(*** decision procedure for linear arithmetic ***)

(*---------------------------------------------------------------------------*)
(* Linear arithmetic                                                         *)
(*---------------------------------------------------------------------------*)

(*
Instantiation of the generic linear arithmetic package for int.
*)

(* Update parameters of arithmetic prover *)
let

(* reduce contradictory <= to False *)
val add_rules = simp_thms @ bin_arith_simps @ bin_rel_simps @
                [int_0,zmult_0,zmult_0_right];

val simprocs = Int_Numeral_Simprocs.cancel_numerals@
               [Int_Cancel.sum_conv, Int_Cancel.rel_conv  (*****,
                Int_CC.sum_conv, Int_CC.rel_conv***)];

val add_mono_thms =
  map (fn s => prove_goal Int.thy s
                 (fn prems => [cut_facts_tac prems 1,
                      asm_simp_tac (simpset() addsimps [zadd_zle_mono]) 1]))
    ["(i <= j) & (k <= l) ==> i + k <= j + (l::int)",
     "(i  = j) & (k <= l) ==> i + k <= j + (l::int)",
     "(i <= j) & (k  = l) ==> i + k <= j + (l::int)",
     "(i  = j) & (k  = l) ==> i + k  = j + (l::int)"
    ];

in
LA_Data_Ref.add_mono_thms := !LA_Data_Ref.add_mono_thms @ add_mono_thms;
LA_Data_Ref.lessD := !LA_Data_Ref.lessD @ [add1_zle_eq RS iffD2];
LA_Data_Ref.ss_ref := !LA_Data_Ref.ss_ref addsimps add_rules
                      addsimprocs simprocs;
LA_Data_Ref.discrete := !LA_Data_Ref.discrete @ [("IntDef.int",true)]
end;

let
val int_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of Int.thy) (s, HOLogic.boolT))
      ["(m::int) < n","(m::int) <= n", "(m::int) = n"];

val fast_int_arith_simproc = mk_simproc
  "fast_int_arith" int_arith_simproc_pats Fast_Arith.lin_arith_prover;
in
Addsimprocs [fast_int_arith_simproc]
end;

(* Some test data
Goal "!!a::int. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a-d+ #2 <= b+(-c)";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a+c+ #1 < b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b <= i+j; a<=b; i<=j |] \
\     ==> a+a <= j+j";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b < i+j; a<b; i<j |] \
\     ==> a+a - - #-1 < j+j - #3";
by (fast_arith_tac 1);
Goal "!!a::int. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> #6*a <= #5*l+i";
by (fast_arith_tac 1);
*)

(*---------------------------------------------------------------------------*)
(* End of linear arithmetic                                                  *)
(*---------------------------------------------------------------------------*)

(** Simplification of inequalities involving numerical constants **)

Goal "(w <= z + (#1::int)) = (w<=z | w = z + (#1::int))";
by (arith_tac 1);
qed "zle_add1_eq";

Goal "(w <= z - (#1::int)) = (w<(z::int))";
by (arith_tac 1);
qed "zle_diff1_eq";
Addsimps [zle_diff1_eq];

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w <= z; #0 <= v |] ==> w <= z + (v::int)";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd";

Goal "w <= z ==> w <= z + (#1::int)";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd1";

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w < z; #0 <= v |] ==> w < z + (v::int)";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd";

Goal "w < z ==> w < z + (#1::int)";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd1";

Goal "(w < z + #1) = (w<=(z::int))";
by (arith_tac 1);
qed "zle_add1_eq_le";
Addsimps [zle_add1_eq_le];

Goal "(z = z + w) = (w = (#0::int))";
by (arith_tac 1);
qed "zadd_left_cancel0";
Addsimps [zadd_left_cancel0];

(*LOOPS as a simprule!*)
Goal "[| w + v < z; #0 <= v |] ==> w < (z::int)";
by (fast_arith_tac 1);
qed "zless_zadd_imp_zless";

(*LOOPS as a simprule!  Analogous to Suc_lessD*)
Goal "w + #1 < z ==> w < (z::int)";
by (fast_arith_tac 1);
qed "zless_zadd1_imp_zless";

Goal "w + #-1 = w - (#1::int)";
by (Simp_tac 1);
qed "zplus_minus1_conv";


(* nat *)

Goal "#0 <= z ==> int (nat z) = z"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, not_neg_nat]) 1); 
qed "nat_0_le"; 

Goal "z <= #0 ==> nat z = 0"; 
by (case_tac "z = #0" 1);
by (asm_simp_tac (simpset() addsimps [nat_le_int0]) 1); 
by (asm_full_simp_tac 
    (simpset() addsimps [neg_eq_less_0, neg_nat, linorder_neq_iff]) 1);
qed "nat_le_0"; 

Addsimps [nat_0_le, nat_le_0];

val [major,minor] = Goal "[| #0 <= z;  !!m. z = int m ==> P |] ==> P"; 
by (rtac (major RS nat_0_le RS sym RS minor) 1);
qed "nonneg_eq_int"; 

Goal "#0 <= w ==> (nat w = m) = (w = int m)";
by Auto_tac;
qed "nat_eq_iff";

Goal "#0 <= w ==> (nat w < m) = (w < int m)";
by (rtac iffI 1);
by (asm_full_simp_tac 
    (simpset() delsimps [zless_int] addsimps [zless_int RS sym]) 2);
by (etac (nat_0_le RS subst) 1);
by (Simp_tac 1);
qed "nat_less_iff";


(*Users don't want to see (int 0), int(Suc 0) or w + - z*)
Addsimps [int_0, int_Suc, symmetric zdiff_def];

Goal "nat #0 = 0";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_0";

Goal "nat #1 = 1";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_1";

Goal "nat #2 = 2";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_2";

Goal "#0 <= w ==> (nat w < nat z) = (w<z)";
by (case_tac "neg z" 1);
by (auto_tac (claset(), simpset() addsimps [nat_less_iff]));
by (auto_tac (claset() addIs [zless_trans], 
	      simpset() addsimps [neg_eq_less_0, zle_def]));
qed "nat_less_eq_zless";

Goal "#0 < w | #0 <= z ==> (nat w <= nat z) = (w<=z)";
by (auto_tac (claset(), 
	      simpset() addsimps [linorder_not_less RS sym, 
				  zless_nat_conj]));
qed "nat_le_eq_zle";

(*Analogous to zadd_int, but more easily provable using the arithmetic in Bin*)
Goal "n<=m --> int m - int n = int (m-n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by Auto_tac;
qed_spec_mp "zdiff_int";


(** Products of signs **)

Goal "(m::int) < #0 ==> (#0 < m*n) = (n < #0)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1_neg], simpset()) 2);
by (eres_inst_tac [("P", "#0 < m * n")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [inst "k" "m" zmult_zless_mono1_neg], 
	       simpset()addsimps [order_le_less, zmult_commute]) 1);
qed "neg_imp_zmult_pos_iff";

Goal "(m::int) < #0 ==> (m*n < #0) = (#0 < n)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1], simpset()) 2);
by (eres_inst_tac [("P", "m * n < #0")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [zmult_zless_mono1_neg], 
	       simpset() addsimps [order_le_less]) 1);
qed "neg_imp_zmult_neg_iff";

Goal "#0 < (m::int) ==> (m*n < #0) = (n < #0)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1_neg], simpset()) 2);
by (eres_inst_tac [("P", "m * n < #0")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [zmult_zless_mono1], 
	       simpset() addsimps [order_le_less]) 1);
qed "pos_imp_zmult_neg_iff";

Goal "#0 < (m::int) ==> (#0 < m*n) = (#0 < n)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1], simpset()) 2);
by (eres_inst_tac [("P", "#0 < m * n")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [inst "k" "m" zmult_zless_mono1], 
	       simpset() addsimps [order_le_less, zmult_commute]) 1);
qed "pos_imp_zmult_pos_iff";

(** <= versions of the theorems above **)

Goal "(m::int) < #0 ==> (m*n <= #0) = (#0 <= n)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      neg_imp_zmult_pos_iff]) 1);
qed "neg_imp_zmult_nonpos_iff";

Goal "(m::int) < #0 ==> (#0 <= m*n) = (n <= #0)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      neg_imp_zmult_neg_iff]) 1);
qed "neg_imp_zmult_nonneg_iff";

Goal "#0 < (m::int) ==> (m*n <= #0) = (n <= #0)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      pos_imp_zmult_pos_iff]) 1);
qed "pos_imp_zmult_nonpos_iff";

Goal "#0 < (m::int) ==> (#0 <= m*n) = (#0 <= n)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      pos_imp_zmult_neg_iff]) 1);
qed "pos_imp_zmult_nonneg_iff";
